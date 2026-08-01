`timescale 1ns / 1ps
`default_nettype none

// Silicon anchor for the AUTO-EMITTED RANGE-BEARING RADAR EKF -- the transcendental frontier.
//
// The canonical Extended Kalman Filter: a target tracked through h(x) = (range, bearing) =
// (sqrt(x0^2+x1^2), atan(x1/x0)). rtl/rb_track_emitted.v is generated verbatim by Forge from
// forge/examples/ekf_range_bearing.eml, whose entire content is that measurement model --
//
//     @target(fpga, form = "ekf2d_filter", transcendentals = "wide")
//     fn track(x0: Real, x1: Real) -> (Real, Real) { (sqrt(x0*x0 + x1*x1), atan(x1/x0)) }
//
// -- from which the compiler DERIVES the Jacobian by symbolic differentiation through sqrt, a
// fractional power, a division and atan:
//
//     H = [[ x0/r, x1/r ], [ -x1/r^2, x0/r^2 ]]        r = sqrt(x0^2 + x1^2)
//
// and emits the whole recursive filter around it. Nobody wrote the Jacobian, the linearization,
// the measurement update or the covariance update.
//
// WHAT THIS ADDS OVER ekf_emitted_arty (which already proved "the compiler wrote it" on silicon):
// that anchor's model was POLYNOMIAL -- three multiplies and four shifts, no kernels. This one is
// TRANSCENDENTAL: eml_sqrt_wide, eml_atan_wide and eml_reciprocal on the die, a chain-rule
// Jacobian, and a 50-cycle model whose latency the filter must stall for (MODEL_LATENCY).
//
// THE GEOMETRY EXERCISES THE RANGE FOLD. Truth (2,5) from prior (3,4), so |x1/x0| runs 2.23 -> 2.47
// -- ABOVE 1 for the whole track. eml_atan's 4-term Taylor DIVERGES there (atan(2) -> -12.55, wrong
// sign); eml_atan_wide's fold atan(x) = sign(x)*pi/2 - atan(1/x) is what makes this track possible,
// and this anchor is the first time that path meets fabric. It deliberately avoids |x1/x0| ~ 1,
// where the series is at its worst (3.5 deg) -- that band edge is characterised by EXHAUSTIVE
// enumeration over all 131,073 Q16.16 values in forge's certificate, which is stronger evidence
// than one silicon point.
//
// Measurement noise is asymmetric (range var 0.02, bearing var 0.002) because the two components of
// h have DIFFERENT UNITS -- new here, and a modelling fact the polynomial anchors never faced.
//
// Capture protocol, UART schema (arty-ekf-filter.v0) and telemetry are identical to the siblings.
// Each epoch LOADS the prior (x0,P0) then streams N measurements, holding each trajectory point
// quasi-static for a UART frame, then replays. BTN0 -> reset; LED -> step.
//
module rb_ekf_anchor_top #(
    parameter integer ADVANCE_PERIOD = 20_000_000,   // 0.2 s @ 100 MHz (sim overrides small)
    parameter integer FRAME_PERIOD   = 10_000_000
) (
    input  wire        clk_100mhz,
    input  wire        btn0,
    output reg  [3:0]  led,
    output wire        uart_txd
);
    localparam integer WIDTH = 32, FRAC = 16, N_MEAS = 8;
    wire rst = btn0;

    // fixed prior + noise (from scripts/ekf2d_filter_golden.py -- byte-identical to ekf_filter_arty)
    localparam signed [WIDTH-1:0] X0_0 = 32'h00030000, X0_1 = 32'h00040000;
    localparam signed [WIDTH-1:0] P0_0 = 32'h00008000, P0_1 = 32'h0000199A,
                                  P0_2 = 32'h0000199A, P0_3 = 32'h00008000;
    localparam signed [WIDTH-1:0] Q_0 = 32'h00000042, Q_1 = 32'h00000000,
                                  Q_2 = 32'h00000000, Q_3 = 32'h00000042;
    localparam signed [WIDTH-1:0] R_0 = 32'h0000051F, R_1 = 32'h00000000,
                                  R_2 = 32'h00000000, R_3 = 32'h00000083;

    // --- measurement ROM: z per step (2 words each) ---
    // Indexed by m_tel (the step index the filter latches THIS cycle), not m: m advances at the
    // same edge flt_vin pulses, so the filter would otherwise latch z[m+1] under label m -- an
    // off-by-one that corrupts x' (which depends on z) but not P (which does not).
    reg [3:0] m;
    reg [3:0] m_tel;
    reg signed [WIDTH-1:0] z0, z1;
    always @(*) begin
        case (m_tel)
            4'd0: begin z0=32'h0005629A; z1=32'h000130B7; end
            4'd1: begin z0=32'h0005629A; z1=32'h000130B7; end
            4'd2: begin z0=32'h0005629A; z1=32'h000130B7; end
            4'd3: begin z0=32'h0005629A; z1=32'h000130B7; end
            4'd4: begin z0=32'h0005629A; z1=32'h000130B7; end
            4'd5: begin z0=32'h0005629A; z1=32'h000130B7; end
            4'd6: begin z0=32'h0005629A; z1=32'h000130B7; end
            4'd7: begin z0=32'h0005629A; z1=32'h000130B7; end
            default: begin z0=32'h0005629A; z1=32'h000130B7; end
        endcase
    end

    // --- quasi-static streaming controller: LOAD (replay) then N steps, each held a UART frame ---
    reg [31:0] advance_counter = 32'd0;
    reg        do_load = 1'b1;
    reg        flt_load, flt_vin;
    always @(posedge clk_100mhz) begin
        if (rst) begin
            advance_counter <= 32'd0; m <= 4'd0; do_load <= 1'b1;
            flt_load <= 1'b0; flt_vin <= 1'b0; m_tel <= 4'd0; led <= 4'd0;
        end else begin
            flt_load <= 1'b0; flt_vin <= 1'b0;
            if (advance_counter == ADVANCE_PERIOD - 1) begin
                advance_counter <= 32'd0;
                if (do_load) begin
                    flt_load <= 1'b1; m <= 4'd0; do_load <= 1'b0;
                end else begin
                    flt_vin <= 1'b1; m_tel <= m; led <= {1'b0, m[2:0]};
                    if (m == N_MEAS - 1) do_load <= 1'b1;
                    else m <= m + 4'd1;
                end
            end else advance_counter <= advance_counter + 32'd1;
        end
    end

    // --- THE DUT: Forge's emitted pipeline (rtl/track_emitted.v, generated -- do not hand-edit) ---
    // Same port list as the hand-written ekf2d_filter, so this instantiation is the ONLY structural
    // difference between this anchor and ekf_filter_arty.
    wire flt_valid;
    wire signed [WIDTH-1:0] fx0, fx1, fp0, fp1, fp2, fp3;
    track_pipeline #(.WIDTH(WIDTH), .FRAC(FRAC)) u_filter (
        .clk(clk_100mhz), .rst(rst),
        .load(flt_load), .x_in0(X0_0), .x_in1(X0_1),
        .p_in0(P0_0), .p_in1(P0_1), .p_in2(P0_2), .p_in3(P0_3),
        .valid_in(flt_vin), .z0(z0), .z1(z1),
        .q0(Q_0), .q1(Q_1), .q2(Q_2), .q3(Q_3),
        .r0(R_0), .r1(R_1), .r2(R_2), .r3(R_3),
        .valid_out(flt_valid),
        .x_out0(fx0), .x_out1(fx1),
        .p_out0(fp0), .p_out1(fp1), .p_out2(fp2), .p_out3(fp3)
    );

    ekf_filter_uart_tx #(.FRAME_PERIOD_CYCLES(FRAME_PERIOD)) telemetry (
        .clk(clk_100mhz), .rst(rst),
        .m_q16({28'd0, m_tel}),
        .x0_q16(fx0), .x1_q16(fx1),
        .p0_q16(fp0), .p1_q16(fp1), .p2_q16(fp2), .p3_q16(fp3),
        .out_valid(flt_valid), .tx(uart_txd)
    );
endmodule

`default_nettype wire
