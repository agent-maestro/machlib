/-!
# AXI-Stream wrapper control FSM — deadlock-free, drop-free, timing-honest

The scalar Kalman kernel closes 100 MHz but lived in a vector-ROM sandbox. To feed it
live sensor data it needs a standard bus: AXI4-Stream `ready`/`valid` with backpressure.
The risk a hand-written wrapper carries is exactly what this file rules out by proof —
that the control FSM could **deadlock**, **drop a sample**, or **re-trigger the
multi-cycle core mid-computation** (violating its timing contract).

The wrapper is a 3-state Moore machine around a multi-cycle core:

  * `idle`    — `s_axis_tready = 1`; on an input beat (`tvalid`&`tready`) latch the
                sample, pulse the core's `valid_in`, go `busy`.
  * `busy`    — the core computes; wait for its `valid_out` (`done`), go `present`.
  * `present` — `m_axis_tvalid = 1`, output held stable; wait for `m_axis_tready`
                (`tready`), go `idle`.

Everything here is **pure discrete reasoning over `Bool`/`Nat`** — no `MachLib.Real`, no
axioms beyond Lean's core. The same FSM is what the RTL wrapper implements, so the proof
and the circuit share one definition (no drift), exactly like the emitted-kernel proofs.

## What is proven

SAFETY
  * `validIn_pulse`   — `valid_in` is a 1-cycle pulse: high at `n` ⟹ low at `n+1`. The
                        multi-cycle core is never re-triggered while it computes, so its
                        one-sample-per-run timing contract is respected.
  * `no_accept_off_idle` — an input is accepted ONLY from `idle`.
  * `conservation`    — `accepted n = emitted n + occ(state n)`, with `occ ∈ {0,1}`: at
                        most one sample in flight; combined with `no_accept_off_idle`, an
                        in-flight sample is never overwritten — **no dropped sample** —
                        and (`no_drop`) whenever the wrapper is idle every accepted input
                        has been emitted.
  * `present_holds`   — under downstream backpressure the output is held in `present`
                        with `tvalid` asserted and stable (AXI no-retraction).

LIVENESS / DEADLOCK-FREEDOM
  * `*_leaves_on_*`   — each waiting state progresses the cycle its enabling signal arrives.
  * `busy_holds`      — while `done` is low it waits in the CORRECT state (never stuck
                        elsewhere).
  * `round_trip`      — from `idle`, once the three signals arrive (immediately here; the
                        `*_holds` lemmas cover arbitrary finite waits) the wrapper accepts,
                        computes, emits EXACTLY one beat, and returns to `idle` — a bounded
                        round trip, so it can never lock up.
-/

namespace MachLib.Axi

/-- Wrapper control state (Moore machine). -/
inductive WState
  | idle
  | busy
  | present
deriving DecidableEq

open WState

/-- The AXI environment the wrapper sees each cycle: `tvalid` — upstream offers an input
beat; `tready` — downstream will accept an output beat; `done` — the core has raised
`valid_out` (its multi-cycle latency elapsed). -/
structure Env where
  tvalid : Bool
  tready : Bool
  done   : Bool

/-- `s_axis_tready`: the wrapper accepts input only when idle. -/
def sready : WState → Bool
  | idle => true
  | _    => false

/-- `m_axis_tvalid`: the wrapper offers output only when a result is present. -/
def mvalid : WState → Bool
  | present => true
  | _       => false

/-- An input beat is consumed exactly when both sides agree (`tvalid` & `sready`). -/
def fireIn (s : WState) (e : Env) : Bool := sready s && e.tvalid

/-- The core's `valid_in` pulse equals the input-beat handshake. -/
def validIn (s : WState) (e : Env) : Bool := fireIn s e

/-- An output beat is produced exactly when both sides agree (`mvalid` & `tready`). -/
def fireOut (s : WState) (e : Env) : Bool := mvalid s && e.tready

/-- The transition. `idle`→`busy` on an input beat; `busy`→`present` when the core
finishes; `present`→`idle` when the output beat is taken (else hold — no retraction). -/
def step (s : WState) (e : Env) : WState :=
  match s with
  | idle    => if e.tvalid then busy else idle
  | busy    => if e.done then present else busy
  | present => if e.tready then idle else present

/-- The run of the wrapper under an environment stream, from `idle`. -/
def run (env : Nat → Env) : Nat → WState
  | 0     => idle
  | n + 1 => step (run env n) (env n)

/-- Occupancy: how many samples are in flight in a given state (0 idle, 1 busy/present). -/
def occ : WState → Nat
  | idle => 0
  | _    => 1

/-- Count a Bool as 0/1. -/
def bc (b : Bool) : Nat := if b then 1 else 0

/-- Total input beats accepted through cycle `n`. -/
def accepted (env : Nat → Env) : Nat → Nat
  | 0     => 0
  | n + 1 => accepted env n + bc (fireIn (run env n) (env n))

/-- Total output beats emitted through cycle `n`. -/
def emitted (env : Nat → Env) : Nat → Nat
  | 0     => 0
  | n + 1 => emitted env n + bc (fireOut (run env n) (env n))

/-! ## Safety -/

/-- Occupancy is at most one. -/
theorem occ_le_one : ∀ s, occ s ≤ 1
  | idle => by decide
  | busy => by decide
  | present => by decide

/-- **`valid_in` is a 1-cycle pulse.** If it fires at `n`, it is low at `n+1` — the
multi-cycle core is never re-triggered while it is still computing. -/
theorem validIn_pulse (env : Nat → Env) (n : Nat) :
    validIn (run env n) (env n) = true → validIn (run env (n + 1)) (env (n + 1)) = false := by
  intro h
  -- firing requires idle, which steps to busy; busy has sready=false so validIn is false
  simp only [validIn, fireIn, sready] at h ⊢
  cases hs : run env n with
  | idle =>
      have htv : (env n).tvalid = true := by simpa [hs] using h
      simp [run, step, hs, htv]
  | busy => simp [hs] at h
  | present => simp [hs] at h

/-- **Input is accepted only from `idle`.** So while a sample is in flight (`busy`/
`present`) none is accepted — an in-flight sample can never be overwritten. -/
theorem no_accept_off_idle (s : WState) (e : Env) :
    s ≠ idle → fireIn s e = false := by
  intro h
  cases s with
  | idle => exact absurd rfl h
  | busy => simp [fireIn, sready]
  | present => simp [fireIn, sready]

/-- **Per-cycle occupancy balance** (a finite identity, checked over all 3 states × 8
signal combinations): occupancy in, plus a beat accepted, equals a beat emitted plus
occupancy out. This is the one-place-buffer invariant, one cycle at a time. -/
theorem occ_step (s : WState) (e : Env) :
    occ s + bc (fireIn s e) = bc (fireOut s e) + occ (step s e) := by
  obtain ⟨tv, tr, dn⟩ := e
  cases s <;> cases tv <;> cases tr <;> cases dn <;> decide

/-- **Conservation.** Accepted = emitted + occupancy at every cycle. Since occupancy is
`≤ 1`, at most one sample is ever in flight; since acceptance happens only from `idle`
(occupancy 0), the in-flight sample is never clobbered. -/
theorem conservation (env : Nat → Env) :
    ∀ n, accepted env n = emitted env n + occ (run env n)
  | 0 => rfl
  | n + 1 => by
      have ih := conservation env n
      have hstep := occ_step (run env n) (env n)
      simp only [accepted, emitted, run]
      omega

/-- **No dropped sample.** Whenever the wrapper is idle, every accepted input has been
emitted — nothing is lost in flight. -/
theorem no_drop (env : Nat → Env) (n : Nat) (hidle : run env n = idle) :
    accepted env n = emitted env n := by
  have := conservation env n
  rw [hidle] at this
  simpa [occ] using this

/-- **At most one sample in flight** at any cycle. -/
theorem in_flight_le_one (env : Nat → Env) (n : Nat) :
    accepted env n ≤ emitted env n + 1 := by
  have hc := conservation env n
  have ho := occ_le_one (run env n)
  omega

/-- **Output holds under downstream backpressure** (AXI no-retraction): in `present`
with `tready` low, the wrapper stays in `present`, so `m_axis_tvalid` remains asserted
and the data is unchanged — the beat is not dropped. -/
theorem present_holds (env : Nat → Env) (n : Nat)
    (hp : run env n = present) (hbp : (env n).tready = false) :
    run env (n + 1) = present := by
  simp [run, step, hp, hbp]

/-! ## Liveness / deadlock-freedom

Each waiting state (a) LEAVES the moment its enabling signal arrives, and (b) HOLDS in
the correct state while the signal is low. Together: the wrapper is only ever "stuck"
waiting for a signal it is *supposed* to wait for, and always advances when that signal
comes — it can never lock up in a wrong or absorbing state. `round_trip` puts the three
together into a bounded, single-beat cycle. -/

/-- `idle` accepts and advances the cycle `tvalid` arrives. -/
theorem idle_leaves_on_tvalid (env : Nat → Env) (n : Nat)
    (hs : run env n = idle) (h : (env n).tvalid = true) : run env (n + 1) = busy := by
  simp [run, step, hs, h]

/-- `idle` waits (correctly) while `tvalid` is low — no spurious transition. -/
theorem idle_holds (env : Nat → Env) (n : Nat)
    (hs : run env n = idle) (h : (env n).tvalid = false) : run env (n + 1) = idle := by
  simp [run, step, hs, h]

/-- `busy` advances the cycle the core finishes (`done`). -/
theorem busy_leaves_on_done (env : Nat → Env) (n : Nat)
    (hs : run env n = busy) (h : (env n).done = true) : run env (n + 1) = present := by
  simp [run, step, hs, h]

/-- `busy` waits (correctly) while the core is still computing — never advances early,
so the multi-cycle core's latency is always respected. -/
theorem busy_holds (env : Nat → Env) (n : Nat)
    (hs : run env n = busy) (h : (env n).done = false) : run env (n + 1) = busy := by
  simp [run, step, hs, h]

/-- `present` advances the cycle the output beat is taken (`tready`). -/
theorem present_leaves_on_tready (env : Nat → Env) (n : Nat)
    (hs : run env n = present) (h : (env n).tready = true) : run env (n + 1) = idle := by
  simp [run, step, hs, h]

/-- **No absorbing/stuck state.** For every state there is an environment signal that
advances it to a *different* state — the FSM has no black hole to deadlock in. -/
theorem no_stuck_state : ∀ s : WState, ∃ e : Env, step s e ≠ s := by
  intro s
  cases s with
  | idle => exact ⟨⟨true, false, false⟩, by decide⟩
  | busy => exact ⟨⟨false, false, true⟩, by decide⟩
  | present => exact ⟨⟨false, true, false⟩, by decide⟩

/-- **Bounded, single-beat round trip.** From `idle`, once `tvalid` (here at `n`), the
core's `done` (at `n+1`), and downstream `tready` (at `n+2`) arrive, the wrapper accepts
one input, runs the core, emits exactly one output, and is back in `idle` three cycles
later — with `accepted` and `emitted` each advanced by exactly one. It cannot lock up,
and it neither drops nor duplicates the sample. (Arbitrary finite waits before each
signal are covered by the `*_holds` lemmas, which keep the state — and `tvalid`/data —
stable meanwhile.) -/
theorem round_trip (env : Nat → Env) (n : Nat)
    (h0 : run env n = idle)
    (h1 : (env n).tvalid = true)
    (h2 : (env (n + 1)).done = true)
    (h3 : (env (n + 2)).tready = true) :
    run env (n + 1) = busy ∧ run env (n + 2) = present ∧ run env (n + 3) = idle
      ∧ fireIn (run env n) (env n) = true
      ∧ fireOut (run env (n + 2)) (env (n + 2)) = true
      ∧ accepted env (n + 3) = accepted env n + 1
      ∧ emitted env (n + 3) = emitted env n + 1 := by
  have rb : run env (n + 1) = busy := idle_leaves_on_tvalid env n h0 h1
  have rp : run env (n + 2) = present := busy_leaves_on_done env (n + 1) rb h2
  have ri : run env (n + 3) = idle := present_leaves_on_tready env (n + 2) rp h3
  have fin : fireIn (run env n) (env n) = true := by simp [fireIn, sready, h0, h1]
  have fout : fireOut (run env (n + 2)) (env (n + 2)) = true := by
    simp [fireOut, mvalid, rp, h3]
  -- the two "no fire" facts on the middle cycles
  have finB : fireIn (run env (n + 1)) (env (n + 1)) = false := by rw [rb]; simp [fireIn, sready]
  have finP : fireIn (run env (n + 2)) (env (n + 2)) = false := by rw [rp]; simp [fireIn, sready]
  have foI : fireOut (run env n) (env n) = false := by rw [h0]; simp [fireOut, mvalid]
  have foB : fireOut (run env (n + 1)) (env (n + 1)) = false := by rw [rb]; simp [fireOut, mvalid]
  refine ⟨rb, rp, ri, fin, fout, ?_, ?_⟩
  · -- accepted: only the beat at n counts (busy/present accept nothing)
    have a1 : accepted env (n + 1) = accepted env n + 1 := by simp [accepted, fin, bc]
    have a2 : accepted env (n + 2) = accepted env (n + 1) := by simp [accepted, finB, bc]
    have a3 : accepted env (n + 3) = accepted env (n + 2) := by simp [accepted, finP, bc]
    omega
  · -- emitted: only the beat at n+2 counts (idle/busy emit nothing)
    have e1 : emitted env (n + 1) = emitted env n := by simp [emitted, foI, bc]
    have e2 : emitted env (n + 2) = emitted env (n + 1) := by simp [emitted, foB, bc]
    have e3 : emitted env (n + 3) = emitted env (n + 2) + 1 := by simp [emitted, fout, bc]
    omega

end MachLib.Axi
