const DATA = {"kernels": [{"kernel_id": "operator_affine_01_a2_b3", "a": 2, "b": 3, "shift_expression": "y=2*x+3", "alpha_expression": "x/(2*x+3)", "beta_expression": "(2*x+3)/x", "singularity_set": [0, -1.5], "limit_alpha_target": 0.5, "limit_beta_target": 2, "status": "PASS"}, {"kernel_id": "operator_affine_02_aneg4_bneg5", "a": -4, "b": -5, "shift_expression": "y=-4*x+-5", "alpha_expression": "x/(-4*x+-5)", "beta_expression": "(-4*x+-5)/x", "singularity_set": [0, -1.25], "limit_alpha_target": -0.25, "limit_beta_target": -4, "status": "PASS"}, {"kernel_id": "operator_affine_03_aneg4_bneg3", "a": -4, "b": -3, "shift_expression": "y=-4*x+-3", "alpha_expression": "x/(-4*x+-3)", "beta_expression": "(-4*x+-3)/x", "singularity_set": [0, -0.75], "limit_alpha_target": -0.25, "limit_beta_target": -4, "status": "PASS"}, {"kernel_id": "operator_affine_04_aneg4_bneg2", "a": -4, "b": -2, "shift_expression": "y=-4*x+-2", "alpha_expression": "x/(-4*x+-2)", "beta_expression": "(-4*x+-2)/x", "singularity_set": [0, -0.5], "limit_alpha_target": -0.25, "limit_beta_target": -4, "status": "PASS"}, {"kernel_id": "operator_affine_05_aneg4_bneg1", "a": -4, "b": -1, "shift_expression": "y=-4*x+-1", "alpha_expression": "x/(-4*x+-1)", "beta_expression": "(-4*x+-1)/x", "singularity_set": [0, -0.25], "limit_alpha_target": -0.25, "limit_beta_target": -4, "status": "PASS"}, {"kernel_id": "operator_affine_06_aneg4_b1", "a": -4, "b": 1, "shift_expression": "y=-4*x+1", "alpha_expression": "x/(-4*x+1)", "beta_expression": "(-4*x+1)/x", "singularity_set": [0, 0.25], "limit_alpha_target": -0.25, "limit_beta_target": -4, "status": "PASS"}, {"kernel_id": "operator_affine_07_aneg4_b2", "a": -4, "b": 2, "shift_expression": "y=-4*x+2", "alpha_expression": "x/(-4*x+2)", "beta_expression": "(-4*x+2)/x", "singularity_set": [0, 0.5], "limit_alpha_target": -0.25, "limit_beta_target": -4, "status": "PASS"}, {"kernel_id": "operator_affine_08_aneg4_b3", "a": -4, "b": 3, "shift_expression": "y=-4*x+3", "alpha_expression": "x/(-4*x+3)", "beta_expression": "(-4*x+3)/x", "singularity_set": [0, 0.75], "limit_alpha_target": -0.25, "limit_beta_target": -4, "status": "PASS"}, {"kernel_id": "operator_affine_09_aneg4_b5", "a": -4, "b": 5, "shift_expression": "y=-4*x+5", "alpha_expression": "x/(-4*x+5)", "beta_expression": "(-4*x+5)/x", "singularity_set": [0, 1.25], "limit_alpha_target": -0.25, "limit_beta_target": -4, "status": "PASS"}, {"kernel_id": "operator_affine_10_aneg3_bneg5", "a": -3, "b": -5, "shift_expression": "y=-3*x+-5", "alpha_expression": "x/(-3*x+-5)", "beta_expression": "(-3*x+-5)/x", "singularity_set": [0, -1.6666666666666667], "limit_alpha_target": -0.3333333333333333, "limit_beta_target": -3, "status": "PASS"}]};
const select = document.getElementById('kernel');
const readout = document.getElementById('readout');
let audioContext = null, oscillator = null;
DATA.kernels.forEach((kernel, index) => {
  const option = document.createElement('option');
  option.value = index;
  option.textContent = `${kernel.kernel_id} a=${kernel.a} b=${kernel.b}`;
  select.appendChild(option);
});
function current() { return DATA.kernels[Number(select.value || 0)]; }
function update() { readout.textContent = JSON.stringify(current(), null, 2); }
function play() {
  stop();
  audioContext = new (window.AudioContext || window.webkitAudioContext)();
  oscillator = audioContext.createOscillator();
  const kernel = current();
  oscillator.type = kernel.a < 0 ? 'triangle' : 'sine';
  oscillator.frequency.value = 220 + Math.abs(kernel.a) * 45 + Math.abs(kernel.b) * 8;
  oscillator.connect(audioContext.destination);
  oscillator.start();
}
function stop() { if (oscillator) oscillator.stop(); oscillator = null; if (audioContext) audioContext.close(); audioContext = null; }
document.getElementById('play').onclick = play;
document.getElementById('stop').onclick = stop;
document.getElementById('mute').onclick = stop;
document.getElementById('step').onclick = () => { select.value = (Number(select.value || 0) + 1) % DATA.kernels.length; update(); };
select.onchange = update;
update();
