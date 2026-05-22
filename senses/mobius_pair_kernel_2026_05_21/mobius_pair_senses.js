const state={idx:0,audio:null,osc:[],muted:false};
const samples=[];
async function load(){const res=await fetch('mobius_pair_trace_data_2026_05_21.json');const data=await res.json();samples.push(...data.samples.filter(r=>r.status==='PASS'));render();}
function render(){const s=samples[state.idx%samples.length]||{};document.getElementById('sample').textContent=JSON.stringify(s,null,2);document.getElementById('status').textContent=`sample ${state.idx+1}/${samples.length}: x=${s.x}`;}
function tone(freq,dur=0.35){if(state.muted)return;if(!state.audio)state.audio=new AudioContext();const o=state.audio.createOscillator();const g=state.audio.createGain();o.frequency.value=freq;g.gain.value=0.04;o.connect(g);g.connect(state.audio.destination);o.start();o.stop(state.audio.currentTime+dur);}
function play(){const s=samples[state.idx%samples.length]; if(!s)return; tone(180+Math.abs(s.alpha)*80); setTimeout(()=>tone(360+Math.min(Math.abs(s.beta),8)*20),120); setTimeout(()=>tone(240),240);}
function stop(){state.osc.forEach(o=>o.stop());state.osc=[];}
function step(){state.idx=(state.idx+1)%samples.length;render();}
function toggleMute(){state.muted=!state.muted;document.getElementById('mute').textContent=state.muted?'Unmute':'Mute';}
window.addEventListener('DOMContentLoaded',()=>{load();document.getElementById('play').onclick=play;document.getElementById('stop').onclick=stop;document.getElementById('step').onclick=step;document.getElementById('mute').onclick=toggleMute;});
