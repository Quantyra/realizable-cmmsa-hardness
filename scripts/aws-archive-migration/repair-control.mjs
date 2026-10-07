// Continue the existing single writer, then complete author evidence only.
// No active restore switch, source deletion, root acceptance or Git mutation.
import * as fs from 'node:fs/promises';
import path from 'node:path';
import {spawn} from 'node:child_process';
import {defaults,save} from './migrate.mjs';
import {sha} from './archive.mjs';
import {requireThat as check} from './custody.mjs';
const base=path.join(defaults.state,'repair'),read=p=>fs.readFile(p,'utf8').then(JSON.parse),lock=path.join(base,'control.lock');
async function main(){
  await fs.mkdir(base,{recursive:true});const handle=await fs.open(lock,'wx',0o600);await handle.writeFile(JSON.stringify({pid:process.pid,at:new Date().toISOString()}));await handle.close();
  try{
    let waiting=0;while(true){const actor=await read(path.join(base,'writer.lock')).catch(e=>{if(e.code==='ENOENT')return null;throw e;});if(!actor)break;let alive=false;try{process.kill(actor.pid,0);alive=true;}catch(e){check(e.code==='ESRCH','cannot-check-copy-actor');}check(alive,'copy-actor-dead-with-lock');if(waiting++%12===0){await save(path.join(base,'control-status.json'),{pid:process.pid,phase:'waiting-for-existing-copy',copy_pid:actor.pid,at:new Date().toISOString()});console.log(JSON.stringify({phase:'waiting-for-existing-copy',copy_pid:actor.pid}));}await new Promise(r=>setTimeout(r,5000));}
    const receipt=await read(path.join(base,'copy-all-receipt.json'));check(receipt.complete&&receipt.versions===205&&receipt.mapping_sha256===sha(await fs.readFile(path.join(defaults.state,'version-mapping.json'))),'copy-terminal-not-current');
    for(const [name,args] of [['recovery-authentication',['recovery.mjs','verify-destination']],['prepare-recovery-successors',['recovery.mjs','activate']],['actual-destination-restore',['bounded-restore.mjs','destination']],['author-exact-version-verification',['repair-verify.mjs']],['temporary-bridge-removal',['server-copy.mjs','remove-bridge']],['prepare-fullscope-packet',['prepare-activation.mjs']]]){
      await save(path.join(base,'control-status.json'),{pid:process.pid,phase:name,at:new Date().toISOString()});console.log(JSON.stringify({phase:name}));await new Promise((resolve,reject)=>{const child=spawn(process.execPath,[path.join(path.dirname(new URL(import.meta.url).pathname.replace(/^\/([A-Za-z]:)/,'$1')),args[0]),...args.slice(1)],{stdio:'inherit',windowsHide:true});child.once('error',()=>reject(Error('child-launch-failed')));child.once('exit',code=>code===0?resolve():reject(Error('child-failed')));});
    }
    const packet=await fs.readFile(path.join(base,'fullscope-packet.json'));await save(path.join(base,'control-status.json'),{pid:process.pid,phase:'author-complete-awaiting-root-acceptance',at:new Date().toISOString(),packet_sha256:sha(packet),active_tool_switch:false,source_retirement:false});console.log(JSON.stringify({phase:'author-complete-awaiting-root-acceptance',packet_sha256:sha(packet)}));
  }finally{await fs.rm(lock);}
}
main().catch(async e=>{const r={pid:process.pid,phase:'control-failed',at:new Date().toISOString(),safe_reason:e.safeReason??null,error:e.name};await save(path.join(base,'control-failure.json'),r).catch(()=>{});console.error(JSON.stringify(r));process.exitCode=1;});
