// Safe local custody status: hashes/counts/process identities, no member paths.
import * as fs from 'node:fs/promises';
import path from 'node:path';
import {defaults} from './migrate.mjs';
import {sha} from './archive.mjs';
const read=async n=>{try{return JSON.parse(await fs.readFile(path.join(defaults.state,n),'utf8'));}catch(e){if(e.code==='ENOENT')return null;throw e;}};
const source=await read('source-versions.json'),mapping=await read('version-mapping.json'),copy=await read('repair/copy-all-receipt.json'),control=await read('repair/control-status.json'),proof=await read('repair/core-progress.json')??await read('verify-destination/verification-progress.json');
const actors=[];for(const n of ['copy-core.lock','repair/writer.lock','repair/control.lock']){const x=await read(n);if(x){let alive=false;try{process.kill(x.pid,0);alive=true;}catch{}actors.push({lock:n,pid:x.pid,alive});}}
const hashes={};for(const n of ['source-versions.json','version-mapping.json','repair/copy-all-receipt.json','repair/fullscope-packet.json','repair/core-authentication.json','repair/author-version-verification.json','repair/temporary-copy-policy-removal.json','repair/retained-versions.json','bounded-destination-receipt.json']){try{hashes[n]=sha(await fs.readFile(path.join(defaults.state,n)));}catch(e){if(e.code!=='ENOENT')throw e;}}
console.log(JSON.stringify({at:new Date().toISOString(),actors,phase:control?.phase??null,source_versions:source?.rows.length,mapped_versions:mapping?.length,mapped_bytes:mapping?.reduce((n,x)=>n+x.bytes,0),core_authenticated_chunks:proof?.completed.length,copy_complete:copy?.complete??false,hashes,root_acceptance:false,active_tool_switch:false,source_retirement:false}));
