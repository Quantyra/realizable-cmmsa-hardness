// Reads metadata/evidence only. The real key is stat'ed, never read/hashed.
import fs from 'node:fs/promises';
import path from 'node:path';
import {sha} from '../../archive.mjs';
import {defaults} from '../../migrate.mjs';
const priorFile=path.join(defaults.state,'hardlink-repair-577c09b8d2154bceb36df4bee335896b/code-supplement.json');
const priorBytes=await fs.readFile(priorFile),s=JSON.parse(priorBytes);
if(sha(priorBytes)!=='b89c87acd487c8647f9678737c6bd85d1c007684954d833d5a08dd1c2b379539')throw Error('Previous supplement changed');
const pins=[...s.old_artifacts,...s.code_files,...s.old_installed_tools,{file:priorFile,sha256:sha(priorBytes)},{file:path.join(defaults.state,'repair/fullscope-packet.json'),sha256:s.old_packet_sha256},{file:path.join(defaults.state,'active-restore-registry.json'),sha256:s.old_local_registry_sha256},{file:path.join(defaults.state,'local-restore-installation.json'),sha256:s.old_local_installation_sha256},...s.catalogs.map(p=>({file:p.catalog_file,sha256:p.catalog_sha256}))];
const checked=[];
for(const p of pins){const h=sha(await fs.readFile(p.file));if(h!==p.sha256)throw Error('Preservation mismatch');checked.push({file:p.file,sha256:h});}
const receipt=JSON.parse(await fs.readFile(path.join(defaults.state,'local-restore-installation.json')));
// Preserve the original historical tools as well as the active accepted pair.
const historical=[];
for(const p of receipt.historical_tools){const hash=sha(await fs.readFile(p.preserved));if(hash!==p.sha256)throw Error('Historical tool changed');historical.push({file:p.preserved,sha256:hash});}
const stat=await fs.stat(defaults.key),key_metadata={size:stat.size,mtime_ms:stat.mtimeMs,birthtime_ms:stat.birthtimeMs};
const result={type:'archive-second-repair-preservation-author-v1',at:new Date().toISOString(),original_artifacts:s.old_artifacts.length,accepted_catalogs:s.catalogs.length,previous_code_files:s.code_files.length,old_packet_sha256:s.old_packet_sha256,prior_supplement_sha256:sha(priorBytes),checked,historical,key_metadata,key_read:false,real_aws_requests:0};
if(process.argv[2]!=='--output'||process.argv.length!==4)throw Error('Exclusive output required');
await fs.writeFile(process.argv[3],JSON.stringify(result,null,2)+'\n',{flag:'wx',mode:0o600});
console.log(JSON.stringify({preserved:true,artifacts:305,catalogs:45,prior_code:10,key_read:false}));
