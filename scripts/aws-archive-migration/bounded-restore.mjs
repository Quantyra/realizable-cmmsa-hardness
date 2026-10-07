import * as fs from 'node:fs/promises';
import path from 'node:path';
import { defaults, save } from './migrate.mjs';
import { restore } from './restore.mjs';
const mode=process.argv[2];
async function main() {
  if(!['source','destination'].includes(mode))throw Error();
  const catalog=mode==='source'?defaults.catalog:path.join(defaults.state,'successor-catalog.json'),c=JSON.parse(await fs.readFile(catalog,'utf8'));
  const chunks=new Map(c.chunks.map(x=>[x.number,x]));
  const member=c.members.filter(m=>m.hardlink==null&&m.path.startsWith('realizable-cmmsa-hardness/')&&/\.log$/.test(m.path)&&m.bytes>0&&m.bytes<=65536).sort((a,b)=>chunks.get(a.chunk).bytes-chunks.get(b.chunk).bytes||a.bytes-b.bytes)[0];
  if(!member)throw Error();const root=path.join(defaults.state,'bounded-'+mode);await fs.mkdir(root,{recursive:true});
  const receipt=await restore({catalog,keyFile:defaults.key,workspaceRoot:root,path:member.path});
  await save(path.join(defaults.state,'bounded-'+mode+'-receipt.json'),{at:new Date().toISOString(),...receipt});console.log(JSON.stringify(receipt));
}
main().catch(()=>{console.error('Bounded restore failed; no payload printed');process.exitCode=1;});
