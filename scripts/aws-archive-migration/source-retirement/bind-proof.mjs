// Local metadata proof only. Stream pins; never decode catalogs or read key files.
import fs from 'node:fs/promises';
import {createReadStream} from 'node:fs';
import {createHash} from 'node:crypto';
import os from 'node:os';
import path from 'node:path';
const state=path.join(os.homedir(),'.quantyra/aws-migration-20261006');
const here=path.dirname(new URL(import.meta.url).pathname.replace(/^\/([A-Za-z]:)/,'$1'));
const hash=b=>createHash('sha256').update(b).digest('hex');
const canonical=x=>Array.isArray(x)?x.map(canonical):x&&typeof x==='object'?Object.fromEntries(Object.keys(x).sort().map(k=>[k,canonical(x[k])])):x;
const canonHash=x=>hash(JSON.stringify(canonical(x)));
const requireThat=(ok,c)=>{if(!ok)throw Error(c);};
const fileHash=async file=>{const h=createHash('sha256');for await(const b of createReadStream(file))h.update(b);return h.digest('hex');};
const packetBytes=await fs.readFile(path.join(state,'repair/fullscope-packet.json'));
const packet=JSON.parse(packetBytes), packetHash=hash(packetBytes);
requireThat(packetHash==='713abbeaeb65c456a1ba333ed0d8c77f7da8ba756085b42cd4493653ecd648ce','PACKET_CHANGED');
requireThat(packet.complete&&packet.versions===205&&packet.core_chunks===51&&packet.recovery_unique_chunks===54&&packet.recovery_catalogs===44&&packet.artifacts.length===305&&packet.catalogs.length===45,'FULL_SCOPE');
const roots=[state,path.join(os.homedir(),'.quantyra/archive-catalogs'),path.resolve(here,'..')];
for(const p of packet.artifacts){
  const f=path.resolve(p.file);
  requireThat(roots.some(r=>f.startsWith(path.resolve(r)+path.sep))&&!/credentials|\.key$/i.test(f),'UNSAFE_PIN');
  requireThat(await fileHash(f)===p.sha256,'PACKET_PIN_CHANGED');
}
for(const c of packet.catalogs)requireThat(packet.artifacts.some(p=>p.file===c.catalog_file&&p.sha256===c.catalog_sha256),'CATALOG_BYTE_PIN');
const readBound=async name=>{const f=path.join(state,name), bytes=await fs.readFile(f);requireThat(packet.artifacts.some(p=>path.resolve(p.file)===f&&p.sha256===hash(bytes)),'UNBOUND_INPUT');return JSON.parse(bytes);};
const mapping=await readBound('version-mapping.json');
const source=await readBound('repair/verified-source-inventory.json');
const dest=await readBound('repair/verified-destination-inventory.json');
requireThat(hash(JSON.stringify(mapping))===packet.mapping_rows_sha256,'MAPPING_ROWS_PIN');
// Existing packet row pins use the archive owner's JSON.stringify representation.
// Verify those exact bytes separately from our canonical successor representation.
requireThat(hash(JSON.stringify(source))===packet.source_inventory_rows_sha256,'SOURCE_ROWS_PIN');
requireThat(hash(JSON.stringify(dest))===packet.destination_inventory_rows_sha256,'DEST_ROWS_PIN');
const rows=mapping.map(r=>({key:r.key,source_version:r.version,destination_version:r.destination_version,bytes:r.bytes,source_etag:r.etag,sha256:r.sha256})).sort((a,b)=>a.key<b.key?-1:a.key>b.key?1:a.source_version<b.source_version?-1:1);
requireThat(rows.length===205&&rows.reduce((n,r)=>n+r.bytes,0)===18579936167,'COUNT_BYTES');
for(const field of ['source_version','destination_version'])requireThat(new Set(rows.map(r=>JSON.stringify([r.key,r[field]]))).size===205&&rows.every(r=>r[field]&&r[field]!=='null'),'EXACT_INJECTIVE_IDS');
requireThat(rows.every(r=>/^[a-f0-9]{64}$/.test(r.sha256)&&source.some(s=>s.key===r.key&&s.version===r.source_version&&s.bytes===r.bytes&&s.etag===r.source_etag)&&dest.some(d=>d.key===r.key&&d.version===r.destination_version&&d.bytes===r.bytes)),'EXACT_MAPPING_COVERAGE');
requireThat(source.length===205&&dest.length===205&&source.every(r=>r.kind==='object')&&dest.every(r=>r.kind==='object')&&packet.retained_destination_versions===0,'NO_UNACCOUNTED_ROWS');
const a={type:'archive-retirement-allowlist-v1',source:'quantyra-research-archive-485386182336-us-east-1',destination:'quantyra-research-archive-063280428495-us-east-1',packet_sha256:packetHash,rows,catalogs:packet.catalogs,packet_artifacts:packet.artifacts};
const verifyOnly=process.argv.includes('--verify-only');
const allowlistBytes=JSON.stringify(canonical(a),null,2)+'\n';
if(verifyOnly)requireThat(await fs.readFile(path.join(here,'evidence/bound-allowlist.json'),'utf8')===allowlistBytes,'BOUND_ALLOWLIST_CHANGED');
else await fs.writeFile(path.join(here,'evidence/bound-allowlist.json'),allowlistBytes,{flag:'wx'});
const receipt={type:'archive-retirement-local-proof-inventory-v1',at:new Date().toISOString(),packet_sha256:packetHash,packet_pins_checked:305,catalog_pins_checked:45,versions:205,bytes:18579936167,canonical_allowlist_sha256:canonHash(a),mapping_stored_sha256:await fileHash(path.join(state,'version-mapping.json')),source_rows_sha256:packet.source_inventory_rows_sha256,destination_rows_sha256:packet.destination_inventory_rows_sha256,hashes_status:'author-proof-only-requires-independent-acceptance',current_cloud_inventory:'NOT_OBSERVED',cloud_requests:0,cloud_mutations:0,payload_downloads:0,key_reads:0,root_acceptance:false,source_eligibility:'HOLD'};
if(!verifyOnly)await fs.writeFile(path.join(here,'evidence/local-proof-inventory.json'),JSON.stringify(receipt,null,2)+'\n',{flag:'wx'});
console.log(JSON.stringify(receipt));
