// Separate successor: the old accepted source/runtime remains byte-identical.
import * as fs from 'node:fs/promises';
import { constants, createReadStream } from 'node:fs';
import path from 'node:path';
import { GetObjectCommand } from '@aws-sdk/client-s3';
import { validate, safePath, sha } from '../archive.mjs';
import { DEST, SOURCE, hashBody } from '../migrate.mjs';
import { decodeCatalog } from '../catalog-bytes.mjs';
import { checkedTarget } from '../restore.mjs';
import { verifyChunk } from './verify-chunk.mjs';
const digest = x => sha(Buffer.from(JSON.stringify(x)));
export function diskBudget(p, unit = 4096n) {
  if(unit<=0n)throw Error('Unknown allocation unit');
  // Round file allocation up and reserve one metadata block per file/directory.
  const allocated=m=>((BigInt(m.bytes)+unit-1n)/unit+1n)*unit;
  const directories=new Set();for(const x of p.outputs)for(let d=path.posix.dirname(x.logical.path);d!=='.';d=path.posix.dirname(d))directories.add(d);
  return p.outputs.reduce((n,x)=>n+allocated(x.logical),0n)+[...p.contents.values()].reduce((n,m)=>n+allocated(m),0n)+BigInt(directories.size+1)*unit+1048576n;
}
export function plan(c, paths = [], {bounded = false} = {}) {
  const {chunks, members} = validate(c), selected = new Map();
  if (!Array.isArray(paths)) throw Error('Invalid selectors');
  if (!paths.length) for (const m of members.values()) selected.set(m.path,m);
  for (const value of paths) {
    if (typeof value !== 'string') throw Error('Invalid selector');
    const p = value.replace(/\/$/,'');safePath(p+'/_selector');
    const matches = [...members.values()].filter(m=>m.path===p||m.path.startsWith(p+'/'));
    if (!matches.length) throw Error('Missing selection');
    for (const m of matches) selected.set(m.path,m);
  }
  if (bounded && (paths.length !== 1 || selected.size !== 1 || !members.has(paths[0]) || [...selected.values()][0].bytes > 1048576)) throw Error('Select one bounded logical member');
  const outputs=[], contents=new Map(), required=new Set();
  for (const logical of selected.values()) {
    const chain=[logical];while(chain.at(-1).hardlink!=null)chain.push(members.get(chain.at(-1).hardlink));
    const content=chain.at(-1);contents.set(content.path,content);for(const m of chain)required.add(m.chunk);outputs.push({logical,content,chain});
  }
  let changed;
  do {changed=false;for(const m of members.values())if(required.has(m.chunk)&&m.hardlink!=null){const n=members.get(m.hardlink).chunk;if(!required.has(n)){required.add(n);changed=true;}}}while(changed);
  const outputBytes=outputs.reduce((n,x)=>n+BigInt(x.logical.bytes),0n);
  if(outputBytes>BigInt(Number.MAX_SAFE_INTEGER))throw Error('Output total exceeds safe accounting');
  const p={chunks,members,outputs,contents,required,bytes:Number(outputBytes)};return {...p,requiredDiskBytes:diskBudget(p)};
}
export function selection(c, requested) {
  const p=plan(c,[requested],{bounded:true});return {...p,...p.outputs[0]};
}
export async function restore(o, client, services = {}) {
  const raw=await fs.readFile(o.catalog),c=decodeCatalog(raw),p=plan(c,o.paths??(o.path?[o.path]:[]),{bounded:o.bounded??false});
  if(![SOURCE,DEST].includes(c.bucket))throw Error('Unexpected bucket');
  if(o.dryRun)return {mode:'dry-run',chunks:p.required.size,members:p.outputs.length,bytes:p.bytes,required_disk_bytes:String(p.requiredDiskBytes)};
  if(!client?.send)throw Error('Accepted consumer client required');
  const root=await fs.realpath(o.workspaceRoot),stat=await fs.lstat(o.workspaceRoot);
  if(!stat.isDirectory()||stat.isSymbolicLink())throw Error('Output root must be a real directory');
  const targets=[];
  for(const x of p.outputs){const target=await checkedTarget(root,x.logical.path);if(await fs.lstat(target).catch(e=>{if(e.code==='ENOENT')return null;throw e;}))throw Error('Refusing existing output');targets.push(target);}
  const space=await fs.statfs(root,{bigint:true});p.requiredDiskBytes=diskBudget(p,space.bsize);
  const available=services.freeBytes?await services.freeBytes(root):space.bsize*space.bavail;
  if(available<p.requiredDiskBytes)throw Error('Insufficient disk for staged and published outputs');
  const scratch=await fs.mkdtemp(path.join(root,'.qarc-logical-')),authenticated=new Set(),stages=new Map();let key;
  try {
    key=await fs.readFile(o.keyFile);
    for(const m of p.contents.values())stages.set(m.path,path.join(scratch,'content-'+stages.size+'.pending'));
    for(const chunk of [...p.chunks.values()].filter(x=>p.required.has(x.number)).sort((a,b)=>a.number-b.number)){
      const r=await client.send(new GetObjectCommand({Bucket:c.bucket,ExpectedBucketOwner:c.bucket===DEST?'063280428495':'485386182336',Key:chunk.key,VersionId:chunk.version_id}));
      await verifyChunk(r.Body,chunk,p.members,key,authenticated,stages);
    }
    for(const x of p.outputs)if(x.chain.some(m=>!authenticated.has(m.path)))throw Error('Logical chain not authenticated');
    for(const m of p.contents.values()){const result=await hashBody(createReadStream(stages.get(m.path)));if(result.bytes!==m.bytes||result.sha256!==m.sha256)throw Error('Restored bytes differ');}
    // No output is published before ALL required chunks/links/content authenticate.
    for(let i=0;i<p.outputs.length;i++){const x=p.outputs[i];await fs.mkdir(path.dirname(targets[i]),{recursive:true});await checkedTarget(root,x.logical.path);await fs.copyFile(stages.get(x.content.path),targets[i],constants.COPYFILE_EXCL);}
    const bindings=p.outputs.map(x=>({bytes:x.logical.bytes,sha256:x.logical.sha256,member_metadata_sha256:digest(x.logical),content_member_metadata_sha256:digest(x.content),logical_member_kind:x.logical.hardlink==null?'regular':'hardlink',materialized_kind:'regular',hardlink_depth:x.chain.length-1}));
    return {mode:'restored',chunks:p.required.size,members:bindings.length,bytes:p.bytes,...bindings.length===1?bindings[0]:{outputs_sha256:digest(bindings)},outputs:bindings,bucket:c.bucket,catalog_sha256:sha(raw),required_disk_bytes:String(p.requiredDiskBytes),exact_versions:[...p.chunks.values()].filter(x=>p.required.has(x.number)).map(x=>({key:x.key,version_id:x.version_id,ciphertext_sha256:x.sha256,tar_sha256:x.tar_sha256}))};
  } finally {
    key?.fill(0);const s=await fs.lstat(scratch);if(path.dirname(scratch)!==root||!s.isDirectory()||s.isSymbolicLink())throw Error('Unsafe scratch cleanup');await fs.rm(scratch,{recursive:true,force:true});
  }
}
