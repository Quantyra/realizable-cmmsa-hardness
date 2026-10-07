import * as fs from 'node:fs/promises';
import { constants } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { S3Client, GetObjectCommand } from '@aws-sdk/client-s3';
import { fromIni } from '@aws-sdk/credential-providers';
import { validate, verifyChunk } from './archive.mjs';
import { defaults, DEST, SOURCE, hashBody } from './migrate.mjs';

export async function checkedTarget(root,relative) {
  const target=path.join(root,...relative.split('/'));let current=root;
  for(const part of relative.split('/')) {current=path.join(current,part);const s=await fs.lstat(current).catch(e=>{if(e.code==='ENOENT')return null;throw e;});if(s?.isSymbolicLink() || s && current!==target && !s.isDirectory())throw Error('Unsafe output ancestor');}
  return target;
}
export async function restore(o,client) {
  const c=JSON.parse(await fs.readFile(o.catalog,'utf8')),{chunks,members}=validate(c),member=members.get(o.path);
  if(!member || member.hardlink!=null || member.bytes>1048576)throw Error('Select one regular member of at most 1 MiB');
  if(![SOURCE,DEST].includes(c.bucket))throw Error('Unexpected bucket');
  const required=new Set([member.chunk]);let changed;
  do {changed=false;for(const m of members.values())if(required.has(m.chunk)&&m.hardlink!=null){const n=members.get(m.hardlink).chunk;if(!required.has(n)){required.add(n);changed=true;}}}while(changed);
  if(o.dryRun)return {mode:'dry-run',chunks:required.size,bytes:member.bytes,sha256:member.sha256};
  const root=await fs.realpath(o.workspaceRoot),stat=await fs.lstat(o.workspaceRoot);
  if(!stat.isDirectory()||stat.isSymbolicLink())throw Error('Output root must be a real directory');
  const target=await checkedTarget(root,member.path);
  if(await fs.lstat(target).catch(e=>{if(e.code==='ENOENT')return null;throw e;}))throw Error('Refusing existing output');
  const scratch=await fs.mkdtemp(path.join(root,'.qarc-restore-')),temp=path.join(scratch,'selected.pending'),key=await fs.readFile(o.keyFile??defaults.key),authenticated=new Set();
  const s3=client??new S3Client({region:'us-east-1',credentials:fromIni({profile:c.bucket===DEST?'quantyra':'cyint-ea-prod'}),maxAttempts:3});
  try {
    for(const chunk of [...chunks.values()].filter(c=>required.has(c.number)).sort((a,b)=>a.number-b.number)) {
      const r=await s3.send(new GetObjectCommand({Bucket:c.bucket,ExpectedBucketOwner:c.bucket===DEST?'063280428495':'485386182336',Key:chunk.key,VersionId:chunk.version_id}));
      await verifyChunk(r.Body,chunk,members,key,authenticated,chunk.number===member.chunk?{...member,temp}:undefined);
    }
    const check=await hashBody((await import('node:fs')).createReadStream(temp));if(check.bytes!==member.bytes||check.sha256!==member.sha256)throw Error('Restored bytes differ');
    await fs.mkdir(path.dirname(target),{recursive:true});await checkedTarget(root,member.path);
    await fs.copyFile(temp,target,constants.COPYFILE_EXCL);
    return {mode:'restored',chunks:required.size,bytes:check.bytes,sha256:check.sha256};
  } finally {
    key.fill(0);if(path.dirname(scratch)!==root || !(await fs.lstat(scratch)).isDirectory() || (await fs.lstat(scratch)).isSymbolicLink())throw Error('Unsafe scratch cleanup');await fs.rm(scratch,{recursive:true,force:true});
  }
}
function args(a) {
  const o={catalog:path.join(path.dirname(defaults.catalog),'research-archive-catalog.quantyra.json')},values={'--catalog':'catalog','--key-file':'keyFile','--workspace-root':'workspaceRoot','--path':'path'};
  for(let i=0;i<a.length;i++){if(a[i]==='--dry-run')o.dryRun=true;else if(values[a[i]]&&a[i+1]&&!a[i+1].startsWith('--'))o[values[a[i]]]=a[++i];else throw Error('Unknown option');}
  if(!o.workspaceRoot||!o.path)throw Error('Missing restore options');return o;
}
if(process.argv[1]&&path.resolve(process.argv[1])===fileURLToPath(import.meta.url))restore(args(process.argv.slice(2))).then(r=>console.log(JSON.stringify(r))).catch(()=>{console.error('Restore failed; no payload printed');process.exitCode=1;});
