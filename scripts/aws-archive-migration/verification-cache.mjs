import { createHash } from 'node:crypto';
import { GetObjectCommand } from '@aws-sdk/client-s3';
import { validate,verifyChunk,sha } from './archive.mjs';
import { save,SOURCE,DEST } from './migrate.mjs';
import * as fs from 'node:fs/promises';
import path from 'node:path';

export function memberSignature(chunk,members) {
  const rows=[...members.values()].filter(m=>m.chunk===chunk.number).sort((a,b)=>a.path<b.path?-1:a.path>b.path?1:0),h=createHash('sha256');
  for(const m of rows)h.update(JSON.stringify([m.path,m.bytes,m.sha256,m.hardlink??null])+'\n');
  return {sha256:h.digest('hex'),rows};
}
export const cacheKey=(c,x,sig)=>JSON.stringify([c.bucket,x.key,x.version_id,x.bytes,x.sha256,x.tar_sha256,sig]);
// Cached evidence is usable only for the same immutable destination object
// version and the complete expected member/type/link/hash vector.
export async function verifyCached(client,c,keyFile,state,cache,cacheFile) {
  if(![SOURCE,DEST].includes(c.bucket))throw Error('Unexpected cached bucket');
  const {chunks,members}=validate(c),key=await fs.readFile(keyFile),authenticated=new Set(),results=[];let reused=0,streamed=0;
  try {
    for(const chunk of [...chunks.values()].sort((a,b)=>a.number-b.number)) {
      const sig=memberSignature(chunk,members),id=cacheKey(c,chunk,sig.sha256),prior=cache.get(id);let result;
      if(prior) {
        if(!prior.authenticated||prior.ciphertext_sha256!==chunk.sha256||prior.tar_sha256!==chunk.tar_sha256||prior.member_signature!==sig.sha256||prior.members!==sig.rows.length)throw Error('Invalid cached authentication');
        for(const m of sig.rows)if(m.hardlink!=null&&members.get(m.hardlink).chunk<chunk.number&&!authenticated.has(m.hardlink))throw Error('Cached dependency not authenticated');
        for(const m of sig.rows)authenticated.add(m.path);
        result={...prior,number:chunk.number,reused:true};reused++;
      } else {
        const r=await client.send(new GetObjectCommand({Bucket:c.bucket,ExpectedBucketOwner:c.bucket===DEST?'063280428495':c.bucket===SOURCE?'485386182336':undefined,Key:chunk.key,VersionId:chunk.version_id}));
        result={...await verifyChunk(r.Body,chunk,members,key,authenticated),key:chunk.key,version_id:chunk.version_id,member_signature:sig.sha256,reused:false};
        cache.set(id,result);streamed++;
        if(cacheFile)await save(cacheFile,{type:'immutable-chunk-authentication-cache-v1',entries:[...cache.entries()]});
      }
      results.push(result);
      await save(path.join(state,'verification-progress.json'),{complete:false,completed:results,reused_chunks:reused,streamed_chunks:streamed});
    }
    if(authenticated.size!==members.size)throw Error('Incomplete cached member coverage');
    const receipt={bucket:c.bucket,catalog_canonical_sha256:sha(Buffer.from(JSON.stringify(c))),member_catalog_sha256:sha(Buffer.from(JSON.stringify(c.members))),chunks:results,members:members.size,complete:true,reused_chunks:reused,streamed_chunks:streamed};
    await save(path.join(state,'verification.json'),receipt);return receipt;
  } finally {key.fill(0);}
}
