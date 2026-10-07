import { createHash, createDecipheriv } from 'node:crypto';
import { Transform } from 'node:stream';
import { pipeline } from 'node:stream/promises';
import { createGunzip } from 'node:zlib';
import { createWriteStream } from 'node:fs';
import * as fs from 'node:fs/promises';
import path from 'node:path';
import tar from 'tar-stream';

export const sha = b => createHash('sha256').update(b).digest('hex');
const check = (ok, message) => { if (!ok) throw Error(message); };
export function safePath(p) {
  check(typeof p === 'string' && /^(realizable-cmmsa-hardness|codex-history\/sessions|archive)\//.test(p) &&
    !/[\\:\x00-\x1f]/.test(p) && p.split('/').every(x => x && x !== '.' && x !== '..' && !/[. ]$/.test(x) && !/^(con|prn|aux|nul|com[1-9]|lpt[1-9])(?:\.|$)/i.test(x)), 'Unsafe member path');
  return p;
}
export function validate(c) {
  check(c && Array.isArray(c.chunks) && c.chunks.length && Array.isArray(c.members) && c.members.length, 'Invalid catalog');
  const chunks = new Map(), members = new Map(), folded = new Set();
  for (const x of c.chunks) {
    check(Number.isSafeInteger(x.number) && x.number > 0 && !chunks.has(x.number) && typeof x.key === 'string' && x.key && typeof x.version_id === 'string' && x.version_id && Number.isSafeInteger(x.bytes) && x.bytes >= 33 && /^[a-f0-9]{64}$/.test(x.sha256) && /^[a-f0-9]{64}$/.test(x.tar_sha256), 'Invalid chunk'); chunks.set(x.number,x);
  }
  for (const m of c.members) {
    safePath(m.path); check(!folded.has(m.path.toLowerCase()) && chunks.has(m.chunk) && Number.isSafeInteger(m.bytes) && m.bytes >= 0 && /^[a-f0-9]{64}$/.test(m.sha256), 'Invalid member');
    members.set(m.path,m); folded.add(m.path.toLowerCase());
  }
  for (const m of members.values()) {
    for (let p=path.posix.dirname(m.path);p!=='.';p=path.posix.dirname(p)) check(!folded.has(p.toLowerCase()),'Ancestor collision');
    let t=m; const seen=new Set();
    while(t.hardlink != null) { check(!seen.has(t.path),'Cyclic hardlink'); seen.add(t.path); safePath(t.hardlink); const next=members.get(t.hardlink); check(next && next.chunk<=t.chunk && next.bytes===t.bytes && next.sha256===t.sha256,'Invalid hardlink'); t=next; }
  }
  return {chunks,members};
}
export class HashStream extends Transform {
  constructor() { super(); this.hash=createHash('sha256'); this.bytes=0; }
  _transform(data,enc,cb) { this.hash.update(data); this.bytes+=data.length; cb(null,data); }
  result() { return {bytes:this.bytes,sha256:this.hash.digest('hex')}; }
}
// Keep the final 16 bytes for the GCM tag. Plaintext only goes to hashes or
// private staging; selected bytes become visible only after pipeline success.
export class Decrypt extends Transform {
  constructor(key) { super(); check(key.length===32,'Invalid key length'); this.key=key; this.pending=Buffer.alloc(0); }
  _transform(data,enc,cb) {
    try {
      this.pending=Buffer.concat([this.pending,data]);
      if(!this.decipher && this.pending.length>=17) { check(this.pending.subarray(0,5).toString()==='QARC1','Invalid envelope'); this.decipher=createDecipheriv('aes-256-gcm',this.key,this.pending.subarray(5,17)); this.pending=this.pending.subarray(17); }
      if(this.decipher && this.pending.length>16) { this.push(this.decipher.update(this.pending.subarray(0,-16))); this.pending=this.pending.subarray(-16); }
      cb();
    } catch { cb(Error('Envelope decryption failed')); }
  }
  _flush(cb) { try { check(this.decipher && this.pending.length===16,'Truncated envelope'); this.decipher.setAuthTag(this.pending); this.push(this.decipher.final()); cb(); } catch { cb(Error('Archive authentication failed')); } }
}
export async function verifyChunk(body,chunk,members,key,authenticated,selection) {
  const cipher=new HashStream(), compressed=new HashStream(), extract=tar.extract(), seen=new Set(), verified=[];
  let selected=false, selectedTemp;
  if(selection) { check(selection.bytes<=1048576,'Restore exceeds 1 MiB bound'); selectedTemp=selection.temp; }
  extract.on('entry',(h,stream,next)=>{
    (async()=>{
      if(h.type==='directory') { const n=h.name.replace(/\/$/,''); if(!['realizable-cmmsa-hardness','codex-history','codex-history/sessions','archive'].includes(n)) safePath(n+'/_dir'); check(h.size===0,'Invalid directory'); stream.resume(); return; }
      safePath(h.name); const m=members.get(h.name);
      check(m && m.chunk===chunk.number && !seen.has(h.name),'Unexpected member'); seen.add(h.name);
      if(h.type==='link') {
        check(m.hardlink===h.linkname && authenticated.has(h.linkname) && h.size===0,'Unverified hardlink'); stream.resume();
        check(selection?.path!==m.path,'Select a regular member for bounded restore');
      } else {
        check(h.type==='file' && m.hardlink==null && h.size===m.bytes,'Member metadata mismatch');
        const hash=createHash('sha256'); let bytes=0;
        if(selection?.path===m.path) {
          const meter=new Transform({transform(d,e,cb){hash.update(d);bytes+=d.length;cb(null,d);}});
          await pipeline(stream,meter,createWriteStream(selectedTemp,{flags:'wx',mode:0o600})); selected=true;
        } else for await(const d of stream) { hash.update(d); bytes+=d.length; }
        check(bytes===m.bytes && hash.digest('hex')===m.sha256,'Member hash mismatch');
      }
      authenticated.add(m.path); verified.push(m.path);
    })().then(()=>next(),e=>extract.destroy(e));
  });
  try {
    await pipeline(body,cipher,new Decrypt(key),compressed,createGunzip(),extract);
    const a=cipher.result(),b=compressed.result();
    check(a.bytes===chunk.bytes && a.sha256===chunk.sha256 && b.sha256===chunk.tar_sha256,'Chunk hash mismatch');
    const expected=[...members.values()].filter(m=>m.chunk===chunk.number).length;
    check(seen.size===expected,'Missing member');
    if(selection?.chunk===chunk.number) check(selected,'Selected restore missing');
    return {number:chunk.number,ciphertext_sha256:a.sha256,tar_sha256:b.sha256,bytes:a.bytes,members:seen.size,authenticated:true};
  } catch(e) { for(const p of verified) authenticated.delete(p); if(selectedTemp) await fs.rm(selectedTemp,{force:true}); throw e; }
}
