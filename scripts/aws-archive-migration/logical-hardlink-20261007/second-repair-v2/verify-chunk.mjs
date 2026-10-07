// Multi-selection extension of the unchanged, old packet-pinned QARC verifier.
import {createHash} from 'node:crypto';
import {Transform} from 'node:stream';
import {pipeline} from 'node:stream/promises';
import {createGunzip} from 'node:zlib';
import {createWriteStream} from 'node:fs';
import * as fs from 'node:fs/promises';
import tar from 'tar-stream';
import {HashStream,Decrypt,safePath} from '../../archive.mjs';
const check=(ok,s)=>{if(!ok)throw Error(s);};
export async function verifyChunk(body,chunk,members,key,authenticated,stages) {
  const cipher=new HashStream(),compressed=new HashStream(),extract=tar.extract(),seen=new Set(),verified=[],selected=new Set(),created=[];
  extract.on('entry',(h,stream,next)=>{
    (async()=>{
      if(h.type==='directory'){const n=h.name.replace(/\/$/,'');if(!['realizable-cmmsa-hardness','codex-history','codex-history/sessions','archive'].includes(n))safePath(n+'/_dir');check(h.size===0,'Invalid directory');stream.resume();return;}
      safePath(h.name);const m=members.get(h.name);check(m&&m.chunk===chunk.number&&!seen.has(h.name),'Unexpected member');seen.add(h.name);
      if(h.type==='link'){check(m.hardlink===h.linkname&&authenticated.has(h.linkname)&&h.size===0,'Unverified hardlink');stream.resume();check(!stages.has(m.path),'Stage must be regular content');}
      else {
        check(h.type==='file'&&m.hardlink==null&&h.size===m.bytes,'Member metadata mismatch');const hash=createHash('sha256');let bytes=0;
        if(stages.has(m.path)){const temp=stages.get(m.path);created.push(temp);const meter=new Transform({transform(d,e,cb){hash.update(d);bytes+=d.length;cb(null,d);}});await pipeline(stream,meter,createWriteStream(temp,{flags:'wx',mode:0o600}));selected.add(m.path);}
        else for await(const d of stream){hash.update(d);bytes+=d.length;}
        check(bytes===m.bytes&&hash.digest('hex')===m.sha256,'Member hash mismatch');
      }
      authenticated.add(m.path);verified.push(m.path);
    })().then(()=>next(),e=>extract.destroy(e));
  });
  try {
    await pipeline(body,cipher,new Decrypt(key),compressed,createGunzip(),extract);const a=cipher.result(),b=compressed.result();
    check(a.bytes===chunk.bytes&&a.sha256===chunk.sha256&&b.sha256===chunk.tar_sha256,'Chunk hash mismatch');
    check(seen.size===[...members.values()].filter(m=>m.chunk===chunk.number).length,'Missing member');
    for(const name of stages.keys())if(members.get(name).chunk===chunk.number)check(selected.has(name),'Selected restore missing');
    return {number:chunk.number,ciphertext_sha256:a.sha256,tar_sha256:b.sha256,bytes:a.bytes,members:seen.size,authenticated:true};
  } catch(e){for(const name of verified)authenticated.delete(name);for(const file of created)await fs.rm(file,{force:true});throw e;}
}
