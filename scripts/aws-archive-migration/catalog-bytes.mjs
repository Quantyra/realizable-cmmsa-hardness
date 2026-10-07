// Hash stored bytes; canonical and member hashes refer to decoded JSON.
import {gzipSync,gunzipSync} from 'node:zlib';
import * as fs from 'node:fs/promises';
import path from 'node:path';
export function decodeCatalog(bytes){return JSON.parse(bytes[0]===31&&bytes[1]===139?gunzipSync(bytes,{maxOutputLength:96*1024**2}):bytes);}
export function encodeCatalog(c){return gzipSync(Buffer.from(JSON.stringify(c)),{level:6});}
export async function saveCompressedCatalog(file,c){const bytes=encodeCatalog(c);await fs.mkdir(path.dirname(file),{recursive:true});const old=await fs.readFile(file).catch(e=>{if(e.code==='ENOENT')return null;throw e;});if(old?.equals(bytes))return old;await fs.writeFile(file+'.tmp',bytes,{flag:'wx',mode:0o600});await fs.rename(file+'.tmp',file);return bytes;}
