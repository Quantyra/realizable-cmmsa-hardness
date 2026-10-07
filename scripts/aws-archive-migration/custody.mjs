// Fail closed on identity, evidence and activation boundaries. No AWS mutations.
import { sha,validate } from './archive.mjs';
export const digest=x=>sha(Buffer.from(JSON.stringify(x)));
export function requireThat(ok,reason){if(!ok){const e=Error(reason);e.safeReason=reason;throw e;}}
export const identity=x=>JSON.stringify([x.key,x.version]);
export const destinationIdentity=x=>JSON.stringify([x.key,x.destination_version??x.version]);
export function orderCandidates(row,candidates){return [...candidates].sort((a,b)=>row.is_latest?Number(b.is_latest)-Number(a.is_latest)||b.last_modified.localeCompare(a.last_modified):a.last_modified.localeCompare(b.last_modified));}
export function uniqueInventory(rows){const seen=new Set();for(const r of rows){requireThat(r.key&&r.version&&r.version!=='null','invalid-exact-source-identity');const id=identity(r);requireThat(!seen.has(id),'duplicate-inventory-identity');seen.add(id);}return seen;}
export function mappingCoverage(source,mapping,destination,retained=[]){
  const src=uniqueInventory(source),dst=uniqueInventory(destination),mapped=new Set(),used=new Set();
  for(const m of mapping){const a=identity(m),b=destinationIdentity(m);requireThat(src.has(a)&&!mapped.has(a),'duplicate-or-foreign-source-mapping');requireThat(!used.has(b),'non-injective-destination-mapping');requireThat(m.verified&&/^[a-f0-9]{64}$/.test(m.sha256),'unverified-mapping');const r=source.find(x=>identity(x)===a),d=destination.find(x=>identity(x)===b);requireThat(d&&r.kind===d.kind&&r.bytes===d.bytes&&m.bytes===r.bytes&&(!r.is_latest||d.is_latest),'mapped-inventory-mismatch');mapped.add(a);used.add(b);}
  requireThat(mapped.size===src.size,'incomplete-source-coverage');
  for(const r of retained){const id=identity(r);requireThat(!used.has(id)&&dst.has(id)&&r.retained===true&&r.reason==='interrupted-copy-duplicate'&&/^[a-f0-9]{64}$/.test(r.sha256)&&r.verified===true,'invalid-retained-version');const m=mapping.find(x=>identity(x)===r.source_identity);requireThat(m&&m.key===r.key&&m.sha256===r.sha256&&m.bytes===r.bytes,'retained-version-unbound');used.add(id);}
  requireThat(used.size===dst.size&&[...dst].every(x=>used.has(x)),'unaccounted-destination-version');return true;
}
export function authenticatedCatalog(c,rawHash,r){
  validate(c);requireThat(r.complete===true&&r.bucket===c.bucket&&r.catalog_sha256===rawHash&&r.catalog_canonical_sha256===digest(c)&&r.member_catalog_sha256===digest(c.members)&&r.members===c.members.length&&r.chunks.length===c.chunks.length,'catalog-evidence-mismatch');
  const ids=new Set();for(const x of c.chunks){const id=JSON.stringify([x.key,x.version_id]);requireThat(!ids.has(id),'duplicate-catalog-object');ids.add(id);const a=r.chunks.filter(y=>y.key===x.key&&y.version_id===x.version_id);requireThat(a.length===1&&a[0].authenticated===true&&a[0].bytes===x.bytes&&a[0].ciphertext_sha256===x.sha256&&a[0].tar_sha256===x.tar_sha256,'chunk-evidence-mismatch');}return true;
}
export function acceptActivation(packet,packetHash,acceptance,catalogPins,independentHash){
  requireThat(packet.type==='archive-author-fullscope-v1'&&packet.complete===true&&packet.versions===205&&packet.core_chunks===51&&packet.recovery_unique_chunks===54&&packet.recovery_catalogs===44&&packet.restore?.verified===true&&packet.bridge?.absent===true,'fullscope-not-complete');
  requireThat(acceptance?.type==='archive-root-acceptance-v1'&&acceptance.decision==='ACCEPT'&&acceptance.reviewer_role==='root-independent-verifier'&&acceptance.author_proof_is_not_independent===true&&acceptance.packet_sha256===packetHash&&acceptance.independent_verification_sha256===independentHash&&/^[a-f0-9]{64}$/.test(independentHash)&&acceptance.independent_verification_sha256!==packetHash,'root-acceptance-required');
  requireThat(digest(packet.catalogs)===digest(catalogPins)&&digest(acceptance.catalogs)===digest(catalogPins)&&catalogPins.length===45,'accepted-catalog-pins-mismatch');return true;
}
export async function reconcileVersion({row,candidates,copy,verify,intent,result}){
  // Intent is durable before CopyObject. A lost reply leaves candidates for the
  // next invocation; each source identity still claims its own exact version.
  for(const c of candidates){const proof=await verify(c.version);if(proof)return {version:c.version,proof,reconciled:true};}
  await intent();const version=await copy();requireThat(version&&version!=='null','copy-exact-version-missing');await result(version);const proof=await verify(version);requireThat(proof,'copy-verification-failed');return {version,proof,reconciled:false};
}
export async function removeBridgeSafely({get,remove,expected,same}){
  const before=await get();if(before!==null){requireThat(same(before,expected),'policy-changed-do-not-remove');await remove();}
  requireThat(await get()===null,'bridge-removal-readback-failed');return {absent:true,removed:before!==null,already_absent:before===null,expected_policy_sha256:digest(expected)};
}
export function stableInventories(beforeSource,afterSource,beforeDestination,afterDestination){requireThat(digest(beforeSource)===digest(afterSource),'source-inventory-unstable');requireThat(digest(beforeDestination)===digest(afterDestination),'destination-inventory-unstable');return true;}
