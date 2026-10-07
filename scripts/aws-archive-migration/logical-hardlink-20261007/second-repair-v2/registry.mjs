import { sha } from '../../archive.mjs';
import { requireThat as check } from '../../custody.mjs';
const digest = x => sha(Buffer.from(JSON.stringify(x)));
// Compare every field, while tolerating JSON whitespace/key-order differences.
function canonical(x) {
  if (Array.isArray(x)) return x.map(canonical);
  if (x && typeof x === 'object') return Object.fromEntries(Object.keys(x).sort().map(k => [k, canonical(x[k])]));
  return x;
}
export function aliases(registry) {
  return [registry.core,...registry.recovery].map((e,i)=>({directory:i,catalog_file:e.catalog_file,catalog_sha256:e.catalog_sha256,source_catalog_sha256:e.source_catalog_sha256,selected_directory:e.selected_directory??null}));
}
export function validateRegistryEvidence(s) {
  check(typeof s.old_registry_utf8 === 'string' && sha(Buffer.from(s.old_registry_utf8)) === s.old_local_registry_sha256, 'accepted-registry-bytes-required');
  const old = JSON.parse(s.old_registry_utf8);
  check(!Object.hasOwn(old,'logical_hardlink_consumer') && old.status === 'verified-quantyra-archive-migration' && old.root_acceptance_commit === s.old_root_acceptance_commit && old.fullscope_packet_sha256 === s.old_packet_sha256, 'accepted-registry-root-mismatch');
  const vector = aliases(old);
  check(vector.length === 45 && s.catalogs.length === 45 && vector.every((e,i)=> (i===0 || old.recovery[i-1].directory===i) && /^[a-f0-9]{64}$/.test(e.source_catalog_sha256) && s.catalogs.filter(p=>p.directory===i && p.catalog_file===e.catalog_file && p.catalog_sha256===e.catalog_sha256).length===1), 'accepted-registry-catalog-mismatch');
  check(JSON.stringify(vector) === JSON.stringify(s.source_aliases) && digest(vector) === s.source_aliases_sha256, 'accepted-source-alias-vector-mismatch');
  return old;
}
export function successorRegistry(authorization) {
  const registry = validateRegistryEvidence(authorization.supplement);
  registry.logical_hardlink_consumer = {root_acceptance_commit:authorization.rootCommit,code_supplement_file:authorization.supplementFile,code_supplement_sha256:authorization.supplementHash};
  return registry;
}
export function authenticateRegistry(registry, authorization) {
  check(JSON.stringify(canonical(registry)) === JSON.stringify(canonical(successorRegistry(authorization))), 'installed-registry-body-changed');
}
