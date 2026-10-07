import * as fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { execFile } from 'node:child_process';
import { promisify } from 'node:util';
import { sha } from '../archive.mjs';
import { defaults } from '../migrate.mjs';
import { requireThat as check } from '../custody.mjs';
export const parent = 'C:/Users/dfred/Desktop/Projects/IGH/Quantyra-Planning';
export const here = path.dirname(fileURLToPath(import.meta.url));
export const repo = path.resolve(here, '../../..');
export const codeNames = ['restore.mjs','verify-chunk.mjs','authorization.mjs','active-restore.mjs','wrappers.mjs','install-local-restore.mjs','prepare-supplement.mjs','test.mjs','README.md','.gitattributes'];
export const acceptanceName = 'archive-recovery-hardlink-acceptance.json';
export const reviewName = 'archive-recovery-hardlink-independent-verification.json';
const git = promisify(execFile);
export async function committed(commit, name) {
  check(/^[a-f0-9]{40}$/.test(commit), 'committed-root-required');
  return (await git('git', ['show', commit + ':docs/aws-migration-2026-10-06/' + name], { cwd: parent, windowsHide: true, encoding: 'buffer', maxBuffer: 16 * 1024 ** 2 })).stdout;
}
export function authorize(s, a, r, supplementHash, reviewHash) {
  check(s.type === 'archive-logical-hardlink-code-supplement-v1' && s.fresh_archive_authentication === false && s.data_versions_unchanged === true, 'code-only-supplement-required');
  check(/^[a-f0-9]{40}$/.test(s.code_commit), 'successor-commit-required');
  check(a.type === 'archive-logical-hardlink-root-acceptance-v1' && a.decision === 'ACCEPT' && a.reviewer_role === 'root-independent-verifier' && a.author_proof_is_not_independent === true, 'new-root-acceptance-required');
  check(a.code_supplement_sha256 === supplementHash && a.independent_verification_sha256 === reviewHash && supplementHash !== reviewHash, 'new-independent-binding-required');
  check(r.type === 'archive-logical-hardlink-independent-verification-v1' && r.complete === true && r.reviewer_role === 'independent-code-verifier' && ['GO','GO-WITH-BOUNDARIES'].includes(r.verdict), 'independent-code-review-required');
  for (const x of [a, r]) check(x.old_packet_sha256 === s.old_packet_sha256 && x.code_commit === s.code_commit && x.code_supplement_sha256 === supplementHash, 'supplement-scope-mismatch');
  check(a.old_root_acceptance_commit === s.old_root_acceptance_commit && s.old_root_acceptance_commit === '6bdf7532fb020397a5cf60c0bf7cc2afccb4cbac', 'old-acceptance-binding-required');
}
export function authorizeRoute(pin, entry, c, requested, isCore) {
  if (pin.directory > 0) {
    const directory = c.selected_directory?.replace(/^realizable-cmmsa-hardness\//,'');
    const paths = requested == null ? [] : Array.isArray(requested) ? requested : [requested];
    const prefix = 'realizable-cmmsa-hardness/'+directory;
    check(!isCore && entry.directory === pin.directory && entry.selected_directory === directory && paths.every(p=>p.replace(/\/$/,'')===prefix||p.startsWith(prefix+'/')), 'outside-recovery-directory');
  } else check(pin.directory === 0 && isCore, 'core-routing-mismatch');
}
export async function loadAuthorization(commit, supplementFile) {
  const acceptanceBytes = await committed(commit, acceptanceName), a = JSON.parse(acceptanceBytes);
  const file = supplementFile ?? a.code_supplement_file, bytes = await fs.readFile(file), s = JSON.parse(bytes);
  const reviewBytes = await committed(commit, reviewName), r = JSON.parse(reviewBytes);
  authorize(s, a, r, sha(bytes), sha(reviewBytes));
  const oldAcceptanceBytes = await committed(s.old_root_acceptance_commit, 'archive-root-acceptance.json');
  check(sha(oldAcceptanceBytes) === s.old_root_acceptance_sha256 && JSON.stringify(JSON.parse(oldAcceptanceBytes).catalogs) === JSON.stringify(s.catalogs), 'old-root-bytes-changed');
  const packetBytes = await fs.readFile(path.join(defaults.state, 'repair/fullscope-packet.json')), packet = JSON.parse(packetBytes);
  check(sha(packetBytes) === s.old_packet_sha256 && JSON.stringify(packet.artifacts) === JSON.stringify(s.old_artifacts) && packet.artifacts.length === 305, 'old-packet-changed');
  for (const p of packet.artifacts) check(sha(await fs.readFile(p.file)) === p.sha256, 'old-artifact-changed');
  check(s.code_files.length === codeNames.length, 'successor-code-set-required');
  for (const name of codeNames) {
    const file = path.join(here, name), pins = s.code_files.filter(p => path.resolve(p.file) === file);
    check(pins.length === 1, 'successor-code-pin-missing');
    const p = pins[0];
    check(p.git_path === path.relative(repo, file).replaceAll('\\', '/') && sha(await fs.readFile(file)) === p.sha256, 'successor-code-changed');
    const blob = (await git('git', ['show', s.code_commit + ':' + p.git_path], { cwd: repo, windowsHide: true, encoding: 'buffer', maxBuffer: 2 * 1024 ** 2 })).stdout;
    check(sha(blob) === p.sha256, 'successor-code-commit-mismatch');
  }
  return { supplement: s, supplementFile: file, supplementHash: sha(bytes), rootCommit: commit, acceptanceHash: sha(acceptanceBytes) };
}
