import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import zlib from 'node:zlib';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';

const here = path.dirname(fileURLToPath(import.meta.url));
const manifest = JSON.parse(fs.readFileSync(path.join(here, 'manifest.json'), 'utf8'));
const repo = path.resolve(here, '../../../..');
const sha = bytes => crypto.createHash('sha256').update(bytes).digest('hex');
const fail = message => { throw new Error(message); };
const check = (bytes, pin) => {
  if (bytes.length !== pin.bytes || sha(bytes) !== pin.sha256) fail(`Byte mismatch: ${pin.path}`);
};
const args = process.argv.slice(2);
if (args.length && !(args.length === 2 && args[0] === '--commit')) fail('Usage: verify-preservation.mjs [--commit COMMIT]');
const git = command => {
  const result = spawnSync('git', command, {
    cwd: repo, env: { ...process.env, GIT_OPTIONAL_LOCKS: '0' }, maxBuffer: 64 * 1024 * 1024,
  });
  if (result.status !== 0) fail(`Git read failed: ${result.stderr.toString()}`);
  return result.stdout;
};
for (const pin of manifest.original_scope_files) {
  check(fs.readFileSync(path.join(repo, pin.path)), pin);
  if (args.length) check(git(['cat-file', 'blob', `${args[1]}:${pin.path}`]), pin);
}
for (const pin of manifest.parent_snapshots) {
  check(fs.readFileSync(path.join(repo, pin.snapshot_path)), { ...pin, path: pin.snapshot_path });
}
const bundle = fs.readFileSync(path.join(repo, manifest.bundle.path));
check(bundle, manifest.bundle);
const tar = zlib.gunzipSync(bundle);
if (tar.length !== manifest.bundle.uncompressed_tar_bytes) fail('Tar size mismatch');
if (!zlib.gzipSync(tar, { level: 9, mtime: 0 }).equals(bundle)) fail('Deterministic gzip reconstruction mismatch');
const expected = new Map(manifest.bundle.members.map(member => [member.path, member]));
const field = bytes => bytes.toString('utf8').split('\0')[0];
let offset = 0, files = 0, directories = 0, payloadBytes = 0;
while (offset + 512 <= tar.length) {
  const header = tar.subarray(offset, offset + 512);
  if (header.every(byte => byte === 0)) {
    if (tar.subarray(offset).some(byte => byte !== 0)) fail('Unexpected data after tar terminator');
    break;
  }
  const checksum = parseInt(field(header.subarray(148, 156)).trim(), 8);
  const measured = header.reduce((sum, byte, index) => sum + (index >= 148 && index < 156 ? 32 : byte), 0);
  if (checksum !== measured) fail('Tar header checksum mismatch');
  const prefix = field(header.subarray(345, 500));
  const memberPath = (prefix ? `${prefix}/` : '') + field(header.subarray(0, 100));
  if (path.posix.isAbsolute(memberPath) || memberPath.split('/').includes('..')) fail('Unsafe bundle path');
  const member = expected.get(memberPath);
  if (!member) fail(`Unexpected or duplicate member: ${memberPath}`);
  expected.delete(memberPath);
  const size = parseInt(field(header.subarray(124, 136)), 8);
  if (size !== member.bytes) fail(`Tar size mismatch: ${memberPath}`);
  const type = String.fromCharCode(header[156]);
  if (member.type === 'directory') {
    if (type !== '5') fail('Directory type mismatch');
    if (!fs.statSync(path.join(repo, memberPath)).isDirectory()) fail(`Original directory missing: ${memberPath}`);
    directories++;
  } else {
    if (type !== '0') fail('File type mismatch');
    const bytes = tar.subarray(offset + 512, offset + 512 + size);
    check(bytes, member);
    check(fs.readFileSync(path.join(repo, memberPath)), member);
    files++;
    payloadBytes += size;
  }
  offset += 512 + Math.ceil(size / 512) * 512;
}
if (expected.size || files !== manifest.bundle.files || payloadBytes !== manifest.bundle.member_file_bytes) fail('Incomplete bundle coverage');
console.log(JSON.stringify({
  originalReceiptFiles: manifest.original_scope_files.length,
  originalReceiptBytes: manifest.original_scope_bytes,
  originalReceiptGitBlobsVerified: Boolean(args.length),
  archivedFixtureFiles: files, archivedFixtureDirectories: directories,
  archivedFixturePayloadBytes: payloadBytes, fixtureTrees: manifest.fixture_roots.length,
  deterministicBundleVerified: true, originalFilesAndEmbeddedGitBytesUnchanged: true,
  liveEligibility: 'HOLD',
}, null, 2));
