"""Static, Git-verified import inventory; not compiler/proof-closure evidence."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

REPO = Path('C:/Users/dfred/.quantyra/upstream/openai-math-adc7f124-20261008')
PIN = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'
ROOTS = ['OAI.Computability.UniqueGames.Inverse.' + name for name in
         ['ShortcodeTheorem', 'KMSLowLevelLemmas', 'KMSFourthMomentMixedEnergyLemmas']]


def strip_comments(text):
    result, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-': depth += 1; i += 2; continue
            if pair == '-/': depth -= 1; i += 2; continue
            result.append('\n' if text[i] == '\n' else ' '); i += 1; continue
        if not string and pair == '/-': depth = 1; i += 2; continue
        if not string and pair == '--':
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
            continue
        if string and text[i] == '\\':
            result.extend(text[i:i+2]); i += 2; continue
        if text[i] == '"': string = not string
        result.append(text[i]); i += 1
    if depth: raise ValueError('Unterminated comment')
    return ''.join(result)


def main():
    def git(*args):
        return subprocess.check_output(['git', '-C', str(REPO), *args])
    if git('rev-parse', 'HEAD').decode().strip() != PIN or git('status', '--porcelain'):
        raise ValueError('Upstream checkout changed')
    blobs = {}
    for entry in git('ls-tree', '-r', '-z', 'HEAD', 'lean').split(b'\0'):
        if entry:
            meta, path = entry.split(b'\t', 1)
            blobs[path.decode()] = meta.split()[2].decode()
    def read(path):
        data = (REPO/path).read_bytes()
        actual = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if actual != blobs[path]: raise ValueError('Tracked blob mismatch: '+path)
        return data
    pending, sources, external = list(ROOTS), {}, set()
    while pending:
        module = pending.pop()
        if module in sources: continue
        path = 'lean/'+module.replace('.', '/')+'.lean'
        if path not in blobs:
            if module.startswith('OAI.'):
                raise ValueError('Missing internal import: '+module)
            external.add(module); continue
        data = read(path)
        clean = strip_comments(data.decode('utf-8'))
        imports = []
        for line in clean.splitlines():
            matched = re.fullmatch(r'\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*', line)
            if matched:
                names = matched[1].split()
                if not all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', n) for n in names):
                    raise ValueError('Import syntax needs explicit parser extension: '+path)
                imports.extend(names)
        sources[module] = {'path': path, 'git_blob': blobs[path], 'sha256': hashlib.sha256(data).hexdigest().upper(), 'bytes': len(data), 'imports': imports}
        pending.extend(imports)
    configs = {}
    for path in sorted(p for p in blobs if p.startswith('lean/patches/') or p in ['lean/lean-toolchain', 'lean/lakefile.lean', 'lean/lake-manifest.json']):
        data = read(path)
        configs[path] = {'sha256': hashlib.sha256(data).hexdigest().upper(), 'bytes': len(data), 'git_blob': blobs[path]}
    output = {'schema': 'upstream-selected-static-import-inventory-v1', 'commit': PIN,
              'roots': ROOTS, 'sources': sources, 'source_count': len(sources),
              'source_bytes': sum(r['bytes'] for r in sources.values()),
              'external_imports': sorted(external), 'configs_and_patches': configs,
              'compiler_executed': False, 'kernel_closure_verified': False,
              'axiom_profiles_verified': False, 'consumer_bridges_proved': False,
              'accepted': False, 'scope': 'Static import inventory and exact Git blob identities only. Package resolution, original compatibility-patch application, compiler identity and GCP native verification remain pending.'}
    dest = Path(__file__).with_name('upstream-selected-static-import-inventory.json')
    with dest.open('x', encoding='utf-8') as stream:
        json.dump(output, stream, indent=2); stream.write('\n')
    print(json.dumps({'sources': len(sources), 'source_bytes': output['source_bytes'], 'external_imports': len(external), 'configs_and_patches': len(configs)}))


if __name__ == '__main__': main()
