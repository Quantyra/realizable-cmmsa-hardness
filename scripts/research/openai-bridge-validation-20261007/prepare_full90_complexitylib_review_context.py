"""Recover complete public-import context for newly reached Complexitylib boundaries."""
import hashlib
import io
import json
from pathlib import Path
import re
import tarfile

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full90-material-resource02')
BASE = ROOT/'consumption-v1/qualification'


def main():
    source_index = json.loads((BASE/'review-sources/source-index.json').read_bytes())
    marker = json.loads((ROOT/'launch-once.json').read_bytes())
    custody = json.loads((Path(marker['preflight'])/'terminal-custody.json').read_bytes())['custody']
    native_path = Path(custody['repository_path'])
    if hashlib.sha256(native_path.read_bytes()).hexdigest().upper() != custody['remote_sha256']:
        raise ValueError('Native source custody changed')
    output = BASE/'complexitylib-review-context-v1'; output.mkdir()
    with tarfile.open(native_path) as native:
        pins = json.load(native.extractfile('package-source-hashes.json'))
        revisions = json.load(native.extractfile('package-identities.json'))
        package_archive = tarfile.open(fileobj=io.BytesIO(native.extractfile('package-sources.tar.gz').read()))
        pending = list(source_index['additional_boundary_review_modules'])
        rows, external_imports = {}, set()
        while pending:
            module = pending.pop()
            if module in rows: continue
            relative = module.replace('.', '/')+'.lean'
            source_path = '.lake/packages/complexitylib/'+relative
            data = package_archive.extractfile(source_path).read()
            if hashlib.sha256(data).hexdigest().upper() != pins[source_path]:
                raise ValueError('Complexitylib source pin mismatch')
            imports = []
            for match in re.finditer(r'^\s*(?:(?:public|private)\s+)?import\s+([^\r\n]+)',data.decode('utf-8'),re.MULTILINE):
                imports.extend(match.group(1).split('--',1)[0].split())
            for name in imports:
                if name.startswith('Complexitylib.'): pending.append(name)
                else: external_imports.add(name)
            destination = output/'external'/relative
            destination.parent.mkdir(parents=True,exist_ok=True); destination.write_bytes(data)
            rows[module] = {'module':module,'path':'external/'+relative,'native_source_path':source_path,
                            'sha256':pins[source_path],'bytes':len(data),'direct_imports':imports,
                            'direct_native_boundary_module':module in source_index['additional_boundary_review_modules'],
                            'complete_source':True,'independent_review_required':True}
    result = {'schema':'full90-complete-Complexitylib-public-import-review-context-v1',
              'source_index_sha256':hashlib.sha256((BASE/'review-sources/source-index.json').read_bytes()).hexdigest().upper(),
              'native_custody_sha256':custody['remote_sha256'],'package_revision':revisions['complexitylib'],
              'complete_sources':[rows[name] for name in sorted(rows)],'complete_source_count':len(rows),
              'complete_source_bytes':sum(row['bytes'] for row in rows.values()),'external_imports':sorted(external_imports),
              'public_and_private_imports_recognized':True,'independent_review_complete':False,
              'accepted':False,'full_goal_complete':False}
    (output/'source-index.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'Complexitylib_complete_sources':len(rows),'bytes':result['complete_source_bytes'],
                      'external_imports':len(external_imports)}))


if __name__ == '__main__': main()
