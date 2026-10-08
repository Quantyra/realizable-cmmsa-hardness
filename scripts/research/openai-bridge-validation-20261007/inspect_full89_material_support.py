"""Conservative static source context for a future same-material export build."""
import hashlib
import json
from pathlib import Path
import re
import tarfile

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full89-resource02')
BASE = ROOT/'consumption-v2/qualification'
REL = 'lean/PvNP/RealizableHardness/ActualSelectedComplementHC46OriginalApplication.lean'


def sha(data):
    return hashlib.sha256(data).hexdigest().upper()


def main():
    binding = json.loads((ROOT/'resource-binding.json').read_bytes())
    archive_bytes = (ROOT/'input-archive.tar.gz').read_bytes()
    if sha(archive_bytes) != binding['files']['input-archive.tar.gz'].upper():
        raise ValueError('Full89 frozen archive changed')
    with tarfile.open(ROOT/'input-archive.tar.gz', 'r:gz') as archive:
        manifest = json.loads(archive.extractfile('capture-manifest.json').read())
        sources = {path: archive.extractfile(path).read() for path in manifest['project_sources']}
    if len(sources) != 319:
        raise ValueError('Full89 source scope changed')
    for path, data in sources.items():
        pin = manifest['project_sources'][path]
        if sha(data) != pin['sha256'].upper() or ('bytes' in pin and len(data) != pin['bytes']):
            raise ValueError('Full89 source identity mismatch')
    index_bytes = (BASE/'review-sources/source-index.json').read_bytes()
    reviewed = {r['path'] for r in json.loads(index_bytes)['project_bodies']}
    candidate_folder = BASE/'material-consumer-candidate-v1'
    candidate_bytes = (candidate_folder/'ActualSelectedComplementHC46OriginalApplication.lean').read_bytes()
    candidate_receipt = json.loads((candidate_folder/'derivation.json').read_bytes())
    if sha(candidate_bytes) != candidate_receipt['candidate_sha256'] or sha(sources[REL]) != candidate_receipt['parent_application_sha256']:
        raise ValueError('Material candidate derivation changed')
    project_modules = {path.removeprefix('lean/').removesuffix('.lean').replace('/', '.'): path for path in sources}
    queued = [REL]
    visited = {}
    external = set()
    while queued:
        path = queued.pop()
        if path in visited:
            continue
        data = candidate_bytes if path == REL else sources[path]
        imports = []
        for match in re.finditer(r'^import\s+([^\r\n]+)', data.decode('utf-8'), re.MULTILINE):
            imports.extend(match.group(1).split('--', 1)[0].split())
        for module in imports:
            if module.startswith('PvNP.'):
                if module not in project_modules:
                    raise ValueError('Uncaptured project import: '+module)
                queued.append(project_modules[module])
            else:
                external.add(module)
        visited[path] = {'path': path, 'sha256': sha(data), 'bytes': len(data), 'direct_imports': imports,
                         'existing_170_body_review_member': path in reviewed,
                         'candidate_modified_body': path == REL}
    missing = sorted(path for path in visited if path not in reviewed)
    receipt = {'schema': 'full89-material-candidate-static-import-context-v1',
               'frozen_archive_sha256': sha(archive_bytes), 'source_index_sha256': sha(index_bytes),
               'candidate_sha256': sha(candidate_bytes), 'project_source_count': len(visited),
               'project_source_bytes': sum(r['bytes'] for r in visited.values()),
               'sources': [visited[path] for path in sorted(visited)],
               'additional_context_outside_prior_170_body_selection': missing,
               'additional_context_count': len(missing), 'external_imports': sorted(external),
               'static_import_context_only': True, 'actual_constant_consumption_pending': True,
               'new_native_profile_pending': True, 'new_review_scope_pending': True,
               'all_existing_sources_pinned_in_319_native_closure': True,
               'all_module_declarations_standard_axioms_claimed': False,
               'frozen_capture_modified': False, 'local_compilation': False,
               'launch_clearance': False, 'accepted': False}
    destination = Path(__file__).with_name('full89-material-static-import-context.json')
    with destination.open('x', encoding='utf-8') as output:
        json.dump(receipt, output, indent=2); output.write('\n')
    print(json.dumps({'project_source_count': len(visited), 'additional_context_count': len(missing),
                      'project_source_bytes': receipt['project_source_bytes'], 'actual_consumption_pending': True}))


if __name__ == '__main__':
    main()
