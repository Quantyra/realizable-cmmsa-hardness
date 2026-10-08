"""Freeze recovered consumption tooling against Full88; never invoke Lean."""
import io
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest
from full88_controller import ROOT, validate_successor
from prepare_builder02 import sha

PROBE = Path('C:/Users/dfred/.quantyra/resume-workspaces/full81/realizable-cmmsa-hardness/docs/a8-gcp/r1007/retry-70b/metadata-probe-preparation-v2')
PROBE_SHA = '42D57E4E1C8F0B3B638BCD7CA5120D5155307F2DB3AF8608BBEB21AAE7D54FC0'

def main():
    validate_successor()
    manifest = json.loads((ROOT/'capture-manifest.json').read_bytes())
    files = {name: (PROBE/name).read_bytes() for name in ('probe.lean', 'postprocess.py', 'preparation-status.json')}
    if sha(files['probe.lean']) != PROBE_SHA:
        raise RuntimeError('Recovered probe identity changed')
    source = files['probe.lean'].decode('utf-8')
    modules = json.loads(re.search(r'private def projectModules : List String := (\[.*?\])', source).group(1))
    roots = json.loads(re.search(r'private def roots : List String := (\[.*?\])', source).group(1))
    expected = {rel.removeprefix('lean/').removesuffix('.lean').replace('/', '.') for rel in manifest['project_sources']}
    spec = json.loads(files['preparation-status.json'])
    if len(modules) != 319 or set(modules) != expected:
        raise RuntimeError('Probe project-module scope differs')
    if len(roots) != 172 or len(set(roots)) != 172 or set(roots) != set(manifest['requested_axioms']) or roots != spec['roots']:
        raise RuntimeError('Probe request scope differs')
    if 'allowOpaque := true' not in source or 'getModuleIdxFor?' not in source:
        raise RuntimeError('Required body/ownership API absent')
    output = ROOT/'consumption-preparation'
    output.mkdir(exist_ok=False)
    with tarfile.open(output/'tooling.tar.gz', 'w:gz') as archive:
        for name, data in sorted(files.items()):
            member = tarfile.TarInfo(name)
            member.size = len(data)
            member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    receipt = dict(resource=ROOT.name, capture_manifest_sha256=digest(ROOT/'capture-manifest.json'),
        input_archive_sha256=digest(ROOT/'input-archive.tar.gz'), tooling_archive_sha256=digest(output/'tooling.tar.gz'),
        files={name: dict(sha256=sha(data), bytes=len(data)) for name, data in files.items()},
        project_modules_exact=319, requested_roots_exact=172, probe_executed=False,
        consumption_coverage_complete=False, native_green=False, reviewed=False, accepted=False,
        scope='Prepared tooling identities only. Execute sequentially on pinned GCP builder-02 after full native GREEN and verified custody; independently classify unresolved boundaries before review.')
    (output/'readiness.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
