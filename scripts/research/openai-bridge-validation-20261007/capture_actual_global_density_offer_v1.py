"""Capture the complete uncompiled density bridge and exact project dependencies."""
import hashlib
import json
from pathlib import Path
import re
import tarfile
from custody_checks import digest
from lean_source_static_preflight_v2 import inspect_bytes

HERE=Path(__file__).resolve().parent
OFFER=HERE/'actual-global-density-bridge-offer-v1'


def main():
    manifest=OFFER/'OFFER-MANIFEST.json'
    assert digest(manifest)=='1060C3FEF1F711FDEC1CC439AF24A99749B1E796680B3EA261B93041C857E024'
    value=json.loads(manifest.read_bytes())
    assert set(p.name for p in OFFER.iterdir())=={'OFFER-MANIFEST.json'}|{r['path'] for r in value['files']}
    for row in value['files']:
        p=OFFER/row['path'];assert p.stat().st_size==row['bytes'] and digest(p)==row['sha256']
    archive=Path(value['source_identity']['archive']);assert digest(archive)==value['source_identity']['archive_sha256']
    with tarfile.open(archive,'r:gz') as tar:
        baseline=json.load(tar.extractfile('capture-manifest.json'))
        for row in value['full113_project_sources']:
            name='lean/PvNP/RealizableHardness/'+row['member'];raw=tar.extractfile(name).read()
            pin=hashlib.sha256(raw).hexdigest().upper()
            assert pin==row['sha256'].upper()==baseline['project_sources'][name]['sha256']
    lean=[p for p in OFFER.iterdir() if p.suffix=='.lean']
    lexical=[inspect_bytes(p.read_bytes(),p.name) for p in lean]
    source=OFFER/'ActualGlobalDensityBridge.lean';checks=OFFER/'ActualGlobalDensityBridgeChecks.lean'
    declared=re.findall(r'(?m)^theorem (\w+)',source.read_text(encoding='utf-8'))
    requested=re.findall(r'(?m)^#print axioms (.+)$',checks.read_text(encoding='utf-8'))
    assert set(requested)=={'PvNP.RealizableHardness.ActualGlobalDensityBridge.'+name for name in declared}
    out=HERE/'actual-global-density-bridge-capture-v1';out.mkdir(exist_ok=False)
    (out/'.gitattributes').write_text('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
    rows=[]
    for p in sorted(OFFER.iterdir()):
        raw=p.read_bytes();(out/p.name).open('xb').write(raw)
        assert digest(out/p.name)==digest(p)
        rows.append(dict(original=str(p),copy=p.name,bytes=len(raw),sha256=digest(p)))
    report=dict(files=rows,dependency_manifest_sha256=digest(manifest),project_dependencies_verified=len(value['full113_project_sources']),
        lexical_preflight=lexical,requested_axioms=requested,all_public_theorems_requested=True,
        root_read_complete_source_checks_map_manifest=True,
        argument_scope='General rational-threshold finite averaging for the same fixed tables and actual complement; one-way event inclusion retained',
        static_review_concerns=[
          'ASCII sum binder syntax must be checked and replaced with actual Lean summation notation if unsupported.',
          'Supply explicit (t := t) (h := h) (k := k) at all density/mass calls where phantom indices cannot be inferred; theorem statements must bind the intended leaf count.',
          'Distribute the outer complement weight through every nested sum before sum_congr.',
          'Convert the constant finite sum explicitly for the final pigeonhole lemma and provide its nonempty finset proof from derived hsideComp.'
        ],capture_control_sha256=digest(__file__),compiler_invoked=False,accepted=False,repair_requested=True)
    (out/'index.json').open('x').write(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(folder=out.name,index_sha256=digest(out/'index.json'),requests=len(requested),uncompiled=True)),flush=True)


if __name__=='__main__':main()
