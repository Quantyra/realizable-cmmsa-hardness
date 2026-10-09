"""Verify pinned Mathlib cardinality APIs without any Lean or cloud operation."""
import json
from pathlib import Path
import re
from custody_checks import digest

ROOT=Path('C:/Users/dfred/.quantyra/builder02/full97-spectral-bridge-utf8-section-repair-resource02')
HERE=Path(__file__).parent
SPECS=[('LinearAlgebra/Matrix/GeneralLinearGroup/Card.lean',
        ['card_linearIndependent','card_GL_field']),
       ('LinearAlgebra/Dimension/Finite.lean',['fintype_card_le_finrank'])]

def main():
    manifest=ROOT/'capture-manifest.json'
    assert digest(manifest)=='39CA9EDB48C35171FC878ED7301456C1D7C0BC5BCDF27F47FE96798040E5779D'
    pins=json.loads(manifest.read_bytes())['cache_provenance']['package_sources']
    rows=[]
    for rel,names in SPECS:
        path=ROOT/'consumption-v1/qualification/review-sources/external/Mathlib'/rel
        pin=pins['.lake/packages/mathlib/Mathlib/'+rel]
        assert digest(path)==pin
        text=path.read_bytes().decode('utf-8')
        declarations=[]
        for name in names:
            matches=list(re.finditer(r'(?m)^theorem '+re.escape(name)+r'\b[\s\S]*?:= by',text))
            assert len(matches)==1
            m=matches[0]
            declarations.append(dict(name=name,line=text[:m.start()].count('\n')+1,statement=m.group()))
        rows.append(dict(source_path=str(path),package_relative_path='.lake/packages/mathlib/Mathlib/'+rel,
                         sha256=pin,bytes=path.stat().st_size,declarations=declarations))
    report=dict(schema='actual-append-spectral-pinned-cardinality-API-audit-v1',
        pinned_manifest_sha256=digest(manifest),sources=rows,source_identity_verified=True,
        APIs=['card_linearIndependent','Matrix.card_GL_field','LinearIndependent.fintype_card_le_finrank'],
        frame_count_assumptions=['DivisionRing K','AddCommGroup V','Module K V','Fintype K','Finite V','k <= Module.finrank K V'],
        available_source_result='Nat.card independent ordered k-frames = product over Fin k of (card(K)^finrank(V) - card(K)^j)',
        zero_case_source_result='An independent finite family has card(index) <= finrank; larger frames are impossible',
        planned_specialization='K=ZMod 2, V=(Fin d -> ZMod 2) or kernel of Matrix.toLin frequency map',
        required_remaining_bridges=['Native specializations including dimension/zero cases',
            'Uniform full-basis tail pushforward to independent frames',
            'Tail-zero equivalence to frames in the actual frequency kernel',
            'Actual append coefficient/Parseval/finite-mean energy bridge',
            'Universal gain bound and transfer retaining the full original Spectral47 contract'],
        new_CMMSA_specialization_native_verified=False,uniform_distribution_proven=False,
        actual_append_energy_bound_proven=False,universal_Spectral47_inhabitant_proven=False,
        compiler_invoked=False,full_goal_complete=False,accepted=False)
    path=HERE/'actual-append-spectral-cardinality-api-audit-v1.json'
    path.write_bytes((json.dumps(report,indent=2,ensure_ascii=False)+'\n').encode('utf-8'))
    print(json.dumps({'sources':len(rows),'APIs':report['APIs'],'audit_sha256':digest(path),'new_native_proof':False}))

if __name__=='__main__':main()
