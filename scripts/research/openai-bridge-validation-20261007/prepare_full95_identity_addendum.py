"""Immutable full-scope review addendum for typed source/object custody questions."""
import json
from pathlib import Path
from custody_checks import digest
from prepare_builder02_full95 import OUTPUT
HERE=Path(__file__).parent
BASE=OUTPUT/'consumption-v1/qualification'
def main():
    original=json.loads((BASE/'material-integration-v1/manifest.json').read_bytes())
    row=original['packets'][0]
    packet=Path(row['path']).read_bytes();assert digest(row['path'])==row['sha256']
    identity=BASE/'source-object-identity-reconciliation-v1.json'
    audit=json.loads(identity.read_bytes());assert len(audit['mappings'])==4 and not audit['source_normalization_or_repair_performed']
    text=b"""FULL95 IMMUTABLE SOURCE/OBJECT IDENTITY ADDENDUM: independent resolution and full-scope reaffirmation.
All bodies, profiles, compiler/package/core/configuration, native and trace archives are unchanged. The original full67-body/current181-root integration packet follows intact. Also supplied are all3 original Full95 independent reports and an exact typed source-to-compiled-object mapping verified against frozen input bytes, reviewed source bytes, native before/after source seals, compiled-project inventory, object-after inventory, qualified native report, and trace source/object preservation.
Independently decide whether proof H-1 / complexity H1 is a real custody defect or a comparison of different artifact categories. Do not accept the author explanation by vote. Compare each source SHA under its .lean path against native source-before/source-after and the capture manifest; compare each object SHA under its .olean path against the compiled-project/object-after inventories and qualified report. Do not require source-file bytes and compiled binary bytes to have the same SHA. Reconcile the source/object convention and the 172-original/173-Full90/181-Full95 labels, and distinguish historical native-phase false flags from later trace/source/review receipts. No normalization or source repair occurred.
Read the original findings and full supplied bodies to whatever depth needed for independent reaffirmation; explicitly state body inspection/reuse coverage, remaining HIGHs and their exact scope. Preserve the original reports unchanged and state whether their conditional material verdict now stands. Neither this identity mapping nor a material GO settles universal Spectral47, numeric NO/useful e, joint source/selection witnesses, source/star/robust8S, encoded runtime/reduction/learning, upstream bridges or final novelty/publication gates. R14 runtime remains separate; the size of a fixed parameter alone is not a runtime proof or disproof.
No tools, writes, Lean/Lake or subagents. Give exact evidence-backed dispositions, conditional safe claim, and remaining to-do list. Do not issue unconditional theorem/manuscript acceptance.
"""
    text+=b'\nEXACT SOURCE/OBJECT IDENTITY RECONCILIATION SHA256 '+digest(identity).encode()+b'\n'+identity.read_bytes()
    for lens in original['required_lenses']:
        path=HERE/'full95-material-integration-reports'/(lens+'-01.md')
        receipt=json.loads(path.with_suffix('.json').read_bytes());assert digest(path)==receipt['report_sha256'] and receipt['actual_packet_context_fit']
        text+=('\nORIGINAL IMMUTABLE FULL95 REVIEW '+lens+' SHA256 '+digest(path)+'\n').encode()+path.read_bytes()
    text+=b'\nORIGINAL EXACT COMPLETE INTEGRATION PACKET\n'+packet
    assert len(text)<1800000,'Do not truncate full required bodies/reports'
    root=BASE/'material-integration-identity-addendum-v1';root.mkdir();path=root/'integration.txt';path.write_bytes(text)
    manifest=dict(original,schema='full95-full-scope-identity-addendum-v1',packets=[dict(row,path=str(path),sha256=digest(path),bytes=len(text))],
        parent_packet_sha256=row['sha256'],identity_mapping_sha256=digest(identity),source_bodies_changed=False,original_reports_changed=False,accepted=False)
    (root/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8');print(json.dumps({'bytes':len(text),'sha256':digest(path),'complete_bodies':67,'root':str(root)}))
if __name__=='__main__':main()
