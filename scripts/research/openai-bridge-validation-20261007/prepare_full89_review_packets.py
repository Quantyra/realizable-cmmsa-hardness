"""Partition complete bodies without truncation; every lens must cover every packet."""
import hashlib
import json
from pathlib import Path

ROOT = Path('C:/Users/dfred/.quantyra/builder02/full89-resource02/consumption-v2/qualification')


def main():
    source = ROOT/'review-sources'
    index = json.loads((source/'source-index.json').read_bytes())
    output = ROOT/'review-packets'; output.mkdir()
    rows = sorted(index['project_bodies'], key=lambda r: (not any(n in r['path'] for n in ('A22OriginalInduction.', 'OriginalExactInhabitant.', 'A22ParentFactorization.', 'HC46OriginalApplication.')), r['path']))
    chunks, current, size = [], [], 0
    for row in rows:
        data = (source/row['path']).read_bytes()
        assert hashlib.sha256(data).hexdigest().upper() == row['sha256'] and len(data) == row['bytes']
        if current and size + len(data) > 450000:
            chunks.append(current); current, size = [], 0
        current.append(row); size += len(data)
    if current: chunks.append(current)
    common = '''Review Full89 original A22/HC46/selected-consumer milestone. This is a partition of a complete review, never a whole-campaign verdict. GCP native scope: seven zero exits, 172 standard axiom profiles, 319 source closure; no owned errors/warnings or inherited regressions. Source-preserving trace: all172 roots, 7251 nodes, zero unresolved graph nodes. The complete selection has170 project files. External Init/Mathlib/Batteries boundaries use pinned kernel/library source; library trust is explicit, not claimed as newly reviewed proof. All source files and the exact172 theorem list are available in the absolute source-index location below. No local Lean/Lake or code execution. Do not invent additional context or acceptance. Broader Spectral47, source/star/robust8S/numericNO/encoded reduction/runtime/learning, upstream bridges, manuscript/render/novelty gates remain open. Audit original unrestricted-eta HC46 and real-q A22 with the same selected consumer, no added hHC premise. Check vacuity, quantifiers, assumptions, numerical exponent bounds and proof direction; distinguish conditional facts from universal claims. Report each supplied complete file as inspected or skipped, concrete findings with declaration/line references, severity, verdict GO/GO-WITH-NOTES/NO-GO/INCOMPLETE. Any skipped body means INCOMPLETE. Cross-partition and external-boundary questions remain explicit for integration. No tools, no writes, no subagents.
'''
    packets = []
    for i, group in enumerate(chunks):
        text = common + f'Absolute source index: {source / "source-index.json"}\nPartition {i+1}/{len(chunks)}.\n'
        for row in group:
            text += f'\n=== COMPLETE FILE {row["path"]} SHA256 {row["sha256"]} ===\n'
            text += (source/row['path']).read_text(encoding='utf-8')
            text += '\n=== END COMPLETE FILE ===\n'
        data = text.encode()
        assert len(data) < 600000
        path = output/f'packet-{i+1:02d}.txt'; path.write_bytes(data)
        packets.append({'path': str(path), 'sha256': hashlib.sha256(data).hexdigest().upper(), 'bytes': len(data), 'files': group})
    assert sum(len(p['files']) for p in packets) == 170
    manifest = {'packets': packets, 'required_lenses': ['proof-adversarial', 'complexity', 'non-claims'],
                'complete_body_partition': True, 'token_bound_policy': 'UTF-8 byte bound under600k per packet; actual provider input usage must be verified, with no compaction/truncation accepted.',
                'actual_context_fit_verified': False, 'integration_required': True, 'reviewed': False, 'accepted': False}
    (output/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'packets': len(packets), 'files': 170, 'max_bytes': max(p['bytes'] for p in packets)}))


if __name__ == '__main__': main()
