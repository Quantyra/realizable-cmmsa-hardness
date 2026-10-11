"""Capture only the two inspected narrow repairs after the immutable v2 offer."""
import json
from pathlib import Path
from custody_checks import digest
from capture_numeric_offers_20261011_v1 import capture

HERE=Path(__file__).resolve().parent


def main():
    source=HERE/'actual-numeric-explicit-height-candidate-v3'
    offer=json.loads((source/'manifest.json').read_bytes())
    previous=HERE/'numeric-explicit-height-offer-capture-v2'
    assert digest(previous/'index.json')==offer['repaired_from']['index_sha256']
    assert digest(previous/'ActualNumericExplicitHeight.lean')==offer['repaired_from']['source_sha256']
    old=json.loads((previous/'manifest.json').read_bytes())
    assert old['pinned_mathlib_api_inspection']==offer['pinned_mathlib_api_inspection']
    assert (previous/'ActualNumericExplicitHeightChecks.lean').read_bytes()==(source/'ActualNumericExplicitHeightChecks.lean').read_bytes()
    a=(previous/'ActualNumericExplicitHeight.lean').read_text(encoding='utf-8')
    before='      have hmulN : (numericN m : Real) ≤ (m : Real) * numericN m :=\n        mul_le_mul_of_nonneg_right hmOneR hNpos'
    after='      have hmulN : (numericN m : Real) ≤ (m : Real) * numericN m := by\n        simpa only [one_mul] using\n          (mul_le_mul_of_nonneg_right hmOneR hNpos)'
    assert a.count(before)==1 and a.replace(before,after)==(source/'ActualNumericExplicitHeight.lean').read_text(encoding='utf-8')
    parents=[(r['directory'],r['index_sha256'],r['source'],r['source_sha256']) for r in
             (offer['parent_source_height_capture'],offer['parent_scalar_capture'])]
    capture(source.name,'numeric-explicit-height-offer-capture-v3','manifest.json',
        '8E7F41B1BB1E6E2754219370183DAA32CC8CF0E2E968D28F9CCB99C444101F3B',parents,
        ['The sole source change explicitly simplifies one_mul in hmulN; exact complete diff verified.',
         'Argument map now correctly bounds r by max(base,Hnum), without bounding arbitrary base by Hnum.',
         'Checks unchanged; full source read via v1 and exact v2/v3 differences. No native acceptance; tactic/coercion repairs may remain.'])


if __name__=='__main__':main()
