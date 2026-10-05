"""Offline warning no-regression decision; legacy audit remains immutable."""
from collections import Counter
from pathlib import Path
import json, re, sys
from common import PACKAGE, SOURCE, CHECKS, file_sha, verify_capture, json_bytes, write_new

def headers(root, i):
    rows = Counter()
    for suffix in ['stdout', 'stderr']:
        for line in (root / f'stage-{i}.{suffix}').read_text(encoding='utf-8', errors='replace').splitlines():
            if re.match(r'^(?:warning\s*:|[^\s].*:\d+:\d+:\s*warning\s*:)', line):
                rows[re.sub(r'/home/dfredriksen_quantyra_org/cmmsa_[^/]+/', '<RUN>/', line)] += 1
    return rows

def check_baseline(manifest):
    seal = json.loads((PACKAGE / 'warning-baseline-seal.json').read_bytes())
    for rel, expected in seal['files'].items():
        assert file_sha(PACKAGE / rel) == expected, rel
    old = json.loads((PACKAGE / 'warning-baseline/manifest.json.snapshot').read_bytes())
    deps = {rel: row for rel, row in manifest['project_sources'].items() if rel not in {SOURCE, CHECKS}}
    assert all(rel in old['project_sources'] and row['sha256'] == old['project_sources'][rel]['sha256'] for rel,row in deps.items()), 'Dependency baseline drift'
    assert manifest['configs'] == old['configs'], 'Configuration baseline drift'
    assert manifest['external_source_baseline'] == old['external_source_baseline'], 'External baseline drift'
    baseline = Counter()
    for i in range(4):
        baseline |= headers(PACKAGE / 'warning-baseline', i)
    return baseline, seal

if __name__ == '__main__':
    if sys.argv[1] == '--preflight':
        manifest = verify_capture(PACKAGE / 'captures' / sys.argv[2])
        baseline, seal = check_baseline(manifest)
        output = {'baseline_verified_before_launch': True, 'warning_headers_in_frozen_union': sum(baseline.values()), 'seal_sha256': file_sha(PACKAGE / 'warning-baseline-seal.json')}
        write_new(PACKAGE / 'captures' / sys.argv[2] / 'warning-preflight.json', json_bytes(output))
        print(json.dumps(output, indent=2))
    else:
        run = PACKAGE / 'runs' / sys.argv[1]
        legacy = json.loads((run / 'audit-custody-recovered.json').read_bytes())
        manifest = verify_capture(PACKAGE / 'captures' / legacy['capture'], live=False)
        baseline, seal = check_baseline(manifest)
        failures = [f for f in legacy['failures'] if f != 'Warnings/errors/unsolved goals are not all zero']
        if legacy.get('diagnostics', {}).get('errors', 1) or legacy.get('diagnostics', {}).get('unsolved_goals', 1):
            failures.append('Errors or unsolved goals')
        regressions = Counter(); owned = Counter(); stages = []
        for i in range(4):
            rows = headers(run / 'remote-evidence', i)
            fresh = rows - baseline
            candidates = Counter({h:c for h,c in rows.items() if SOURCE in h or CHECKS in h})
            regressions |= fresh; owned |= candidates
            stages.append({'stage': i, 'total_warning_headers': sum(rows.values()), 'owned_warning_headers': sum(candidates.values()), 'above_frozen_baseline': dict(fresh)})
        if regressions: failures.append('Inherited warning regression')
        if owned: failures.append('New owned warnings')
        result = {'run': run.name, 'green': not failures, 'failures': failures,
            'compiler_stage_results': legacy.get('stage_results'), 'diagnostics': legacy.get('diagnostics'),
            'axiom_profiles': legacy.get('axiom_profiles'), 'warning_stage_results': stages,
            'new_owned_warning_headers': dict(owned), 'regressions': dict(regressions),
            'frozen_baseline_header_union': sum(baseline.values()), 'baseline_seal_sha256': file_sha(PACKAGE / 'warning-baseline-seal.json'),
            'legacy_zero_total_audit_green': legacy['green'], 'legacy_audit_sha256': file_sha(run / 'audit-custody-recovered.json'),
            'debt_story': 'S3137', 'source_sha256': manifest['offered_identities'][SOURCE],
            'checks_sha256': manifest['offered_identities'][CHECKS], 'owning_story': 'S3132 partial',
            'full_manuscript_certification': 'INCOMPLETE', 'route_final_reviews': 'INCOMPLETE'}
        write_new(run / 'prospective-audit-custody-recovered.json', json_bytes(result))
        print(json.dumps(result, indent=2))
        sys.exit(0 if result['green'] else 1)
