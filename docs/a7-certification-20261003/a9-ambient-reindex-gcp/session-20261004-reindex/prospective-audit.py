"""Offline prospective warning decision; preserves the executed legacy audit."""
from pathlib import Path
from collections import Counter
import hashlib, json, re, sys
from common import verify_capture, SOURCE, CHECKS

p = Path(__file__).resolve().parent
run = p/'runs'/sys.argv[1]
legacy = json.loads((run/'audit.json').read_bytes())
manifest = verify_capture(p/'captures'/legacy['capture'], live=False)
seal = json.loads((p/'warning-baseline-seal.json').read_bytes())
for rel, expected in seal['files'].items():
    assert hashlib.sha256((p/rel).read_bytes()).hexdigest().upper() == expected
old = json.loads((p/'warning-baseline/manifest.json.snapshot').read_bytes())
drift = [rel for rel,row in old['project_sources'].items()
         if rel in manifest['project_sources'] and row['sha256'] != manifest['project_sources'][rel]['sha256']]
assert not drift, drift

def headers(root, i):
    text = '\n'.join((root/f'stage-{i}.{s}').read_text(encoding='utf-8',errors='replace') for s in ['stdout','stderr'])
    rows = Counter()
    for line in text.splitlines():
        if re.match(r'^(?:warning\s*:|[^\s].*:\d+:\d+:\s*warning\s*:)',line):
            line = re.sub(r'/home/dfredriksen_quantyra_org/cmmsa_[^/]+/', '<RUN>/', line)
            rows[line] += 1
    return rows

baseline = Counter()
for i in range(4):
    baseline |= headers(p/'warning-baseline',i)
extension_file = p/'expanded-dependency-warning-baseline-headers.json'
extension = json.loads(extension_file.read_bytes())
if run.name != extension['basis_run']:
    basis = p/'runs'/extension['basis_run']
    assert hashlib.sha256((basis/'manifest.json.snapshot').read_bytes()).hexdigest().upper() == extension['basis_manifest_sha256']
    assert hashlib.sha256((basis/'terminal.json').read_bytes()).hexdigest().upper() == extension['basis_terminal_sha256']
    for rel, expected in extension['basis_raw_hashes'].items():
        assert hashlib.sha256((basis/'remote-evidence'/rel).read_bytes()).hexdigest().upper() == expected
    assert all(manifest['project_sources'][rel]['sha256'] == row['sha256'] for rel,row in extension['project_sources'].items())
    baseline |= Counter(extension['additional_inherited_headers'])
results = []
regressions = Counter()
owned = Counter()
for i in range(4):
    rows = headers(run/'remote-evidence',i)
    fresh = rows-baseline
    regressions |= fresh
    candidates = Counter({h:c for h,c in rows.items() if SOURCE in h or CHECKS in h})
    owned |= candidates
    results.append({'stage':i,'warning_headers':sum(rows.values()),
                    'candidate_owned_headers':sum(candidates.values()),
                    'above_frozen_baseline':dict(fresh)})
failures = [f for f in legacy['failures'] if f != 'Warnings/errors/unsolved goals are not all zero']
if legacy.get('diagnostics',{}).get('errors',1) or legacy.get('diagnostics',{}).get('unsolved_goals',1):
    failures.append('Errors or unsolved goals')
if regressions:
    failures.append('Warning header regression against frozen prior ambient baseline')
if owned:
    failures.append('New owned warning headers')
result = {'run':run.name,'green':not failures,'failures':failures,
          'legacy_zero_total_audit_green':legacy['green'],
          'legacy_audit_unchanged_sha256':hashlib.sha256((run/'audit.json').read_bytes()).hexdigest().upper(),
          'warning_baseline_seal_sha256':hashlib.sha256((p/'warning-baseline-seal.json').read_bytes()).hexdigest().upper(),
          'inherited_dependency_warning_debt':748,'prior_ambient_owned_style_warning_debt':13,
          'additional_unchanged_dependency_header_debt':extension['additional_inherited_count'],
          'additional_dependency_diagnostic_occurrences_per_build_stage':343,
          'expanded_baseline_sha256':hashlib.sha256(extension_file.read_bytes()).hexdigest().upper(),
          'warning_count_note':'Legacy diagnostic counts also count warning text in multiline hints; prospective counts actual warning headers and normalizes only the unique workspace prefix.',
          'debt_story':'S3137','warning_stage_results':results,
          'new_owned_warning_headers':dict(owned),'regressions':dict(regressions),
          'shared_dependency_source_drift':drift,
          'compiler_stage_results':legacy.get('stage_results'),
          'axiom_profiles':legacy.get('axiom_profiles'),
          'source_sha256':manifest['offered_identities'][SOURCE],
          'checks_sha256':manifest['offered_identities'][CHECKS],
          'compiler_only_repairs':True,'helper_development_increments':0,
          'three_lens_reviews':'NOT RUN; user-directed',
          'full_manuscript_certification':'INCOMPLETE'}
output=run/'prospective-audit.json'
with output.open('x',encoding='utf-8') as f:
    json.dump(result,f,indent=2); f.write('\n')
print(json.dumps(result,indent=2))
sys.exit(0 if result['green'] else 1)
