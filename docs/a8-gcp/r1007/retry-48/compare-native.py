"""Compare exact final native headers and every authorized source; no compiler/Git."""
from pathlib import Path
import json, hashlib, sys
here = Path(__file__).resolve().parent
package = here.parent
repo = package.parents[2]
run = package / 'runs' / sys.argv[1]
snapshot = run / sys.argv[2] / 'native-stdout.snapshot'
offer = package / 'retry-16' / sys.argv[3]
auth = json.loads((here / 'authorized-owned-successor-paths.json').read_bytes())
owned = set(auth['paths_before'])
stage_index=int(sys.argv[4]) if len(sys.argv)>4 else 1
final = (run / f'remote-evidence/stage-{stage_index}.stdout').read_bytes()
provisional = snapshot.read_bytes()
def headers(data, prefix):
    return [line for line in data.decode('utf-8').splitlines()
            if line.startswith(prefix) and any(name in line for name in owned)]
errors = headers(final, 'error:')
warnings = headers(final, 'warning:')
value = {'headers_equal': errors == headers(provisional, 'error:') and
         warnings == headers(provisional, 'warning:'),
         'owned_error_headers': len(errors),
         'unsolved_goal_headers': sum('unsolved goals' in line for line in errors),
         'owned_warning_headers': len(warnings), 'authoritative_headers': errors,
         'authoritative_warnings': warnings,
         'source_sha256': hashlib.sha256(final).hexdigest().upper(),
         'stage_index': stage_index, 'combined_acceptance': False, 'scope': 'full14 original A8 A11; RED, no acceptance'}
assert value['headers_equal']
def save(name, obj):
    with (run / name).open('x', encoding='utf-8', newline='\n') as stream:
        json.dump(obj, stream, indent=2)
save('native-diagnostic-comparison.json', value)
pins = {name: hashlib.sha256((repo / name).read_bytes()).hexdigest().upper() for name in owned}
changed = {name: {'before': old, 'after': pins[name]}
           for name, old in auth['paths_before'].items() if old != pins[name]}
custody = json.loads((offer / 'custody.json').read_bytes())
for offer_name in sys.argv[5:]:
    extra=json.loads((package/'retry-16'/offer_name/'custody.json').read_bytes())
    assert not set(custody['exact_sha256']) & set(extra['exact_sha256'])
    custody['exact_sha256'].update(extra['exact_sha256'])
assert all(row['after'] == custody['exact_sha256'][Path(name).name]
           for name, row in changed.items())
save('all-owned-successor-comparison.json', {
    'all14paths_pinned': len(pins) == 14, 'changed': changed,
    'exact_successor_custody_match': True,
    'additional_successor_custodies':['retry-16/'+n+'/custody.json' for n in sys.argv[5:]],
    'executed_generic_and_authorized_reports_preserved': True})
print(json.dumps({key: value[key] for key in
    ['headers_equal', 'owned_error_headers', 'unsolved_goal_headers', 'owned_warning_headers']}))
