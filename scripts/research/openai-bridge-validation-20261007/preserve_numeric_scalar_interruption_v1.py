"""Preserve the interrupted author's draft; this is not a completed offer."""
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent
source = HERE / 'actual-numeric-no-scalar-candidate-v1/ActualNumericNoScalar.lean'
data = source.read_bytes()
data.decode('utf-8')
assert not data.startswith(b'\xef\xbb\xbf')
destination = HERE / 'actual-numeric-no-scalar-interrupted-v1'
destination.mkdir(exist_ok=False)
(destination / '.gitattributes').open('x', encoding='utf-8').write('* -text whitespace=cr-at-eol,-blank-at-eof,-blank-at-eol\n')
copy = destination / source.name
copy.open('xb').write(data)
assert digest(copy) == digest(source)
(destination / 'observation.json').open('x', encoding='utf-8').write(json.dumps(dict(
    source=str(source), copy=copy.name, bytes=len(data), sha256=digest(source),
    observed_agent='operator_author', provider_request_id='27b82bb4-6ff6-4933-940d-2e46cb59f7b8',
    observed_failure='stream disconnected before completion', raw_provider_transcript_archived=False,
    files_present=[p.name for p in source.parent.iterdir() if p.is_file()],
    completed_offer_received=False, Checks_received=False, argument_map_received=False,
    draft_preservation_not_offer_capture=True, compiler_invoked=False, accepted=False), indent=2)+'\n')
print(json.dumps(dict(folder=str(destination), bytes=len(data), sha256=digest(source), draft_only=True)), flush=True)
