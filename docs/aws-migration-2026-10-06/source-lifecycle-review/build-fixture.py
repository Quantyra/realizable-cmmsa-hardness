"""Derive only synthetic fixture builders; leave reviewed satellite bytes unchanged."""
import hashlib
import json
from pathlib import Path
AUDIT = Path(__file__).resolve().parent
WEBSITE = AUDIT.parents[2].parent/'Quantyra-Website'
HERE = WEBSITE/'scripts/aws-migration/source-lifecycle'
source = (HERE/'integration.test.mjs').read_text(encoding='utf-8')
prefix = source[:source.index("test('production collector")]
for name in ('core', 'packet', 'aws', 'collector', 'policy', 'lifecycle', 'proofs', 'wire'):
    prefix = prefix.replace("'./"+name+".mjs'", "'"+(HERE/(name+'.mjs')).as_uri()+"'")
prefix += '\nexport {fakeAWS,packetFixture,captured,original,mapping,staged};\n'
out = AUDIT/'website-derived-fixture.mjs'
out.write_text(prefix, encoding='utf-8')
(AUDIT/'derived-fixture-provenance.json').write_text(json.dumps({
    'source': str(HERE/'integration.test.mjs'),
    'source_sha256': hashlib.sha256((HERE/'integration.test.mjs').read_bytes()).hexdigest(),
    'derived': str(out), 'derived_sha256': hashlib.sha256(out.read_bytes()).hexdigest(),
    'transformation': 'Only prefix before first registered test; local imports become absolute file URLs; export fixture builders.'
}, indent=2), encoding='utf-8')
