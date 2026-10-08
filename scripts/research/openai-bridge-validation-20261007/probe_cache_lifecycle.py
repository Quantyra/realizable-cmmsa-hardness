"""Run only on GCP: exercise the owned production mount component on fixtures."""
import datetime
import hashlib
import json
from pathlib import Path
import platform
import uuid
from isolated_cache import CacheMount

assert platform.system() == 'Linux'
home = Path.home().resolve()
root = home / ('cmmsa-cache-lifecycle_' + datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ') + '_' + uuid.uuid4().hex[:8])
root.mkdir()
warm = root / 'warm'; warm.mkdir(); (warm / 'sample').write_bytes(b'frozen-input')
for name in ('alpha', 'beta'): (root / name).mkdir()
caches = [CacheMount(root / name, warm) for name in ('alpha', 'beta')]
failure = None
try:
    for cache in caches: cache.open()
    for cache in caches:
        rows = [line.split() for line in Path('/proc/mounts').read_text().splitlines()]
        row = next(row for row in rows if row[1] == str(cache.root / 'lower'))
        assert 'ro' in row[3].split(',')
    a, b = [cache.view for cache in caches]
    (a / 'sample').write_bytes(b'alpha')
    assert (b / 'sample').read_bytes() == b'frozen-input'
    (b / 'sample').write_bytes(b'beta')
    (a / 'sample').unlink()
    assert (b / 'sample').read_bytes() == b'beta'
    assert (warm / 'sample').read_bytes() == b'frozen-input'
except Exception as error:
    failure = repr(error)
finally:
    cleanup = []
    for cache in reversed(caches):
        try: cache.close()
        except Exception as error: cleanup.append(repr(error))
    receipt = {'root': str(root), 'failure': failure, 'cleanup_failures': cleanup,
               'all_owned_mounts_released': all(not cache.mounted for cache in caches),
               'commands': [cache.receipts for cache in caches],
               'component_sha256': hashlib.sha256(Path(__file__).with_name('isolated_cache.py').read_bytes()).hexdigest(),
               'fixture_preserved': True, 'production_cache_touched': False,
               'lean_invoked': False, 'vm_power_operations': False}
    (root / 'receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))
if failure or cleanup or not receipt['all_owned_mounts_released']: raise SystemExit(1)
