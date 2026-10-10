"""Split full bodies across two complete packets after preserved context rejection."""
import json
from pathlib import Path
from custody_checks import digest
from audit_full107_prior_review_reuse import BASE, FRESH, LENSES


def main():
    old = BASE/'material-integration-v3'
    manifest = json.loads((old/'manifest.json').read_bytes())
    packet = manifest['packets'][0]
    assert packet['sha256'] == 'B995BB63DD9E53092EDB90CB044AE57B5277715EF6F4C186D0590AF689DCEC07'
    assert digest(packet['path']) == packet['sha256']
    failures = []
    for lens in LENSES:
        folder = old/(lens+'-01')
        raw = json.loads((folder/'stdout.json').read_bytes())
        assert int((folder/'native-exit.txt').read_text()) == 1
        assert raw['is_error'] and raw['terminal_reason'] == 'prompt_too_long'
        assert raw['api_error_status'] == 400 and raw['usage']['input_tokens'] == 0
        failures.append(dict(lens=lens, native_exit=1, raw_stdout_sha256=digest(folder/'stdout.json'),
                             original_scope_rejected=True, inference_performed=False))
    sections = {}
    for row in packet['files']:
        path = Path(row['source_root'])/row['path']
        assert digest(path) == row['sha256'] and path.stat().st_size == row['bytes']
        sections[row['path']] = ('\n=== COMPLETE FILE '+row['source_kind']+' '+row['path']+' SHA256 '+row['sha256']+' ===\n').encode()+path.read_bytes()+b'\n=== END COMPLETE FILE ===\n'
    body = b''.join(sections[row['path']] for row in packet['files'])
    original = Path(packet['path']).read_bytes()
    assert original.endswith(body)
    prefix = original[:-len(body)]
    fresh = [row for row in packet['files'] if row['path'] in FRESH]
    assert len(fresh) == 2
    groups = [[], []]
    sizes = [0, 0]
    for row in sorted((r for r in packet['files'] if r['path'] not in FRESH), key=lambda r: -len(sections[r['path']])):
        number = sizes.index(min(sizes))
        groups[number].append(row)
        sizes[number] += len(sections[row['path']])
    assert {r['path'] for group in groups for r in group} | set(FRESH) == set(sections)
    destination = BASE/'material-integration-v4'; destination.mkdir()
    packets = []
    for number, group in enumerate(groups, 1):
        selected = fresh+group
        notice = f'\nV4 COMPLETE-SCOPE SPLIT: packet{number} of2. Original one-packet attempts were rejected before inference. Both packets together retain all98 complete files; neither file nor argument nor prior report is truncated. Both fresh product-law bodies, full critical arguments, all39 prior reports and native/trace/reuse evidence appear in each packet. Review every supplied file; full per-lens integration requires both reports and root reconciliation. Do not claim unsupplied bodies freshly read.\n'.encode()
        text = prefix+notice+b''.join(sections[r['path']] for r in selected)
        assert len(text) < 1600000
        output = destination/f'integration-{number:02d}.txt'; output.open('xb').write(text)
        packets.append(dict(path=str(output),sha256=digest(output),bytes=len(text),files=selected))
    result = dict(manifest, schema='full107-full346-full260-conditional-material-integration-v4',
                  packets=packets, original_rejected_packet_sha256=packet['sha256'],
                  original_rejections=failures, common_unabridged_prefix_sha256=__import__('hashlib').sha256(prefix).hexdigest().upper(),
                  complete_file_union_preserved=98, fresh_two_complete_bodies_in_each_packet=True,
                  arguments_and39_prior_reports_unabridged_in_each_packet=True,
                  actual_provider_context_fit_verified=False, accepted=False)
    (destination/'manifest.json').open('x',encoding='utf-8').write(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(packets=[dict(bytes=r['bytes'],complete_files=len(r['files']),sha256=r['sha256']) for r in packets],complete_union=98,accepted=False)))


if __name__ == '__main__':
    main()
