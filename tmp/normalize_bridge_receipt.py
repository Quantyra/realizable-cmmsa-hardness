from pathlib import Path
import hashlib

directory = Path('evidence/gcp/satellite/gcp_cmmsa_tagged_selected_decoder_bridge_20260928')
for name in ('build.log', 'replay.log', 'source.sha256'):
    path = directory / name
    normalized = '\n'.join(line.rstrip() for line in path.read_text(encoding='utf-8').splitlines()) + '\n'
    path.write_text(normalized, encoding='utf-8', newline='\n')

lines = []
for name in ('build.log', 'replay.log'):
    digest = hashlib.sha256((directory / name).read_bytes()).hexdigest()
    lines.append(f'{digest}  {name}')
(directory / 'logs.sha256').write_text('\n'.join(lines) + '\n', encoding='utf-8', newline='\n')
