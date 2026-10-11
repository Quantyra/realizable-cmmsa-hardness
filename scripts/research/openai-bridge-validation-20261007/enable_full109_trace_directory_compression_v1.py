"""Enable lossless compression for future trace files; no content deletion."""
import json
import shutil
import stat
import subprocess
from full109_builder02_controller import ROOT
from custody_checks import digest


def main():
    target = ROOT/'consumption-v3'
    assert target.resolve().parent == ROOT.resolve() and target.is_dir()
    assert not (target/'launch-once.json').exists()
    folder = ROOT/'local-custody-directory-compression-v1'
    folder.mkdir(exist_ok=False)
    paths = sorted(p for p in target.iterdir() if p.is_file())
    before = {p.name:dict(bytes=p.stat().st_size, sha256=digest(p)) for p in paths}
    attrs = target.stat().st_file_attributes
    free = shutil.disk_usage(target).free
    argv = ['compact.exe', '/C', '/Q', str(target)]
    result = subprocess.run(argv, capture_output=True, creationflags=subprocess.CREATE_NO_WINDOW)
    (folder/'stdout').write_bytes(result.stdout)
    (folder/'stderr').write_bytes(result.stderr)
    after = {p.name:dict(bytes=p.stat().st_size, sha256=digest(p)) for p in paths}
    record = dict(argv=argv, native_exit=result.returncode, before=before, after=after,
                  attributes_before=attrs, attributes_after=target.stat().st_file_attributes,
                  free_before_bytes=free, free_after_bytes=shutil.disk_usage(target).free,
                  recursive_operation=False, source_or_archive_deleted=False,
                  existing_root_file_bytes_unchanged=before == after,
                  scope='Directory compression inheritance for subsequently created trace artifacts',
                  compiler_invoked=False, VM_operation=False)
    (folder/'receipt.json').write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
    assert result.returncode == 0 and before == after
    assert target.stat().st_file_attributes & stat.FILE_ATTRIBUTE_COMPRESSED
    print(json.dumps(dict(folder=str(folder), root_files_verified=len(paths), compression_inheritance_enabled=True)))


if __name__ == '__main__':
    main()
