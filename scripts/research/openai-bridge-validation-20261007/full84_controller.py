"""Verify the exact failed-parent source repair before the full seven-stage successor."""
import sys
sys.dont_write_bytecode=True
import json
import hashlib
from pathlib import Path
import tarfile
import builder02_controller as controller
from custody_checks import digest,verify_local_custody
from prepare_builder02_full84 import REL

ROOT=controller.ROOT.parent/'full84-resource02-warning-clean'
STAGE='/home/dfredriksen_quantyra_org/full84-builder02-stage'

def validate_capsule_successor(root,parent,expected,rel=REL):
    repair=json.loads((root/'source-repair.json').read_bytes())
    binding=json.loads((root/'resource-binding.json').read_bytes())
    if repair['source']!=rel: raise RuntimeError('Unexpected repair source')
    if binding['source_repair_sha256'] != digest(root/'source-repair.json'): raise RuntimeError('Repair identity drift')
    if binding['parent_resource_binding_sha256'] != digest(parent/'resource-binding.json'): raise RuntimeError('Parent binding drift')
    custody=repair['parent_custody']
    verify_local_custody(custody['short_path'],custody['repository_path'],custody['remote_sha256'],custody['bytes'])
    def files(path):
        with tarfile.open(path,'r:gz') as archive:
            members=archive.getmembers()
            if any(not m.isfile() for m in members) or len({m.name for m in members}) != len(members): raise RuntimeError('Invalid capsule')
            return {m.name:archive.extractfile(m).read() for m in members}
    old=files(parent/'input-archive.tar.gz'); new=files(root/'input-archive.tar.gz')
    if set(old)!=set(new) or sorted(name for name in old if old[name]!=new[name]) != sorted([rel,'capture-manifest.json']): raise RuntimeError('Unexpected successor changes')
    if hashlib.sha256(old[rel]).hexdigest().upper()!=repair['old_sha256']: raise RuntimeError('Parent source pin mismatch')
    source=old[rel].decode('utf-8')
    for before,after in repair['exact_edits'].items():
        if source.count(before)!=1: raise RuntimeError('Repair anchor drift')
        source=source.replace(before,after)
    if source.encode('utf-8')!=new[rel] or digest(root/'input-archive.tar.gz')!=binding['files']['input-archive.tar.gz']: raise RuntimeError('Repair/capsule mismatch')
    a=json.loads(old['capture-manifest.json']); b=json.loads(new['capture-manifest.json'])
    b['project_sources'][rel]=a['project_sources'][rel]
    if a!=b: raise RuntimeError('Stages, requests, configurations or provenance changed')
    if repair['new_sha256']!=expected or hashlib.sha256(new[rel]).hexdigest().upper()!=expected:
        raise RuntimeError('Unapproved proof repair')
    if json.loads(new['capture-manifest.json'])['project_sources'][rel]['sha256']!=expected:
        raise RuntimeError('Repaired manifest source pin mismatch')

def validate_successor():
    validate_capsule_successor(ROOT,controller.ROOT,'03519AE870FEF6A37EE833A3C1E1E26A8CA27F544C4F743D4DEB25A1F9D17C6A')

def main(execute=False):
    validate_successor()
    controller.ROOT=ROOT; controller.STAGE=STAGE
    controller.EXTRA_LOCAL_CONTROLS=('full84_controller.py',)
    return controller.main(execute)

if __name__=='__main__':
    if sys.argv[1:] not in ([],['--execute']): raise SystemExit('Default preflight or --execute')
    raise SystemExit(main(sys.argv[1:]==['--execute']))
