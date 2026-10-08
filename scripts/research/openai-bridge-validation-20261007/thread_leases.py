"""Cooperative shared-VM lease primitives. No cloud power operations."""
import json,re,os
from pathlib import Path
from contextlib import contextmanager
class Busy(RuntimeError):pass
class OwnershipError(RuntimeError):pass
def checked(value):
    if not re.fullmatch(r'[A-Za-z0-9_-]{1,96}',value):raise ValueError('Invalid identity')
    return value
@contextmanager
def locked(root):
    root=Path(root);root.mkdir(parents=True,exist_ok=True)
    lock=root/'coordination-lock'
    try:lock.mkdir()
    except FileExistsError:raise Busy('Lifecycle coordination is active;do not restart or clear its lock')
    try:yield root
    finally:lock.rmdir()
def phase(root):
    p=root/'manager-state.json'
    return json.loads(p.read_text())['phase'] if p.exists() else 'ACCEPTING'
def write_phase(root,value):
    p=root/'manager-state.next';p.write_text(json.dumps({'phase':value})+'\n')
    os.replace(p,root/'manager-state.json')
def acquire(root,thread,run):
    thread,run=checked(thread),checked(run)
    with locked(root) as root:
        if phase(root)!='ACCEPTING':raise Busy('VM lifecycle is draining')
        (root/'active').mkdir(exist_ok=True);lease=root/'active'/thread
        try:lease.mkdir()
        except FileExistsError:raise Busy('Thread already has an active lease;retain its handle')
        # A partially written lease still blocks shutdown.
        (lease/'owner.json').write_text(json.dumps({'thread':thread,'run':run})+'\n')
        return lease
def release(root,thread,run,*,native_terminal,custody_verified):
    thread,run=checked(thread),checked(run)
    with locked(root) as root:
        lease=root/'active'/thread;owner=json.loads((lease/'owner.json').read_text())
        if owner!={'thread':thread,'run':run}:raise OwnershipError('Cannot release another run')
        if not native_terminal or not custody_verified:raise Busy('Terminal and custody evidence required')
        completed=root/'completed';completed.mkdir(exist_ok=True);destination=completed/run
        if destination.exists():raise OwnershipError('Preserved completion already exists')
        (lease/'terminal-custody.json').write_text(json.dumps({'native_terminal':True,'custody_verified':True})+'\n')
        lease.rename(destination)  # Preserve metadata;never expire/delete a foreign lease.
        return destination
@contextmanager
def manager_drain(root,*,observed_unregistered_workloads):
    # Hold admission mutex across the manager action;DRAINING persists afterward.
    with locked(root) as root:
        active=root/'active'
        if active.exists() and any(active.iterdir()):raise Busy('Active or incomplete thread leases')
        if observed_unregistered_workloads:raise Busy('Unregistered workloads must be resolved')
        if phase(root)!='ACCEPTING':raise Busy('An existing lifecycle action owns this VM')
        write_phase(root,'DRAINING')
        yield
