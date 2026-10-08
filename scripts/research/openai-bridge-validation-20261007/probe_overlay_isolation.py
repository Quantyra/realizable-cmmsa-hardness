"""GCP-only filesystem-isolation probe;never compiles Lean or changes VM power."""
from pathlib import Path
import subprocess,json,hashlib,uuid,datetime
home=Path.home().resolve()
root=home/('cmmsa-overlay-preflight_'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'_'+uuid.uuid4().hex[:8])
assert root.parent==home and not root.exists()
root.mkdir();lower=root/'lower';lower.mkdir();(lower/'sample').write_bytes(b'frozen-input')
mounts=[];failure=None
try:
    for name in ['alpha','beta']:
        d=root/name;d.mkdir()
        for part in ['upper','work','view']:(d/part).mkdir()
        args=['sudo','-n','mount','-t','overlay','overlay','-o','lowerdir='+str(lower)+',upperdir='+str(d/'upper')+',workdir='+str(d/'work'),str(d/'view')]
        subprocess.run(args,check=True);mounts.append(d/'view')
    a=root/'alpha/view';b=root/'beta/view'
    (a/'sample').write_bytes(b'alpha-private')
    assert (lower/'sample').read_bytes()==b'frozen-input' and (b/'sample').read_bytes()==b'frozen-input'
    (b/'sample').write_bytes(b'beta-private')
    assert (a/'sample').read_bytes()==b'alpha-private' and (lower/'sample').read_bytes()==b'frozen-input'
    (a/'sample').unlink()
    assert not (a/'sample').exists() and (b/'sample').read_bytes()==b'beta-private' and (lower/'sample').read_bytes()==b'frozen-input'
except Exception as e:failure=repr(e)
finally:
    unmount=[]
    for target in reversed(mounts):
        assert target.resolve().is_relative_to(root)
        result=subprocess.run(['sudo','-n','umount',str(target)],capture_output=True)
        unmount.append({'target':str(target),'native_exit':result.returncode,'stderr':result.stderr.decode(errors='replace')})
    receipt={'root':str(root),'overlay_copyup_and_whiteout_isolation':failure is None,'failure':failure,'lower_sha256':hashlib.sha256((lower/'sample').read_bytes()).hexdigest(),'unmount':unmount,'fixture_preserved':True,'production_cache_touched':False,'vm_power_operations':False,'lean_invoked':False}
    (root/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if failure or any(x['native_exit'] for x in unmount):raise SystemExit(1)
