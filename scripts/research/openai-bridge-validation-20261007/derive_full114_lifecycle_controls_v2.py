"""Exact rebinding of settled lifecycle, recovery and transport controls."""
import ast
import json
from pathlib import Path
import re
import subprocess
from custody_checks import digest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PREFIX = HERE.relative_to(REPO).as_posix() + '/'
BASE = '91ea5a69'


def main():
    rows = []
    common = [('full113-exact-real-complex-operators-repair3', 'full114-exact-real-complex-operators-repair4'),
              ('full113', 'full114'), ('Full113', 'Full114')]
    def derive(name, target, changes):
        raw = (HERE/name).read_bytes()
        assert raw == subprocess.check_output(['git','cat-file','blob',BASE+':'+PREFIX+name],cwd=REPO)
        text = raw.decode(); replacements=[]
        for old,new in changes:
            count=text.count(old)
            if not count:
                assert (old,new) in common,(name,old)
                continue
            text=text.replace(old,new);replacements.append(dict(old=old,new=new,occurrences=count))
        ast.parse(text); (HERE/target).open('xb').write(text.encode())
        rows.append(dict(source=name,source_commit=BASE,source_sha256=digest(HERE/name),target=target,target_sha256=digest(HERE/target),exact_replacements=replacements))
    derive('run_full112_settled_cache_recovery_v1.py','run_full113_settled_cache_recovery_v1.py',common+[
        ('full112','full113'),
        ('cmmsa_a8_output_20261011T051406Z_3ef6ddc2','cmmsa_a8_output_20261011T060110Z_204d10cd')])
    for name in ['full113_dedicated_openssh_v2.py','full113_openssh_control_v1.py',
                 'run_full113_native_openssh_v1.py','terminate_full113_after_custody_openssh_v1.py',
                 'stage_full113_after_recovery_openssh_v2.py','validate_full113_openssh_controls_v2.py']:
        derive(name,name.replace('full113','full114'),common)
    for name in ['run_full113_cache_recovery_v2.py','audit_full113_cache_recovery_v2.py','preserve_full113_recovery_v2.py']:
        derive(name,name.replace('full113','full114'),common+[('full112','full113')])
    derive('refresh_full113_recovery_idle_v1.py','refresh_full114_recovery_idle_v1.py',common+[
        ('from run_full114_cache_recovery_v1 import RECOVERY','from run_full114_cache_recovery_v2 import RECOVERY')])
    derive('inspect_full113_recovery_capacity_v2.py','inspect_full114_recovery_capacity_v2.py',common+[
        ('range(83, 99)','range(106, 114)')])
    derive('inspect_full113_generated_cache_capacity_v1.py','inspect_full114_generated_cache_capacity_v1.py',common+[
        ('cmmsa_a8_output_20261011T051406Z_3ef6ddc2','cmmsa_a8_output_20261011T060110Z_204d10cd'),
        ('663376C33593CB13D2ACF4ADD8B872D1DAFD718FC61C8080A0D5B101B6E6C8D5','46D726F1F8D4A1784B5EE4FF6ED6E02AF0EA183AD959A984C525B7F361821A2B')])
    source=(HERE/'run_full113_resume_step_v5.py').read_text()
    old=re.search(r'^ALLOWED = .+$',source,re.M).group()
    allowed=['run_full113_settled_cache_recovery_v1.py','run_full114_cache_recovery_v2.py','audit_full114_cache_recovery_v2.py',
        'preserve_full114_recovery_v2.py','stage_full114_after_recovery_openssh_v2.py','run_full114_native_openssh_v1.py',
        'terminate_full114_after_custody_openssh_v1.py','full114_postprocess.py','inspect_full114_recovery_capacity_v2.py',
        'inspect_full114_generated_cache_capacity_v1.py','preserve_full114_frozen_package_v1.py','refresh_full114_recovery_idle_v1.py']
    derive('run_full113_resume_step_v5.py','run_full114_resume_step_v2.py',[(old,'ALLOWED = '+repr(set(allowed))),
        ('from full113_builder02_controller import ROOT','from full114_builder02_controller import ROOT')])
    derive('preserve_full113_frozen_package_v1.py','preserve_full114_frozen_package_v1.py',common+[
        ('two-source','one-source-private-helper'),
        ('20261011T053328425826Z','20261011T062522107773Z'),
        ('original_preparation_tool_handle=74402','original_preparation_tool_handle=54521'),
        ('original_validation_tool_handle=74402','original_validation_tool_handle=29921'),
        ('all367_other_sources','all368_other_sources')])
    (HERE/'full114-lifecycle-control-derivation-v2.json').open('x').write(json.dumps(dict(records=rows,
        exact_current_parent_native_run='cmmsa_a8_output_20261011T060110Z_204d10cd',
        all_thresholds_retained=True,VM_creation=False,cloud_action=False,compiler_invoked=False),indent=2)+'\n')
    print(json.dumps(dict(derived=len(rows),compiler_invoked=False)))


if __name__ == '__main__':
    main()
