"""Bind the existing bounded idle refresh to the settled Full110 recovery lifecycle."""
import ast
import json
from pathlib import Path
from custody_checks import digest

HERE = Path(__file__).resolve().parent
records = []
for source_name, target_name, changes in [
    ('refresh_full109_trace_staging_idle_v1.py', 'refresh_full110_recovery_idle_v1.py', [
        ('from full109_builder02_controller import', 'from full110_builder02_controller import'),
        ('from full109_capture_gates import validate_successor', 'from run_full110_settled_cache_recovery_v1 import settled'),
        ('    validate_successor()', '    settled()'),
        ("ROOT/'consumption-v3'/'launch-once.json'", "ROOT.parent/'full111-exact-real-complex-operators-repair-resource02'/'launch-once.json'"),
        ("ROOT/'consumption-v3'/'idle-refresh-controls'", "ROOT/'settled-cache-recovery-v1'/'idle-refresh-controls'")]),
    ('run_full110_resume_step_v2.py', 'run_full110_resume_step_v3.py', [
        ("ALLOWED = {'run_full110_settled_cache_recovery_v1.py'}", "ALLOWED = {'refresh_full110_recovery_idle_v1.py'}")])]:
    source = HERE / source_name
    text = source.read_text(encoding='utf-8')
    for old, new in changes:
        assert text.count(old) == 1, old
        text = text.replace(old, new)
    ast.parse(text)
    target = HERE / target_name
    target.open('xb').write(text.encode('utf-8'))
    records.append(dict(source=source_name, source_sha256=digest(source), target=target_name,
        target_sha256=digest(target), exact_replacements=changes))
(HERE / 'full110-recovery-idle-refresh-derivation-v1.json').open('x', encoding='utf-8').write(json.dumps(dict(
    records=records, idle_timer_remains_enabled=True, single_activity_refresh_only=True,
    compiler_or_new_resource_or_power_operation=False), indent=2)+'\n')
print(json.dumps(dict(controls=len(records), action_executed=False)))
