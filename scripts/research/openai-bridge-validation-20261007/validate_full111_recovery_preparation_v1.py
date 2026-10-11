import ast,json,sys
from pathlib import Path
from custody_checks import digest
here=Path('.')
names=["audit_full110_settled_cache_recovery_v1.py","compress_full110_settled_native_metadata_v2.py","derive_full110_metadata_compression_v2.py","derive_full110_recovery_idle_refresh_v1.py","derive_full111_recovered_staging_v1.py","full110-metadata-compression-derivation-v2.json","full110-recovery-idle-refresh-derivation-v1.json","full111-recovered-staging-derivation-v1.json","preserve_full110_recovery_lifecycle_start_v1.py","refresh_full110_recovery_idle_v1.py","run_full110_resume_step_v3.py","run_full111_resume_step_v2.py","stage_full111_after_recovery_v1.py"]
for name in names:
    if name.endswith('.py'):
        ast.parse((here/name).read_text(encoding='utf-8'))
stage=json.loads((here/'full111-recovered-staging-derivation-v1.json').read_bytes())
text=(here/stage['source']).read_text(encoding='utf-8')
assert digest(here/stage['source'])==stage['source_sha256']
assert text.count(stage['removed_admission_block'])==1
text=text.replace(stage['removed_admission_block'],stage['replacement_admission_block'])
for old,new in stage['exact_replacements']:
    assert text.count(old)==1
    text=text.replace(old,new)
assert text.encode()==(here/stage['target']).read_bytes()
assert digest(here/stage['target'])==stage['target_sha256']
tree=ast.parse(text)
for node in ast.walk(tree):
    if isinstance(node,ast.Call) and isinstance(node.func,ast.Name) and node.func.id=='cloud':
        if node.args and isinstance(node.args[0],ast.List):
            constants=[x.value for x in node.args[0].elts if isinstance(x,ast.Constant)]
            assert constants[:3]!=['compute','instances','start']
value=json.loads((here/'full110-settled-native-metadata-lossless-v2/result.json').read_bytes())
assert len(value['files'])==70 and value['all_logical_sizes_and_hashes_unchanged']
for path,row in value['files'].items():
    assert digest(Path(path))==row['sha256'] and Path(path).stat().st_size==row['bytes']
print(json.dumps(dict(python_controls_parsed=10,staging_derivation_exact=True,no_VM_start_call=True,settled_compressed_files_verified=70,compiler_invoked=False)))
