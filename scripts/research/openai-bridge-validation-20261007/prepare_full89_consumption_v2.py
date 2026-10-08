"""Preserve OOM v1 and replace expanded type rendering with shared Expr encoding."""
import io
import json
import re
from pathlib import Path
import tarfile
from custody_checks import digest, verify_local_custody
from full89_controller import ROOT, validate_successor
from prepare_builder02 import sha

DAG = r'''
private partial def dagName (n : Name) : Json :=
  match n with
  | .anonymous => Json.arr #[]
  | .str p s => Json.arr #[toJson "str", dagName p, toJson s]
  | .num p i => Json.arr #[toJson "num", dagName p, toJson i]
private structure TypeDagState where
  exprIds : Std.HashMap Expr Nat := {}
  levelIds : Std.HashMap Level Nat := {}
  exprNodes : Array Json := #[]
  levelNodes : Array Json := #[]
  deriving Inhabited
private partial def dagLevel (u : Level) : StateM TypeDagState Nat := do
  let s ← get
  if let some i := s.levelIds[u]? then return i
  let node ← match u with
    | .zero => pure (Json.arr #[toJson "zero"])
    | .succ v => do
      let i ← dagLevel v
      pure (Json.arr #[toJson "succ", toJson i])
    | .max v w => do
      let i ← dagLevel v
      let j ← dagLevel w
      pure (Json.arr #[toJson "max", toJson i, toJson j])
    | .imax v w => do
      let i ← dagLevel v
      let j ← dagLevel w
      pure (Json.arr #[toJson "imax", toJson i, toJson j])
    | .param n => pure (Json.arr #[toJson "param", dagName n])
    | .mvar n => pure (Json.arr #[toJson "mvar", dagName n.name])
  let s ← get
  let i := s.levelNodes.size
  set { s with levelIds := s.levelIds.insert u i, levelNodes := s.levelNodes.push node }
  return i
private partial def dagExpr (e : Expr) : StateM TypeDagState Nat := do
  let s ← get
  if let some i := s.exprIds[e]? then return i
  let node ← match e with
    | .bvar i => pure (Json.arr #[toJson "bvar", toJson i])
    | .fvar n => pure (Json.arr #[toJson "fvar", dagName n.name])
    | .mvar n => pure (Json.arr #[toJson "mvar", dagName n.name])
    | .sort u => do
      let i ← dagLevel u
      pure (Json.arr #[toJson "sort", toJson i])
    | .const n us => do
      let ids ← us.mapM dagLevel
      pure (Json.arr #[toJson "const", dagName n, toJson ids])
    | .app f a => do
      let i ← dagExpr f
      let j ← dagExpr a
      pure (Json.arr #[toJson "app", toJson i, toJson j])
    | .lam n t b bi => do
      let i ← dagExpr t
      let j ← dagExpr b
      pure (Json.arr #[toJson "lam", dagName n, toJson i, toJson j, toJson (reprStr bi)])
    | .forallE n t b bi => do
      let i ← dagExpr t
      let j ← dagExpr b
      pure (Json.arr #[toJson "forall", dagName n, toJson i, toJson j, toJson (reprStr bi)])
    | .letE n t v b nonDep => do
      let i ← dagExpr t
      let j ← dagExpr v
      let k ← dagExpr b
      pure (Json.arr #[toJson "let", dagName n, toJson i, toJson j, toJson k, toJson nonDep])
    | .lit (.natVal n) => pure (Json.arr #[toJson "nat", toJson n])
    | .lit (.strVal s) => pure (Json.arr #[toJson "string", toJson s])
    | .mdata md b => do
      let i ← dagExpr b
      pure (Json.arr #[toJson "mdata", toJson i, toJson (reprStr md)])
    | .proj n idx b => do
      let i ← dagExpr b
      pure (Json.arr #[toJson "proj", dagName n, toJson idx, toJson i])
  let s ← get
  let i := s.exprNodes.size
  set { s with exprIds := s.exprIds.insert e i, exprNodes := s.exprNodes.push node }
  return i
private def typeDagJson (e : Expr) : Json :=
  let (root, s) := (dagExpr e).run {}
  Json.mkObj [("schema", toJson "lean-expr-type-dag-v1"), ("root", toJson root),
    ("expr_nodes", Json.arr s.exprNodes), ("level_nodes", Json.arr s.levelNodes)]
'''

def validate_predecessor():
    parent = ROOT/'consumption-v1'
    marker = json.loads((parent/'launch-once.json').read_bytes())
    check = Path(marker['preflight'])
    terminal = json.loads((check/'terminal-custody.json').read_bytes())
    stop = json.loads((check/'vm-termination.json').read_bytes())
    if terminal['run'] != marker['run'] or stop['run'] != marker['run']:
        raise RuntimeError('Predecessor run identity differs')
    if terminal['probe_terminal']['probe_native_exit'] != 137 or stop['independent']['status'] != 'TERMINATED':
        raise RuntimeError('Required terminal failure and termination absent')
    if str(stop['independent']['id']) != '7237681467779354904' or stop['independent']['name'] != 'quantyra-lean-builder-02':
        raise RuntimeError('Foreign predecessor resource')
    if terminal['probe_terminal']['project_sources_preserved'] != 319 or terminal['probe_terminal']['compiled_objects_preserved'] != 645:
        raise RuntimeError('Predecessor preservation incomplete')
    custody = terminal['custody']
    verify_local_custody(custody['short_path'], custody['repository_path'], custody['remote_sha256'], custody['bytes'])
    return custody

def main():
    validate_successor()
    custody = validate_predecessor()
    old_readiness = json.loads((ROOT/'consumption-preparation/readiness.json').read_bytes())
    with tarfile.open(ROOT/'consumption-preparation/tooling.tar.gz') as archive:
        files = {m.name: archive.extractfile(m).read() for m in archive.getmembers()}
    for name, row in old_readiness['files'].items():
        if sha(files[name]) != row['sha256']: raise RuntimeError('Original tooling drift')
    old = files['probe.lean'].decode('utf-8')
    anchor = 'private def projectModules : List String :='
    if old.count(anchor) != 1 or old.count('("type_repr",toJson (reprStr c.type))') != 1:
        raise RuntimeError('Unexpected probe recipe anchor')
    source = old.replace(anchor, DAG+'\n'+anchor).replace('("type_repr",toJson (reprStr c.type))', '("type_dag",typeDagJson c.type)')
    source = source.replace('      | some c =>\n', '      | some c =>\n        IO.eprintln ("TRACE_ENTER " ++ n.toString)\n')
    source = source.replace('        let isProject :=', '        IO.eprintln ("TRACE_EDGES " ++ n.toString)\n        let isProject :=')
    for label in ('projectModules', 'roots'):
        pattern = r'private def '+label+r' : List String := (\[.*?\])'
        if re.search(pattern, old).group(1) != re.search(pattern, source).group(1):
            raise RuntimeError('Probe scope changed')
    files['probe.lean'] = source.encode('utf-8')
    output = ROOT/'consumption-preparation-v2-dag'; output.mkdir(exist_ok=False)
    with tarfile.open(output/'tooling.tar.gz', 'w:gz') as archive:
        for name, data in sorted(files.items()):
            member = tarfile.TarInfo(name); member.size = len(data); member.mode = 0o644
            archive.addfile(member, io.BytesIO(data))
    readiness = dict(old_readiness, tooling_archive_sha256=digest(output/'tooling.tar.gz'),
        files={name: dict(sha256=sha(data), bytes=len(data)) for name, data in files.items()},
        predecessor_probe_sha256=old_readiness['files']['probe.lean']['sha256'],
        predecessor_terminal_custody_sha256=custody['remote_sha256'],
        change='Shared Expr/Level DAG for types and per-node progress diagnostics; all roots/modules/type/proof/union edges and opaque-body retrieval retained.',
        native_verification_pending=True, probe_executed=False, consumption_coverage_complete=False, accepted=False)
    (output/'readiness.json').write_text(json.dumps(readiness, indent=2)+'\n', encoding='utf-8')
    (output/'probe.lean').write_bytes(files['probe.lean'])
    print(json.dumps(dict(probe_sha256=readiness['files']['probe.lean']['sha256'],
                         probe_bytes=len(files['probe.lean']), project_modules=319, roots=172, native_verification_pending=True)))

if __name__ == '__main__':
    main()
