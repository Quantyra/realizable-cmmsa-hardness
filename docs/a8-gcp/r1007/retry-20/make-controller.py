"""Full original A8+A11/A7 coherent candidate; accepted A9 bytes pinned separately."""
from pathlib import Path
import ast,json,hashlib
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent
A9='lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A9AmbientReindex.lean'
accepted=PACKAGE.parents[1]/'a7-certification-20261003/a9-ambient-reindex-gcp/session-20261004-reindex'
data=(accepted/'captures/capture-20261004T192543Z/inputs'/A9).read_bytes()
report=json.loads((accepted/'report.json').read_bytes()); assert report['bounded_acceptance_green']
assert hashlib.sha256(data).hexdigest().upper()==report['source_sha256']=='5B4958CE0B86D02F578457715F05382EF6037535C5CDB7177F48945FF1E8A2BE'
(HERE/'accepted-a9-source.lean.snapshot').write_bytes(data)
(HERE/'accepted-a9-dependency.json').write_bytes(json.dumps({'source':A9,'sha256':report['source_sha256'],'accepted_report_sha256':hashlib.sha256((accepted/'report.json').read_bytes()).hexdigest().upper(),'accepted_run':report['run'],'accepted_evidence_sha256':report['evidence_archive_sha256'],'fresh_dependency_build_required':True,'all_three_direct_import_bytes_match_capture16':True,'new_acceptance_credit':False},indent=2).encode())
t=(PACKAGE/'retry-19/controller.py').read_text(encoding='utf-8').replace('integrated19_import','integrated20_import').replace('capture-integrated-19','capture-integrated-20').replace('retry-19/','retry-20/').replace('prepare19','prepare20')
needle="SOURCE=OWNED[-2]; CHECKS=OWNED[-1]"
t=t.replace(needle,"OWNED+=['lean/PvNP/RealizableHardness/ActualBinaryMatrixHC46A11WeightedAggregate'+s+'.lean' for s in ['', 'Checks']]\nSOURCE=OWNED[-2]; CHECKS=OWNED[-1]")
t=t.replace("'project_modules\": len(records) - 6, \"check_modules\": 6", "'project_modules\": len(records) - 7, \"check_modules\": 7")
t=t.replace('len(records) - 6, "check_modules": 6','len(records) - 7, "check_modules": 7')
needle="    common.write_new(HERE/'cloud_capture.snapshot.py',cloud)"
t=t.replace(needle,"    cloud=cloud.replace(\"for rel in manifest['owned_sources']:\",\"for rel in manifest['owned_sources']+['"+A9+"']:\")\n"+needle)
t=t.replace("        assert rel in old_manifest['project_sources'], 'Unmapped dependency '+rel", "        if rel=='"+A9+"':\n            data=(HERE/'accepted-a9-source.lean.snapshot').read_bytes(); assert common.sha(data)=='5B4958CE0B86D02F578457715F05382EF6037535C5CDB7177F48945FF1E8A2BE'\n            return data,'accepted A9 exact frozen bytes; fresh native dependency build with owned-artifact invalidation'\n        assert rel in old_manifest['project_sources'], 'Unmapped dependency '+rel")
t=t.replace("'PvNP.RealizableHardness.ActualBinaryMatrixHC46A8OutputCoordinateTransport']", "'PvNP.RealizableHardness.ActualBinaryMatrixHC46A8OutputCoordinateTransport','PvNP.RealizableHardness.ActualBinaryMatrixHC46A9AmbientReindex']")
ast.parse(t); (HERE/'controller.py').write_bytes(t.encode()); (HERE/'control').mkdir()
(HERE/'author-report.md').write_bytes(b'# Full original A8 and A11/A7 coherent development candidate\n\nFourteen owned source/Checks modules and fresh profiles for every Checks print, including original weighted hS and final allspaces A7 theorem. Exact captured native19 routine repairs9D38/9BDC and full original consumer054/F981. Accepted A9 source5B4958 is separately pinned to accepted report/input, direct imports identical to capture16, freshly built after all own artifacts unlinked. Unchanged200 dependencies retain400 exact object pins. No local Lean, no new helper acceptance, no manuscript completion claim.\n')
