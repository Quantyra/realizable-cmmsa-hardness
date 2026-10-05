"""Offline preparation of the sole corrected S3132/A8 compiler attempt."""
from pathlib import Path
import hashlib, json, shutil, difflib, sys

p = Path(__file__).resolve().parent
repo = p.parents[3]
prior = p.parent / 'session-20261004T214637Z-compiler-retry'
scripts = ['common.py','prepare.py','runner.py','audit.py','cloud_capture.py','validate.py',
           'preserve-incomplete.py','remote-template.sh','README.md','.gitattributes','.gitignore',
           'prospective-audit.py','observe.py','closeout.py','deliver.py']
for name in scripts + ['workflow-protocol.snapshot','warning-baseline-seal.json']:
    shutil.copyfile(prior/name, p/name)
shutil.copytree(prior/'warning-baseline',p/'warning-baseline')
old_rel = prior.relative_to(repo).as_posix()
new_rel = p.relative_to(repo).as_posix()
source_hash = '071A4D1D34B17E065FCD7421F3C544AA00029983C75E26A231DD3E60E3FCED10'
checks_hash = '31BDCB4F891A449222FC812A5447439474ECAC5F00AB22DD802B6BDB137C1078'
statement = ('Existing S3132/A8 bounded increment after Luna transpose orientation correction.\n'
 'Range: quotient-C coordinates; kernel: H coordinates; P/R: quotient of range ambient.\n'
 'Claims and assumptions unchanged. No Sol source repair; zero helper credit.\n'
 'Prior red evidence: '+old_rel+'; no successor theorem or story closure.\n')
(p/'statement-fidelity.md').write_bytes(statement.encode('utf-8'))
report_hash = hashlib.sha256((p/'statement-fidelity.md').read_bytes()).hexdigest().upper()
common = (p/'common.py').read_text(encoding='utf-8').replace(old_rel,new_rel)
common = common.replace('9FC68B94545497AC9B562EC34B769E7CFA95F335E08F18AF78D8A67DD3AA66FA',source_hash)
common = common.replace('7ADA4EB03420CF310112557FA666548B6FA241D9479D5874CAFE1264EAAEE35E',report_hash)
(p/'common.py').write_bytes(common.encode('utf-8'))
prepare = (p/'prepare.py').read_text(encoding='utf-8')
prepare = prepare.replace('"prospective-audit.py"]','"prospective-audit.py", "observe.py", "closeout.py", "deliver.py", "setup.py", "workflow-protocol.snapshot", "warning-baseline-seal.json", "static-inspection.json", "statement-fidelity.md"]')
(p/'prepare.py').write_bytes(prepare.encode('utf-8'))
closeout = (p/'closeout.py').read_text(encoding='utf-8')
closeout = closeout.replace("Sol made one pre-capture mechanical repair: close the parenthesis after N in local g' definition. Claims and assumptions were unchanged. No further repair, successor increment, or retry was launched.", "Luna supplied the exact transpose orientation correction. Sol made no source repair. Claims and assumptions were unchanged. No successor increment was launched.")
(p/'closeout.py').write_bytes(closeout.encode('utf-8'))
deliver = (p/'deliver.py').read_text(encoding='utf-8').replace('root=p.parent.relative_to(REPO).as_posix()','root=p.relative_to(REPO).as_posix()')
(p/'deliver.py').write_bytes(deliver.encode('utf-8'))
sys.path.insert(0,str(p))
from common import SOURCE,CHECKS,forbidden_tokens,file_sha
rows = {}
for rel, expected in [(SOURCE,source_hash),(CHECKS,checks_hash)]:
    data=(repo/rel).read_bytes(); text=data.decode('utf-8',errors='strict')
    assert file_sha(repo/rel)==expected
    assert not data.startswith(b'\xef\xbb\xbf')
    bad=[v for v in ['\ufffd','â†','â§','â‚','Ã','Â'] if v in text]
    tokens=forbidden_tokens(data)
    assert not bad and not tokens
    rows[rel]={'sha256':expected,'bytes':len(data),'strict_UTF8':True,'BOM':False,'mojibake_markers':bad,'forbidden_tokens':tokens}
old=(prior/'captures').glob('*/source.lean.snapshot')
previous=list(old)[0].read_text(encoding='utf-8')
current=(repo/SOURCE).read_text(encoding='utf-8')
(p/'author-orientation-correction.diff').write_bytes(''.join(difflib.unified_diff(previous.splitlines(True),current.splitlines(True),fromfile='prior-red-source',tofile='Luna-corrected-source')).encode('utf-8'))
(p/'static-inspection.json').write_bytes((json.dumps({'targets':rows,'Sol_source_repairs':0,'helper_credit':0,'claims_and_assumptions_changed':False,'local_compilation':False},indent=2)+'\n').encode('utf-8'))
(p/'prior-completion-report.md.snapshot').write_bytes((prior/'completion-report.md').read_bytes())
(p/'prior-owned-diagnostics.txt.snapshot').write_bytes((prior/'owned-diagnostics.txt').read_bytes())
print(json.dumps({'session':new_rel,'static_inspection':rows},indent=2))
