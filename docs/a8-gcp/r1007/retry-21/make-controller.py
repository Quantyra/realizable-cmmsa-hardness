"""Prepare immutable next full candidate and lossless archive transport handling."""
from pathlib import Path
import ast,shutil
HERE=Path(__file__).resolve().parent; PACKAGE=HERE.parent
t=(PACKAGE/'retry-20/controller.py').read_text(encoding='utf-8').replace('integrated20_import','integrated21_import').replace('capture-integrated-20','capture-integrated-21').replace('retry-20/','retry-21/').replace('prepare20','prepare21')
needle='    def cloud(self,args,**kwargs):\n'
insert='''    def cloud(self,args,**kwargs):
        chunk=next((a for a in args if a.startswith('--command=dd if=')),None)
        if chunk is not None:
            assert re.fullmatch(r'--command=dd if=/home/dfredriksen_quantyra_org/cmmsa-evidence/cmmsa_a8_output_\\d{8}T\\d{6}Z_[a-f0-9]{8}-evidence\\.tar\\.gz bs=4194304 skip=\\d+ count=1 status=none \\| base64 -w0',chunk)
            kwargs['allow_failure']=True
            code,out,err=original_cloud(self,args,**kwargs)
            if code:
                common.write_new(self.run/('archive-chunk-native-nonzero-'+str(len(self.records)-1)+'.json'),common.json_bytes({'native_exit':code,'raw_receipts_preserved':True,'payload_sha256':common.sha(out),'compiler_outcome_unmodified':True,'custody_requires_exact_base64_length_and_full_remote_sha256':True}))
            return code,out,err
'''
assert t.count(needle)==1; t=t.replace(needle,insert)
ast.parse(t); (HERE/'controller.py').write_bytes(t.encode()); (HERE/'control').mkdir()
for n in ['accepted-a9-source.lean.snapshot','accepted-a9-dependency.json']:
    shutil.copyfile(PACKAGE/'retry-20'/n,HERE/n)
(HERE/'author-report.md').write_bytes(b'# Full original A8 and A11/A7 native successor\n\nExact routine native20 proof/API/parser repairs FB583C53/CF7FC710, same full original054/F981 A11/A7 consumer, fourteen owned modules and all49 fresh axiom requests. Accepted A9 exact5B4958 rebuilt after own lib/ir invalidation; same400 frozen dependency object pins. Archive transport nonzero exit receipts remain raw; received bytes can reach custody only after exact decoded chunk lengths and full remote/short/repository SHA256 parity. Compiler exits are unchanged. No local Lean or new helper acceptance.\n')
