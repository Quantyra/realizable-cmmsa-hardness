from pathlib import Path
import subprocess,shutil,os
p=Path(__file__).resolve().parent
os.environ.setdefault('SOURCE_DATE_EPOCH','1789171200')
os.environ.setdefault('FORCE_SOURCE_DATE','1')
root=p.parent;build=root/'tmp'/'pdfs';build.mkdir(parents=True,exist_ok=True)
subprocess.run(['python',str(p/'render_manuscript.py')],check=True,cwd=root)
shutil.copyfile(p/'references.bib',build/'references.bib')
cmd=['pdflatex','--interaction=nonstopmode','--halt-on-error','--output-directory='+str(build),'realizable-hardness.tex']
for stage in range(3):
 result=subprocess.run(cmd,cwd=p,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (build/f'pdflatex-pass-{stage+1}.log').write_bytes(result.stdout)
 if result.returncode:print(result.stdout.decode(errors='replace'));raise SystemExit(result.returncode)
 if stage==0:
  r=subprocess.run(['bibtex','realizable-hardness'],cwd=build,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(build/'bibtex-build.log').write_bytes(r.stdout);r.check_returncode()
out=root/'output'/'pdf';out.mkdir(parents=True,exist_ok=True);shutil.copyfile(build/'realizable-hardness.pdf',out/'realizable-hardness.pdf')
print('Built',out/'realizable-hardness.pdf')
