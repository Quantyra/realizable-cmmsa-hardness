from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parent.parent
SOURCE=Path('paper/submission-manuscript.md')
src=(ROOT/SOURCE).read_text(encoding='utf-8')
# This renderer is deliberately tied to the submission source: every source line is
# assigned to a generated paragraph, table, statement or display in correspondence.json.
GREEK=['pi','sigma','gamma','epsilon','lambda','Gamma','Lambda','Sigma','rho','beta','delta','Delta','zeta','xi','tau','eta','kappa','alpha']
FUN=['log2','log','ln','sqrt','floor','ceil','min','max','dim','codim','Pr','SD','Grass','Zoom','sum','Omega']
def esc(s):
 return s.replace('\\',r'\textbackslash{}').replace('&',r'\&').replace('%',r'\%').replace('#',r'\#').replace('_',r'\_').replace('{',r'\{').replace('}',r'\}')
def math(s):
 s=s.strip().rstrip('.')
 # Balanced exponent and subscript groups.
 for op in ['^','_']:
  while op+'(' in s:
   st=s.index(op+'(');depth=1;j=st+2
   while depth and j<len(s):
    if s[j]=='(':depth+=1
    elif s[j]==')':depth-=1
    j+=1
   s=s[:st]+op+'{'+s[st+2:j-1]+'}'+s[j:]
 for fname,left,right in [('sqrt',r'\sqrt{','}'),('floor',r'\lfloor ',r'\rfloor'),('ceil',r'\lceil ',r'\rceil')]:
  while fname+'(' in s:
   st=s.rfind(fname+'(');p0=st+len(fname);dep=1;j=p0+1
   while dep and j<len(s):
    if s[j]=='(':dep+=1
    elif s[j]==')':dep-=1
    j+=1
   s=s[:st]+left+s[p0+1:j-1]+right+s[j:]
 s=re.sub(r'_(adv|zoom|new|outer|dim|learn|min)\b',r'_{\1}',s)
 s=s.replace('^learn',r'^{\mathrm{learn}}')
 for old,new in [('!=',r'\ne '),('<=',r'\le '),('>=',r'\ge '),('->',r'\to '),('subset',r'\subseteq '),('intersect',r'\cap '),(' times ',r'\times '),(' AND ',r'\land '),(' OR ',r'\lor ')]:s=s.replace(old,new)
 s=s.replace('^learn',r'^{\mathrm{learn}}');s=re.sub(r'(?<!_)\*',lambda m:r'\cdot ',s)
 s=re.sub(r'\bGF\(2\)',lambda m:r'\mathbb F_2',s)
 for g in GREEK:s=re.sub(r'(?<![A-Za-z\\])'+g+r'(?![A-Za-z])',lambda m:'\\'+g,s)
 s=re.sub(r'\blog2\b',lambda m:r'\log_2',s)
 for f in ['log','ln','min','max','dim','Pr','Omega']:
  s=re.sub(r'(?<![A-Za-z\\])'+f+r'(?![A-Za-z])',lambda m:'\\'+f,s)
 for f in ['SD','codim','Grass','Zoom','sum']:
  s=re.sub(r'(?<![A-Za-z\\])'+f+r'(?![A-Za-z])',lambda m:r'\operatorname{'+f+'}',s)
 s=s.replace('in ',r'\in ')
 s=re.sub(r'\b(adv|zoom|new|outer|learn)\b',lambda m:r'\mathrm{'+m[0]+'}',s)
 return s
# Exact displays avoid ambiguity in machine conversion of grouped expressions.
displays=[
r'\frac{\log\sigma_L}{\log L}\longrightarrow1,\qquad\gamma_L\longrightarrow0.',
r'\begin{aligned} L&=a-2\lceil\log_2(a+1)\rceil-c_U,\\ \sigma_a^{\mathrm{learn}}&=\lfloor0.49\sigma_L\rfloor, &\gamma_a^{\mathrm{learn}}&=5\gamma_L.\end{aligned}',
r'F_e=\bigvee_{b\in\Sigma_y}\left[z_{y,b}\land\bigwedge_{x\in X_e}\left(\bigvee_{a\in P_{e,x,b}}z_{x,a}\right)\right].',
r't=\frac{s+\lambda\epsilon}{1+\lambda},\qquad \sigma_{\mathrm{new}}=\lfloor\sigma/4\rfloor,\qquad \Gamma_{\mathrm{new}}=2\Gamma.',
r'\lfloor\sigma/4\rfloor(s+\lambda\epsilon)\le\frac{3\sigma s}{8}.',
r'\frac{3\sigma s/8}{\lambda}=\frac{3\Gamma}{8}',
r"\operatorname{SD}(P,P')\le\delta_{\mathrm{adv}}:=\beta\sqrt J\,2^{a+4}.",
r'\delta_{\mathrm{zoom}}:=\sqrt\beta\,J^{1/4}',
r'\Pr[D>T]\le\left(\frac{eAh^2}{T}\right)^T\le2^{-100h^2}',
r'\delta_{\mathrm{zoom}}+3\delta_{\mathrm{adv}}+2^{-70h^2}<2^{-20h^2}.',
r"\begin{aligned}\frac{\Pr[V\mid Q]}{\Pr[V]}&=\frac{\mathbf1[Q\subseteq V]}{{\dim V\brack a}_2P'(Q)}\\&\le2\frac{{3J\brack a}_2}{{3J-2D\brack a}_2}\le8\cdot2^{2aT}.\end{aligned}",
r'\begin{aligned}\Pr[\operatorname{codim}_V(W\cap V)\ne c\mid Q]&\le8\cdot2^{2aT}(2^c-1)\beta+\zeta\\&\le2\zeta.\end{aligned}',
r'\mathbf1[Q\subseteq V]\frac{{d\brack a}_2}{{\dim V\brack a}_2}.',
r'p_V=\frac{{\dim V-a-c\brack b}_2}{{\dim V-a\brack b}_2}=p_0\bigl(1+O(2^{-J/2})\bigr).',
r'O(2^{-J/2}+\zeta/p_0).',
r'2^{J+d-\dim W+1}\le2^{-2J+d+r+1}.',
r'2^{J+d-(\dim V-r)+1}\le2^{-2J+2T+d+r+1}.',
r'\frac{B_r}{2^{-2(1-\rho^3)h}}=\frac{2^{2(1000\rho^2-\rho^3)h}}{20\cdot5^r}\ge1',
r'A>\frac{20}{\kappa}.',
r'\epsilon_1\le\frac{\tau}{100(m+1)J}.',
r'\frac{(m+1)J\epsilon_1}{1-a}\le\frac{\tau}{75}<\tau.',
r'\sigma=\left\lfloor\frac{R^{1-1/m}}{16}\right\rfloor,\qquad\xi=\frac1{m^2}.',
r'\Gamma=2(3/4)^q,\qquad\epsilon=\frac{\Gamma}{16\sigma},\qquad\tau=\frac{\epsilon}{4q}.',
r'\begin{aligned}T&=32(N_0+11)P^2, &M&=2^{\operatorname{clog}_2 T},\\\frac{N_0\ln2+\ln12}{2(\epsilon/8)^2}&\le T\le M<2T.\end{aligned}',
r"B_0=\min\{A_0,\lceil Dt\rceil+N'\},\qquad v_i'=a_i/A_0,\qquad t'=B_0/A_0.",
r"\frac{\sigma_{\mathrm{new}}}{2}\frac{B_0}{D}\le\frac{\sigma_{\mathrm{new}}}{2}\left(t+\frac{N'+1}{D}\right)\le\frac9{16}\sigma_{\mathrm{new}}t<\sigma_{\mathrm{new}}t.",
r'L+2\lceil\log_2(L+1)\rceil+c_U.',
r'h(L,m)=b_m\left\lfloor\frac{\log_2((L-1)/(q(m+1)))}{2b_m}\right\rfloor,\qquad R=2^{2h}.',
r'\begin{aligned}\log R&=\log L-O(\log(m+1)+b_m)=\log L-o(\log L),\\\frac{\log\sigma}{\log L}&\longrightarrow1,\\\Gamma&=2(3/4)^{\lfloor\sqrt m\rfloor}\longrightarrow0.\end{aligned}',
r'\sigma_L=\left\lfloor\frac{\lfloor\sigma/4\rfloor}{2}\right\rfloor,\qquad\gamma_L=2\Gamma.'
]
# Render maximal mathematical token runs while retaining all prose words.
variables=set(GREEK+FUN+['H','X','v','u','y','z','label','Bin','O','o','E','pi','L','R','m','h','J','r','a','c','d','b','Q','W','V','U','P','D','T','C','A','N','M','N_0','N_outer','s','t','w','x','g','q','i','j','n','e_j','e','F','F_j','F_1','F_M','K','T1','T2','P_e','X_e','H_U','p0','p_V','c_U','a_i','A_0','B_0','B_j','B_r','B','v_i','w_i','f','N_min','S','kappa','C_*'])
def balanced_at(s,i):
 depth=1;j=i+1
 while j<len(s) and depth:
  if s[j]=='(':depth+=1
  if s[j]==')':depth-=1
  j+=1
 return j if depth==0 else i
# Fixed textual expressions with special set/probability semantics.
special={
 'P=ceil(1/epsilon)':r'P=\lceil 1/\epsilon\rceil',
 'clog_2 T':r'\operatorname{clog}_2 T',
 'M<64(N_0+11)P^2':r'M<64(N_0+11)P^2',
 '1/epsilon<=P':r'1/\epsilon\le P',
 'ln 2<=1':r'\ln 2\le1',
 'ln 12<=11':r'\ln 12\le11',
 'p_V':r'p_V',
 '2^N_0':r'2^{N_0}',
 'L=a-2 ceil(log2(a+1))-c_U':r'L=a-2\lceil\log_2(a+1)\rceil-c_U',

 'lambda(u)=E_e[1[y=u]+sum_i 1[x_i=u]]/(m+1)':r'\lambda(u)=\frac{\mathbb E_e[\mathbf1[y=u]+\sum_i\mathbf1[x_i=u]]}{m+1}',
 'Lambda=sum_u lambda(u)|Sigma_u|':r'\Lambda=\sum_u\lambda(u)|\Sigma_u|',
 'sum_i':r'\sum_i', 'sum_u':r'\sum_u',

 '(1/8)(5/8)^(1/(m+1))':r'\frac18(5/8)^{1/(m+1)}', '(3/4)^q':r'(3/4)^q',

 'GF(2)':r'\mathbb F_2','{0,1}':r'\{0,1\}','{0,...,r}':r'\{0,\ldots,r\}',
 'Gap^(0,gamma_L)_(sigma_L) F[L]-CMMSA':r'\operatorname{Gap}^{0,\gamma_L}_{\sigma_L}\mathcal F[L]\text{-CMMSA}',
 'Gap^(epsilon,gamma)_sigma F[L]-CMMSA':r'\operatorname{Gap}^{\epsilon,\gamma}_\sigma\mathcal F[L]\text{-CMMSA}',
 'Gap^(epsilon,gamma)_sigma Learn[a]':r'\operatorname{Gap}^{\epsilon,\gamma}_\sigma\operatorname{Learn}[a]',
 'Gap^(0,gamma^learn_a)_(sigma^learn_a) Learn[a]':r'\operatorname{Gap}^{0,\gamma_a^{\mathrm{learn}}}_{\sigma_a^{\mathrm{learn}}}\operatorname{Learn}[a]',
 'F[L]':r'\mathcal F[L]', 'w(x)=sum_{i:x_i=1} w_i':r'w(x)=\sum_{i:x_i=1}w_i',
 '[n choose a]_2':r'{n\brack a}_2', 'Q subset L subset W':r'Q\subseteq L\subseteq W',
 'W(Q) intersect V':r'W(Q)\cap V','Q+H_U':r'Q+H_U','L intersect H_U={0}':r'L\cap H_U=\{0\}',
 'L/Q':r'L/Q','{0,1}^N':r'\{0,1\}^N','{0,1}^n':r'\{0,1\}^n','1^n,1^s':r'1^n,1^s',
 'Pr[D>T | Q]':r'\Pr[D>T\mid Q]',
 'sum_{i=0}^{a-1} 2^(i-dim(V))':r'\sum_{i=0}^{a-1}2^{i-\dim V}',
  'T1':r'T_1','T2':r'T_2','p0':r'p_0',
 'loglog(J)':r'\log_2\log_2 J','binomial':None,
}
def inline(s):
 s=' '.join(s.split())
 s=s.replace('](../SOURCES.md)','](SOURCES.md)').replace('](../REVIEW.md)','](REVIEW.md)')
 s=re.sub(r'\[([^\]]+)\]\(SOURCES\.md\)',lambda m:r'\cite{HN,Hir22}' if 'HN' in m[1] else (r'\cite{MZ,MZ24,BKM}' if 'MZ' in m[1] else 'the bibliography'),s)
 s=s.replace('[MANUSCRIPT.md](MANUSCRIPT.md)','this manuscript').replace('[REVIEW.md](REVIEW.md)','the companion review disclosures').replace('[SOURCES.md](SOURCES.md)','the bibliography')
 s=re.sub(r'Theorem 1(?![0-9]|\.[0-9])',lambda m:r'Theorem~\ref{thm:main}',s);s=re.sub(r'Corollary 2(?![0-9]|\.[0-9])',lambda m:r'Corollary~\ref{cor:learn}',s)
 stash=[]
 def hold(v):
  stash.append(v);return f'@@{len(stash)-1}@@'
 s=re.sub(r'Theorem~\\ref\{thm:main\}|Corollary~\\ref\{cor:learn\}|\\cite\{[^}]+\}',lambda m:hold(m[0]),s)
 for a,b in sorted(special.items(),key=lambda kv:-len(kv[0])):
  if b is None:continue
  pat=r'(?<![A-Za-z0-9_])'+re.escape(a)+r'(?![A-Za-z0-9_])'
  s=re.sub(pat,lambda m:hold('\\('+b+'\\)'),s)
 # Protect non-mathematical article 'a', and prose single-letter words.
 out=[];i=0
 while i<len(s):
  if s.startswith('@@',i):
   j=s.find('@@',i+2);out.append(s[i:j+2]);i=j+2;continue
  mo=re.match(r'(?:[A-Za-z][A-Za-z0-9]*|\d+(?:\.\d+)?)(?:\*)?',s[i:])
  if not mo:out.append(esc(s[i]));i+=1;continue
  word=mo[0];j=i+len(word)
  if i>0 and s[i-1].isalpha():out.append(esc(word));i=j;continue
  ismath=word in variables or (word[0].isdigit() and j<len(s) and s[j] in '^_')
  if word in ['a','i','e','s','t','w','x','f','g','n','b','c','d','q','r','m','h']:
   # 'a' as English article is never italicized unless syntactically mathematical.
   if word=='a' and (j>=len(s) or s[j] not in '_^=<>+'):
    nextword=re.match(r'\s+([A-Za-z]+)',s[j:]);ismath=bool(nextword and nextword[1] in ['for','denotes'])
    ismath=ismath or bool(re.search(r'(?:cap|most|large|than|guessing|first|probability|within)\s+$',s[:i])) or (i>0 and s[i-1] in '-/=') or s[j:j+10].startswith('-subspace') or s[j:j+4]==',c,d'
  if word in ['floor','ceil','sqrt'] and (j>=len(s) or s[j]!='('):ismath=False
  if word=='s' and i>0 and s[i-1]=="'":ismath=False
  if word=='A' and j<len(s) and s[j]==' ':ismath=bool(re.match(r' (?:h\b|depends\b|does\b)',s[j:]))
  if ismath:
   # Include subscripts/exponents and immediate function arguments.
   while j<len(s):
    if s[j] in '_^':
     j+=1
     if j<len(s) and s[j]=='(':j=balanced_at(s,j)
     elif j<len(s) and s[j]=='{':
      k=s.find('}',j);j=k+1 if k>=0 else j
     else:
      mm=re.match(r"[A-Za-z0-9*]+",s[j:]);j+=len(mm[0]) if mm else 0
    elif s[j]=='(':
     k=balanced_at(s,j)
     if k==j:break
     if '@@' in s[j:k] or re.search(r'\b(?:the|of|for|and|or)\b',s[j:k]):break
     j=k
    elif s[j]=="'":j+=1
    else:break
   expr=s[i:j];out.append(hold('\\('+math(expr)+'\\)'))
  else:out.append(esc(word))
  i=j
 s=''.join(out)
 # Replace operators left outside math by math symbols.
 for a,b in [('<=',r'\(\le\)'),('>=',r'\(\ge\)'),('!=',r'\(\ne\)'),('->',r'\(\to\)'),('<',r'\(<\)'),('>',r'\(>\)')]:s=s.replace(a,b)
 s=re.sub(r'\*\*([^*]+)\*\*',lambda m:r'\textbf{'+m[1]+'}',s)
 s=s.replace('|',r'\(\mid\)').replace('*',r'\(\cdot\)')
 for _ in range(3):
  for j,v in enumerate(stash):s=s.replace(f'@@{j}@@',v)
 assert '@@' not in s,s
 s=s.replace(r'\)*\(',r'\)\(\cdot\)\(')
 return s
lines=src.splitlines();out=[];ledger=[];i=0;di=0;theorem=None;abstract=False;listopen=False;sec=0
skip_header={0,1,2}
while i<len(lines):
 start=i;line=lines[i]
 if i in skip_header or not line.strip():i+=1;continue
 if line.startswith('## Abstract'):
  out.append(r'\begin{abstract}');abstract=True;i+=1;continue
 if line.startswith('## '):
  if abstract:
   out += [r'\end{abstract}',r'\noindent\textbf{Keywords:} hardness of approximation; monotone formulas; realizable learning; PCPs.',r'\paragraph{Status.} Local submission draft based on the archived version 0.1.0. The full Lean formalization is incomplete; no formal certification is claimed. This paper has not been submitted or announced.']
   abstract=False
  sec+=1;out.append('\\section{'+esc(line[3:])+'}\\label{sec:'+str(sec)+'}');i+=1;continue
 if line.startswith('### '):out.append('\\subsection{'+esc(line[4:])+'}');i+=1;continue
 if line == '```latex':
  # Explicit reviewed mathematics stays in the canonical Markdown source.
  # These unnumbered displays do not consume the legacy numbered-display table.
  i+=1; block=[]
  while i<len(lines) and lines[i] != '```':
   block.append(lines[i]); i+=1
  if i==len(lines): raise ValueError('Unclosed explicit LaTeX block')
  i+=1; out.append('\n'.join(block))
 elif line.startswith('    '):
  block=[]
  while i<len(lines) and (lines[i].startswith('    ') or (not lines[i].strip() and i+1<len(lines) and lines[i+1].startswith('    '))):block.append(lines[i]);i+=1
  out.append('\\begin{equation}\\label{eq:'+str(di+1)+'}\n'+displays[di]+'\n\\end{equation}');di+=1
 elif line.startswith('|'):
  rows=[]
  while i<len(lines) and lines[i].startswith('|'):
   row=[x.strip() for x in lines[i].strip('|').split('|')]
   if not all(re.fullmatch(r'[-:]+',x or '-') for x in row):rows.append(row)
   i+=1
  out.append(r'\begin{longtable}{@{}p{0.29\textwidth}p{0.67\textwidth}@{}}\toprule')
  out.append(' & '.join('\\textbf{'+inline(x)+'}' for x in rows[0])+r'\\\midrule\endhead')
  for row in rows[1:]:out.append(' & '.join(inline(x) for x in row)+r'\\[5pt]')
  out.append(r'\bottomrule\end{longtable}')
 elif re.match(r'^\d+\. ',line):
  # Import contracts become numbered propositions, retaining numbered source references.
  block=[]
  while i<len(lines) and not (lines[i].startswith('       ') or (i>start and re.match(r'^\d+\. ',lines[i])) or lines[i].startswith('##')):
   if not lines[i].strip() and (i+1>=len(lines) or not lines[i+1].startswith('   ')):break
   block.append(lines[i]);i+=1
  text=' '.join(x.strip() for x in block);text=re.sub(r'^\d+\. ','',text)
  out.append('\\paragraph{Imported contract.} '+inline(text))
 elif line.startswith('* '):
  out.append(r'\begin{itemize}')
  while i<len(lines) and lines[i].startswith('* '):
   block=[lines[i][2:]];i+=1
   while i<len(lines) and lines[i].startswith('  ') and not lines[i].startswith('    '):block.append(lines[i].strip());i+=1
   out.append(r'\item '+inline(' '.join(block)))
  out.append(r'\end{itemize}')
 else:
  block=[]
  while i<len(lines) and lines[i].strip() and not lines[i].startswith(('##','    ','|','* ','```')) and not (i>start and re.match(r'^\d+\. ',lines[i])):
   block.append(lines[i].strip());i+=1
  text=' '.join(block)
  if text.startswith('**Theorem 1'):
   text=text.split('**',2)[2];out.append(r'\begin{theorem}[Realizable CMMSA]\label{thm:main}'+inline(text));theorem='theorem'
  elif text.startswith('**Corollary 2'):
   text=text.split('**',2)[2];out.append(r'\begin{corollary}[Realizable learning]\label{cor:learn}'+inline(text));theorem='corollary'
  else:out.append(inline(text))
  if theorem and (text.startswith('such that, for every') or text.startswith('Then Gap')):
   out.append('\\end{'+theorem+'}');theorem=None
  if not block:raise RuntimeError((i,lines[i]))
 ledger.append({'source_start_line':start+1,'source_end_line':i,'source_text_sha256':hashlib.sha256('\n'.join(lines[start:i]).encode()).hexdigest()})
 out.append('')
assert di==len(displays),(di,len(displays))
# Theorem 1 includes the following short sentence; close only after that paragraph.
tex='\n'.join(out)
tex=tex.replace('HN revision 1 proves',r'HN revision 1~\cite{HN} proves',1)
tex=tex.replace("Hirahara's FOCS 2022 work",r"Hirahara's FOCS 2022 work~\cite{Hir22}",1)
tex=tex.replace('The MZ higher-query',r'The MZ~\cite{MZ} higher-query',1)
tex=tex.replace("MZ24's two-query",r"MZ24's~\cite{MZ24} two-query",1)
tex=tex.replace('KMS Definition 4.5',r'KMS~\cite{KMS}, Definition 4.5',1)
tex=tex.replace('\\section{Explicit-list exception lemma}',r'\section{Explicit-list exception lemma}')
# Mark the central stand-alone lemma and its complete proof without changing text.
tex=tex.replace('Input: ',r'\begin{lemma}[Finite-list completeness repair]\label{lem:repair} Input: ',1)
tex=tex.replace('In the YES case, take an original witness',r'The resulting list has at most \(L+1\) leaves per formula. In the YES case an assignment of normalized weight at most \(t\) satisfies every formula. In the NO case every assignment of normalized weight at most \(\sigma_{\mathrm{new}}t\) satisfies strictly less than \(\Gamma_{\mathrm{new}}\) of the list.\end{lemma}\begin{proof} In the YES case, take an original witness',1)
tex=tex.replace('No SAT, optimum, or counting oracle is used.', 'No SAT, optimum, or counting oracle is used.',1)
tex=tex.replace('sampling precedes it.','sampling precedes it.\\end{proof}',1)
# Add navigational cross-references, keeping them explicitly editorial.
tex=tex.replace(r'We now prove the parameter extension and the remaining composition in full.',r'We now prove the parameter extension and the remaining composition in full. Lemma~\ref{lem:repair} gives the finite-list repair; Sections~\ref{sec:6}--\ref{sec:10} supply the parameter and reduction arguments for Theorem~\ref{thm:main} and Corollary~\ref{cor:learn}.')
tex=tex.replace('This completes both proofs.',r'This completes the proofs of Theorem~\ref{thm:main} and Corollary~\ref{cor:learn}.\hfill$\square$')
tex=re.sub(r'\{([^{}]+)\\brack ([^{}]+)\}_2',lambda m:r'\genfrac{[}{]}{0pt}{}{'+m[1]+'}{'+m[2]+'}_2',tex)
(ROOT/'paper'/'body.tex').write_text(tex,encoding='utf-8',newline='\n')
(ROOT/'paper'/'correspondence.json').write_text(json.dumps({'source':SOURCE.as_posix(),'source_sha256':hashlib.sha256(src.encode()).hexdigest(),'source_lines':len(lines),'display_count':di,'mapping':ledger},indent=2)+'\n',encoding='utf-8',newline='\n')
print('Rendered body',len(tex),'characters',di,'displays',len(ledger),'source spans')
