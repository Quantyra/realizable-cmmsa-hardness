"""Extend the static additive proposal to six captured candidates on Full114."""
import ast,json
from pathlib import Path
from custody_checks import digest

HERE=Path(__file__).resolve().parent

def main():
    source=HERE/'prepare_complete_numeric_scope_v1.py'
    assert digest(source)=='4EE0A30D0EB3CA278A605A7B210200295520365040E28AD1EE8CCC1815115C29'
    raw=source.read_text(encoding='utf-8')
    replacements=[
        ('the four captured numeric offers','the six captured numeric and density offers'),
        ('full113-exact-real-complex-operators-repair3-resource02','full114-exact-real-complex-operators-repair4-resource02'),
        ('BE67B48A7D6AA2745A1D28B99953E29B5764686EECFE4EDCFA01908872DE7EC2','70FC4654130BA2BD9D1FFC79EA015F511E9BC7E4297D5D2DB6F62E42DC38CA04'),
        ('46D726F1F8D4A1784B5EE4FF6ED6E02AF0EA183AD959A984C525B7F361821A2B','60DE0615C4B5228F0AFE9A9D2DB487D92866C811D2E7595A06AA63CB18ED243E'),
        ("    ('numeric-explicit-height-offer-capture-v3', '48323F05192D57BC7E308FD80CF15CBA2ABA0DAF474DF603C9A49F09FB9D5B3F'),",
         "    ('numeric-explicit-height-offer-capture-v3', '48323F05192D57BC7E308FD80CF15CBA2ABA0DAF474DF603C9A49F09FB9D5B3F'),\n    ('actual-global-density-bridge-capture-v2', '30A2513548AC7DC5AB2521977D60BCCC05D5AA5EC4C23DA224D55CDE3B0C079A'),\n    ('numeric-exact-threshold-capture-v2', 'EFEC33817B3F7585E51AD5DA03840F8566E7C3FF61DA5FE8F0E30C3A21C62C22'),"),
        ("row['path']","row.get('path',row.get('copy'))"),
        ('assert len(sources) == 8','assert len(sources) == 12'),
        ('len(requests) == 24','len(requests) == 31'),
        ('== 377','== 381'),('== 371','== 378'),('sources=377','sources=381'),('profiles=371','profiles=378'),
        ('complete-numeric-additive-scope-proposal-v1','complete-numeric-additive-scope-proposal-v2'),
        ('Full113 live at proposal preparation; no acceptance asserted','Full114 native verification in progress; no acceptance asserted'),
        ('Same-instance source/table/lower-signal/physical-sampler construction','Route original global acceptance to the same-instance side density; source/table/sampler obligations remain under audit'),
        ('Effective satisfying common source/spectral cutoff and encoded runtime','Effective source base and encoded runtime; spectral cutoff zero specialization already source-supported'),
    ]
    rows=[]
    for old,new in replacements:
        count=raw.count(old);assert count>0,old
        raw=raw.replace(old,new);rows.append(dict(before=old,after=new,count=count))
    ast.parse(raw)
    target=HERE/'prepare_complete_numeric_scope_v2.py'
    target.open('x',encoding='utf-8',newline='\n').write(raw)
    result=dict(parent_control_sha256=digest(source),successor_control_sha256=digest(target),replacements=rows,
        six_immutable_captures=True,parent_sources_retained=369,parent_requests_retained=347,
        mathematical_sources_edited=False,execution_archive_created=False,compiler_invoked=False)
    (HERE/'complete-numeric-scope-derivation-v2.json').open('x').write(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)

if __name__=='__main__':main()
