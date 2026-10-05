from pathlib import Path
import ast
HERE=Path(__file__).resolve().parent
t=(HERE.parent/'retry-18/stage-current-preservation.py').read_text(encoding='utf-8').replace('retry-18','retry-19').replace('capture-integrated-18','capture-integrated-19').replace('cmmsa_a8_output_20261005T200559Z_dec38ed7','cmmsa_a8_output_20261005T202321Z_454c93d6')
start=t.index('offers='); end=t.index('\nroots+=',start)
offers=['successor-a11-weighted-a9-partition-offer','successor-a11-supported-charge-offer','successor-a11-finite-tail-offer','successor-a11-w6-terminal-offer','successor-a11-full-original-offer','successor-native-19-repair']
t=t[:start]+'offers='+repr(offers)+t[end:]
t=t.replace("attrs.write_text(text+'\n',encoding='utf-8')","attrs.write_bytes((text+'\n').encode('utf-8'))")
# Match literal escaped newline in Python source.
t=t.replace("attrs.write_text(text+'\\n',encoding='utf-8')","attrs.write_bytes((text+'\\n').encode('utf-8'))")
ast.parse(t); (HERE/'stage-current-preservation.py').write_bytes(t.encode())
