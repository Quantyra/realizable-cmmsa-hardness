from pathlib import Path
import ast
HERE=Path(__file__).resolve().parent
t=(HERE.parent/'retry-19/stage-current-preservation.py').read_text(encoding='utf-8').replace('retry-19','retry-20').replace('capture-integrated-19','capture-integrated-20').replace('cmmsa_a8_output_20261005T202321Z_454c93d6','cmmsa_a8_output_20261005T204004Z_25170909')
start=t.index('offers='); end=t.index('\nroots+=',start)
t=t[:start]+"offers=['successor-native-20-repair']"+t[end:]
t=t.replace("roots+=['retry-16/'+n for n in offers]","roots+=['retry-16/'+n for n in offers]+['retry-21']")
ast.parse(t); (HERE/'stage-current-preservation.py').write_bytes(t.encode())
