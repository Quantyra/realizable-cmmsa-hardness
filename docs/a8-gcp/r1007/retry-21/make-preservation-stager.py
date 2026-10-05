from pathlib import Path
import ast
HERE=Path(__file__).resolve().parent
t=(HERE.parent/'retry-20/stage-current-preservation.py').read_text(encoding='utf-8').replace('retry-20','retry-21').replace('capture-integrated-20','capture-integrated-21').replace('cmmsa_a8_output_20261005T204004Z_25170909','cmmsa_a8_output_20261005T205338Z_98887da0').replace('successor-native-20-repair','successor-native-21-repair')
t=t.replace("+['retry-21']","+['retry-22']")
ast.parse(t); (HERE/'stage-current-preservation.py').write_bytes(t.encode())
