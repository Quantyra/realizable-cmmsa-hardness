from pathlib import Path
import hashlib
import json

S = Path(__file__).resolve().parent
OUT = S / 'numeric-count-import-readback-20261011-v1'
PDF = Path(r'C:\Users\dfred\.quantyra\source-verification\spectral-primary-20261009-v1\mz24-eccc-r1-windows.pdf')
sha = lambda raw: hashlib.sha256(raw).hexdigest().upper()
pin = '13B8EB55F86CFE28AC8B283FE83612889B335E14B7A87D64D479451693C7DFF4'
assert sha(PDF.read_bytes()) == pin
assert not (OUT / 'source-readback.json').exists()
files = []
for name in ['page-41.png', 'page-42.png']:
    raw = (OUT / name).read_bytes()
    assert raw.startswith(b'\x89PNG\r\n\x1a\n')
    files.append(dict(path=name, bytes=len(raw), sha256=sha(raw)))
receipt = dict(schema='numeric-count-import-readback-20261011-v1',
    story='E002/S3137', author='/root', accepted=False, compiler_invoked=False,
    source=dict(path=str(PDF), sha256=pin,
        url='https://eccc.weizmann.ac.il/report/2024/027/revision/1/download/',
        version='ECCC report 2024/027 revision 1', printed_pages=[41,42]),
    rendering=dict(tool='pymupdf', scale=1.3, original_exec_chunk='33c698', exit_code=0,
        visual_readback_performed=True),
    text_extraction=dict(tool='Git bundled pdftotext', first_page=40, last_page=43,
        original_exec_chunk='7f2582', exit_code=0, stdout_only=True,
        glyph_loss=True, visual_readback_controls_formula_reading=True),
    earlier_read_attempt=dict(module='pypdf', original_exec_chunk='b20967', exit_code=1,
        error='ModuleNotFoundError: No module named pypdf', source_modified=False,
        packages_installed=False, native_log_file_created=False),
    interpretation=dict(scope='All maximal window/function pairs; no fixed-window substitution',
        exact_reciprocal_binding='n=b*m>0; delta=1/n; xi=delta^5; delta2=xi/100',
        integer_parameter='t=factorial(2^(2+1000*n^5))',
        linear_exponent='100*factorial(t-1)*(10*n)^2*n^5',
        source_height_cutoff_retained=True, source_count_locally_proved=False,
        source_game_identified=False), files=files)
(OUT/'source-readback.json').write_text(json.dumps(receipt, indent=2)+'\n',
    encoding='utf-8', newline='\n')
print(json.dumps(dict(receipt_sha256=sha((OUT/'source-readback.json').read_bytes()),
                     rendered_files=files)))
