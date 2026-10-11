from pathlib import Path

# Preserve V1's wrong archive-member lookup. Only its exact lookup changes;
# no source proof bytes or verification conditions change.
prior = Path(__file__).with_name('prepare_numeric_original_ordered_row_law_offer_v1.py')
code = prior.read_text(encoding='utf-8')
old = "archive.extractfile('lean/lean-toolchain')"
new = "archive.extractfile('lean-toolchain')"
assert code.count(old) == 1
exec(compile(code.replace(old, new), str(prior), 'exec'))
