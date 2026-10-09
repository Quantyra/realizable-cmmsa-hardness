"""Top-level tools-disabled critical-argument reviewer; not final closeout."""
import run_full90_material_review_packet as runner
from full100_consumption_v2_controller import ROOT

runner.ROOT = ROOT/'spectral-argument-review-v1'

if __name__ == '__main__': runner.main()
