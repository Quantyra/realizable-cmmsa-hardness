"""Exclusive top-level tools-disabled spectral manuscript/source crosswalk review."""
import run_full90_material_review_packet as runner
from prepare_spectral_manuscript_crosswalk_review import ROOT

runner.ROOT = ROOT

if __name__ == '__main__':
    runner.main()
