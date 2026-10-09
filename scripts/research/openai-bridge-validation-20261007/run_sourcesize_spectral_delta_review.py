"""Exclusive top-level tools-disabled v2 consumer delta review."""
import run_full90_material_review_packet as runner
from prepare_sourcesize_spectral_delta_review import ROOT
runner.ROOT = ROOT
if __name__ == '__main__':
    runner.main()
