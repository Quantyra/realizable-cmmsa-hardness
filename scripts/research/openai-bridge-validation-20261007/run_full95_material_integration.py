"""Exclusive full Full95 integration review; original provider runner unchanged."""
from pathlib import Path
import run_full90_material_review_packet as runner
from prepare_builder02_full95 import OUTPUT
runner.ROOT=OUTPUT/'consumption-v1/qualification/material-integration-v1'
if __name__=='__main__':runner.main()
