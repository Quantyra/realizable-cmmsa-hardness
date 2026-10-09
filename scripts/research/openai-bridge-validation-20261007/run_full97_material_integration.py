"""Exclusive Full97 review using the unchanged tools-disabled provider runner."""
import run_full90_material_review_packet as runner
from prepare_builder02_full97 import OUTPUT

runner.ROOT = OUTPUT / 'consumption-v1/qualification/material-integration-v1'

if __name__ == '__main__':
    runner.main()
