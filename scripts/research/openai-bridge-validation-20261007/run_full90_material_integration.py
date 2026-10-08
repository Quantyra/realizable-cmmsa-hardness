"""Exclusive complete integration review using the proven bounded CLI runner."""
from pathlib import Path
import run_full90_material_review_packet as runner

runner.ROOT = Path('C:/Users/dfred/.quantyra/builder02/full90-material-resource02/consumption-v1/qualification/material-integration-v1')

if __name__ == '__main__':
    runner.main()
