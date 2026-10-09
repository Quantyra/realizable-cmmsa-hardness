"""Exclusive full-scope identity addendum; preserve original reviews."""
from pathlib import Path
import preserve_full90_material_review_terminal as runner
from prepare_builder02_full95 import OUTPUT
runner.ROOT=OUTPUT/'consumption-v1/qualification/material-integration-identity-addendum-v1'
runner.REPORT_DESTINATION=Path(__file__).parent/'full95-material-identity-addendum-reports'
runner.RECEIPT_SCHEMA='full95-identity-addendum-terminal-v1'
if __name__=='__main__':runner.main()
