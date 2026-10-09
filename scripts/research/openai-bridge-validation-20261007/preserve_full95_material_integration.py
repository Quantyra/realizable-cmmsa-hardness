"""Preserve native/provider/context-qualified Full95 integration reports."""
from pathlib import Path
import preserve_full90_material_review_terminal as collector
from prepare_builder02_full95 import OUTPUT
collector.ROOT=OUTPUT/'consumption-v1/qualification/material-integration-v1'
collector.REPORT_DESTINATION=Path(__file__).parent/'full95-material-integration-reports'
collector.RECEIPT_SCHEMA='full95-independent-material-integration-terminal-v1'
if __name__=='__main__':collector.main()
