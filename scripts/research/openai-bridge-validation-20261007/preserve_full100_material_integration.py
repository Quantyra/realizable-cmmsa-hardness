"""Preserve Full100 integration terminal/context and exact raw report bytes."""
from pathlib import Path
import preserve_full90_material_review_terminal as collector
from full100_consumption_v2_controller import ROOT

collector.ROOT=ROOT/'qualification/material-integration-v1'
collector.REPORT_DESTINATION=Path(__file__).parent/'full100-material-integration-reports'
collector.RECEIPT_SCHEMA='full100-independent-material-integration-terminal-v1'

if __name__=='__main__':collector.main()
