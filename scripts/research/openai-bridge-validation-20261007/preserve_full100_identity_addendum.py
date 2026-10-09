"""Retain actual terminal/provider/body evidence for every addendum lens."""
from pathlib import Path
import preserve_full90_material_review_terminal as collector
from full100_consumption_v2_controller import ROOT

collector.ROOT=ROOT/'qualification/identity-addendum-v1'
collector.REPORT_DESTINATION=Path(__file__).parent/'full100-identity-addendum-reports'
collector.RECEIPT_SCHEMA='full100-actual-body-identity-addendum-terminal-v1'

if __name__=='__main__':collector.main()
