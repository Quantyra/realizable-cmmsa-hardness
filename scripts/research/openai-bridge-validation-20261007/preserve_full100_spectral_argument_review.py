"""Preserve exact terminal/context/coverage evidence for argument assessment."""
from pathlib import Path
import preserve_full90_material_review_terminal as collector
from full100_consumption_v2_controller import ROOT

collector.ROOT = ROOT/'spectral-argument-review-v1'
collector.REPORT_DESTINATION = Path(__file__).parent/'full100-spectral-argument-reports'
collector.RECEIPT_SCHEMA = 'full100-spectral-critical-argument-terminal-v1'

if __name__ == '__main__': collector.main()
