"""Preserve actual model/context/terminal evidence for exact operator review."""
from pathlib import Path
import preserve_full90_material_review_terminal as collector
from prepare_exact_spectral_operator_review import ROOT

collector.ROOT = ROOT
collector.REPORT_DESTINATION = Path(__file__).parent / 'exact-spectral-operator-reports'
collector.RECEIPT_SCHEMA = 'exact-spectral-operator-argument-terminal-v1'

if __name__ == '__main__':
    collector.main()
