"""Preserve actual terminal context and report byte identities."""
from pathlib import Path
import preserve_full90_material_review_terminal as collector
from prepare_sourcesize_spectral_review import ROOT
collector.ROOT = ROOT
collector.REPORT_DESTINATION = Path(__file__).parent / 'sourcesize-spectral-review-reports'
collector.RECEIPT_SCHEMA = 'sourcesize-spectral-consumer-review-terminal-v1'
if __name__ == '__main__':
    collector.main()
