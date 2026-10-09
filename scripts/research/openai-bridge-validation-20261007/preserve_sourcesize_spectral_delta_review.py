"""Preserve actual v2 delta reviewer terminal/context evidence."""
from pathlib import Path
import preserve_full90_material_review_terminal as collector
from prepare_sourcesize_spectral_delta_review import ROOT
collector.ROOT = ROOT
collector.REPORT_DESTINATION = Path(__file__).parent / 'sourcesize-spectral-delta-review-reports'
collector.RECEIPT_SCHEMA = 'sourcesize-spectral-consumer-delta-terminal-v2'
if __name__ == '__main__':
    collector.main()
