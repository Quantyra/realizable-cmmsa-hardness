"""Preserve actual terminal/model/context evidence for the scoped crosswalk."""
from pathlib import Path
import preserve_full90_material_review_terminal as collector
from prepare_spectral_manuscript_crosswalk_review import ROOT

collector.ROOT = ROOT
collector.REPORT_DESTINATION = Path(__file__).parent / 'spectral-manuscript-crosswalk-reports'
collector.RECEIPT_SCHEMA = 'spectral-manuscript-source-caller-crosswalk-terminal-v1'

if __name__ == '__main__':
    collector.main()
