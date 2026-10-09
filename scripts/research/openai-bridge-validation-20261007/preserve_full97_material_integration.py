"""Preserve terminal/context-qualified Full97 reports for full root inspection."""
from pathlib import Path
import preserve_full90_material_review_terminal as collector
from prepare_builder02_full97 import OUTPUT

collector.ROOT = OUTPUT / 'consumption-v1/qualification/material-integration-v1'
collector.REPORT_DESTINATION = Path(__file__).parent / 'full97-material-integration-reports'
collector.RECEIPT_SCHEMA = 'full97-independent-material-integration-terminal-v1'

if __name__ == '__main__':
    collector.main()
