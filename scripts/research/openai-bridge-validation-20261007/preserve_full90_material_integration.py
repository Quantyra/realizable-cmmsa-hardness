"""Separate integration-report custody with identical native/context checks."""
from pathlib import Path
import preserve_full90_material_review_terminal as collector

collector.ROOT = Path('C:/Users/dfred/.quantyra/builder02/full90-material-resource02/consumption-v1/qualification/material-integration-v1')
collector.REPORT_DESTINATION = Path(__file__).parent/'full90-material-integration-reports'
collector.RECEIPT_SCHEMA = 'full90-independent-material-integration-terminal-v1'

if __name__ == '__main__':
    collector.main()
