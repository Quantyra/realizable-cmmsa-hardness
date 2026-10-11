"""Preserve actual Full109 v1 review terminal/context/body evidence."""
from pathlib import Path
import preserve_full90_material_review_terminal as collector
from audit_full109_prior_review_reuse_v1 import BASE

collector.ROOT = BASE/'material-integration-v1'
collector.REPORT_DESTINATION = Path(__file__).parent/'full109-material-integration-reports-v1'
collector.RECEIPT_SCHEMA = 'full109-independent-material-integration-terminal-v1'

if __name__ == '__main__':
    collector.main()
