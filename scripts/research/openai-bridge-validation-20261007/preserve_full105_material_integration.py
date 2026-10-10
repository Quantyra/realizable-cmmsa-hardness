"""Preserve actual Full105 review terminal/context/body evidence."""
from pathlib import Path
import preserve_full90_material_review_terminal as collector
from audit_full105_prior_review_reuse import BASE

collector.ROOT = BASE/'material-integration-v3'
collector.REPORT_DESTINATION = Path(__file__).parent/'full105-material-integration-reports'
collector.RECEIPT_SCHEMA = 'full105-independent-material-integration-terminal-v3'

if __name__ == '__main__':
    collector.main()
