"""Preserve actual Full107 v4 review terminal/context/body evidence."""
from pathlib import Path
import preserve_full90_material_review_terminal as collector
from audit_full107_prior_review_reuse import BASE

collector.ROOT = BASE/'material-integration-v4'
collector.REPORT_DESTINATION = Path(__file__).parent/'full107-material-integration-reports-v4'
collector.RECEIPT_SCHEMA = 'full107-independent-material-integration-terminal-v4'

if __name__ == '__main__':
    collector.main()
