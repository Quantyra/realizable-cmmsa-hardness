"""One original top-level Full107 v4 packet review; tools disabled, no subagents."""
import run_full90_material_review_packet as runner
from audit_full107_prior_review_reuse import BASE

runner.ROOT = BASE/'material-integration-v4'

if __name__ == '__main__':
    runner.main()
