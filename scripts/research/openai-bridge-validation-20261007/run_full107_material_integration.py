"""One top-level tools-disabled Full107 integration reviewer; no subagents."""
import run_full90_material_review_packet as runner
from audit_full107_prior_review_reuse import BASE

runner.ROOT = BASE/'material-integration-v3'

if __name__ == '__main__':
    runner.main()
