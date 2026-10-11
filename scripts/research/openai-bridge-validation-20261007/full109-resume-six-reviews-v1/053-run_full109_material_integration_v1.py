"""One original top-level tools-disabled Full109 material review."""
import run_full90_material_review_packet as runner
from audit_full109_prior_review_reuse_v1 import BASE

runner.ROOT = BASE/'material-integration-v1'

if __name__ == '__main__':
    runner.main()
