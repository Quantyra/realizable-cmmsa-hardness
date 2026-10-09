"""One top-level tools-disabled Full100 conditional integration review."""
import run_full90_material_review_packet as runner
from full100_consumption_v2_controller import ROOT

runner.ROOT=ROOT/'qualification/material-integration-v1'

if __name__=='__main__':runner.main()
