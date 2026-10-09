"""Independent tools-disabled review of exact Full100 evidence/body addendum."""
import run_full90_material_review_packet as runner
from full100_consumption_v2_controller import ROOT

runner.ROOT=ROOT/'qualification/identity-addendum-v1'

if __name__=='__main__':runner.main()
