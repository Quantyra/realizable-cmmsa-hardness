"""Bind actual complete approved39 bytes; preserve the pending adapter unchanged."""
from pathlib import Path
import full118_pending39_custody_v1 as previous
from full115_cumulative_cleanup_custody_v2 import checked_json
from custody_checks import digest

HERE=Path(__file__).resolve().parent
PREVIOUS_PIN='772913A5F2CAFBED0664D433F6E2CAD63B528D1605DA803F9265CEF05CAA5FC5'
RECEIPT=HERE/'full118-approved39-cleanup-continuation-v2/receipt.json'
RECEIPT_PIN='7DFB1421061A569CE498634C693D0FA81F5B33D7A7AD892D54FDB128B452A9A1'
AUTH_PIN='71CC39AC43A564630C1D7178CE75BA068A1A5D7C69BE8FE21A94F93C71FE6E71'
AUTH='Approve these 39 duplicates'
REPLY='call_6f682c9366ed44459369c65368325c0a'

class Authorized39Custody(previous.Pending39Custody):
    def documents(self):
        if digest(Path(previous.__file__))!=PREVIOUS_PIN:
            raise ValueError('Frozen prior custody preparation changed')
        approved,receipt=super().documents()
        authorization=checked_json(self.actual.path.parent/'authorization.json',AUTH_PIN)
        if (self.actual.authorization!=AUTH or receipt['authorization']!=AUTH or
                receipt.get('authorization_sha256')!=AUTH_PIN or
                authorization.get('authorization')!=AUTH or authorization.get('reply_reference')!=REPLY or
                authorization.get('authorization_received') is not True or
                authorization.get('approved_plan_sha256')!=previous.PLAN_PIN or
                authorization.get('scope_count')!=39 or authorization.get('scope_bytes')!=509908701 or
                receipt.get('count')!=39 or receipt.get('total_bytes')!=509908701 or
                receipt.get('all_retained_originals_and_members_verified_after') is not True or
                any(r.get('native_remove_exit')!=0 for r in receipt['files'])):
            raise ValueError('Actual exact authorization, complete cleanup and receipt required')
        checked_json(self.actual.path.parent/'approved-plan.json',previous.PLAN_PIN)
        return approved,receipt

def configured_guard():
    return Authorized39Custody(previous.ActualReceipt(RECEIPT,RECEIPT_PIN,AUTH))

def activate():
    guard=configured_guard();guard.documents()
    if previous.custody_checks.verify_local_custody is not previous.ORIGINAL:
        raise ValueError('Another custody adapter is already installed')
    previous.custody_checks.verify_local_custody=guard.reconcile
    return guard
