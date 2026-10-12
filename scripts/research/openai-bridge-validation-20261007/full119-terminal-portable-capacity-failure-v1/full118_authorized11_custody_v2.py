"""Actual approved11 binding. Prior pending adapter remains immutable."""
from pathlib import Path
import full118_pending11_custody_v1 as prior
from custody_checks import digest
H=Path(__file__).resolve().parent
PENDING_PIN='CBBAADB4F278B0E391F4974C945ADA0EECD56B3B1FBEF08749D1482CCB6E3233'
RECEIPT=H/'full118-approved11-cleanup-execution-v1/receipt.json'
RECEIPT_PIN='6688054B7AB03BB4712F034A80E6F5471950791F76DF132E857DC64218A9F6AD'
AUTH=H/'full118-approved11-actual-authorization-v1/authorization.json'
AUTH_PIN='644EADAFE8D0230567B9CCAA71320D8D7C238DDEA66DB69164280F94E49C19F0'
USER_REPLY='Approve these 11 archives'
REPLY_ID='call_4ac88b2a181a434f8e092be53ffbdda3'
def configured_guard():
 if digest(Path(prior.__file__))!=PENDING_PIN:raise ValueError('Frozen pending11 control changed')
 return prior.Pending11Custody(prior.Actual11Receipt(RECEIPT,RECEIPT_PIN,AUTH,AUTH_PIN,USER_REPLY,REPLY_ID))
def activate():
 guard=configured_guard();guard.documents()
 if prior.custody_checks.verify_local_custody is not prior.ORIGINAL:raise ValueError('Another adapter already active')
 prior.custody_checks.verify_local_custody=guard.reconcile
 return guard
