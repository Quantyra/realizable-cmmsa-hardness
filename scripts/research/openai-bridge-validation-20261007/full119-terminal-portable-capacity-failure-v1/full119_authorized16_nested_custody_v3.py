"""Bind actual exact16 approval and complete receipt to frozen disjoint custody preparation."""
from pathlib import Path
import full119_pending16_nested_custody_v2 as prior
from custody_checks import digest
H=Path(__file__).resolve().parent
PENDING_PIN='7DBD0BA8C2DDB7854D2F4B848CF17FC3DE89CE736F9CE4EC63959001D1AAD7E9'
RECEIPT=H/'full118-approved16-cleanup-execution-v1/receipt.json'
RECEIPT_PIN='5E00210EC11EA2E09CB19E6C28013FA39B0E8961FB5E4D475DB57282D520A956'
AUTH=H/'full118-approved16-actual-authorization-v1/authorization.json'
AUTH_PIN='D048B2CD481F82DB8A09D31E93FDB17E3ACA4CB06EEBB64697F4A178109EA43C'
USER_REPLY='Approve these 16 archives'
REPLY_ID='call_PPwl1T2ItKs32BPAyMSX52py'
def configured_guard():
 if digest(Path(prior.__file__))!=PENDING_PIN:raise ValueError('Frozen pending actual16 control changed')
 return prior.Pending16Custody(prior.Actual16Evidence(RECEIPT,RECEIPT_PIN,AUTH,AUTH_PIN,USER_REPLY,REPLY_ID))
def activate():
 guard=configured_guard();guard.documents()
 if prior.custody_checks.verify_local_custody is not prior.ORIGINAL:raise ValueError('Another custody adapter already installed')
 prior.custody_checks.verify_local_custody=guard.reconcile
 return guard
