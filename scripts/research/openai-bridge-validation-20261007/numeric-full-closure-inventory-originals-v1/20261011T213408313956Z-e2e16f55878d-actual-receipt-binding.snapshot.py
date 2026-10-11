"""Bind the two completed cleanups to actual pinned authorization receipts."""
from pathlib import Path
import full115_cumulative_cleanup_custody_v2 as custody

HERE = Path(__file__).resolve().parent
ADDITIONAL_PATH = HERE / 'full115-authorized-additional18-cleanup-20261011T1931573414476Z/receipt.json'
ADDITIONAL_PIN = '159FE07B28362140A6040510C963A94A5BEB061C2F69377654D70BFFACA67968'
ADDITIONAL_AUTHORIZATION = 'Approve the additional 18 files'


def configured_guard():
    return custody.CumulativeCustody(custody.AdditionalReceipt(
        ADDITIONAL_PATH, ADDITIONAL_PIN, ADDITIONAL_AUTHORIZATION))


def activate():
    return custody.activate(custody.AdditionalReceipt(
        ADDITIONAL_PATH, ADDITIONAL_PIN, ADDITIONAL_AUTHORIZATION))
