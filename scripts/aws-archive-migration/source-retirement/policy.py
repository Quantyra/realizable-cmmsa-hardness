"""Exact unapplied bucket policies: deny producer writes for EVERY principal."""
from safety import BUCKET, TARGET, SOURCE, PRINCIPALS

OBJECT_WRITES = ['s3:PutObject', 's3:DeleteObject', 's3:PutObjectTagging',
                 's3:DeleteObjectTagging', 's3:PutObjectVersionTagging',
                 's3:DeleteObjectVersionTagging', 's3:PutObjectAcl', 's3:PutObjectVersionAcl',
                 's3:PutObjectRetention', 's3:PutObjectLegalHold', 's3:RestoreObject',
                 's3:AbortMultipartUpload']
# S3 deletion APIs for tagging/CORS/ownership controls require their PutBucket
# IAM actions, already covered by PutBucket*. API names are not IAM actions.
CONTROL_WRITES = ['s3:PutBucket*', 's3:PutEncryptionConfiguration', 's3:PutLifecycleConfiguration',
                  's3:PutReplicationConfiguration', 's3:PutAccelerateConfiguration',
                  's3:DeleteBucketPolicy', 's3:DeleteBucketWebsite']


def tls(bucket, sid):
    return {'Sid': sid, 'Effect': 'Deny', 'Principal': '*', 'Action': 's3:*',
            'Resource': [f'arn:aws:s3:::{bucket}', f'arn:aws:s3:::{bucket}/*'],
            'Condition': {'Bool': {'aws:SecureTransport': 'false'}}}


def source_freeze():
    return {'Version': '2012-10-17', 'Statement': [tls(BUCKET, 'DenyInsecureTransport'),
        {'Sid': 'ArchiveProducerWritesDeniedForEveryone', 'Effect': 'Deny', 'Principal': '*',
         'Action': OBJECT_WRITES, 'Resource': f'arn:aws:s3:::{BUCKET}/*'},
        {'Sid': 'ArchiveControlPlaneFrozen', 'Effect': 'Deny', 'Principal': '*',
         'Action': CONTROL_WRITES, 'Resource': f'arn:aws:s3:::{BUCKET}'},
        {'Sid': 'ArchiveCleanupPinnedPrincipalOnly', 'Effect': 'Deny', 'Principal': '*',
         'Action': ['s3:DeleteObjectVersion', 's3:DeleteBucket'],
         'Resource': [f'arn:aws:s3:::{BUCKET}', f'arn:aws:s3:::{BUCKET}/*'],
         'Condition': {'ArnNotEquals': {'aws:PrincipalArn': PRINCIPALS[SOURCE]}}}]}


def destination_custody():
    return {'Version': '2012-10-17', 'Statement': [
        tls(TARGET, 'QuantyraArchiveHTTPSOnly20261007'),
        {'Sid': 'ArchiveDestinationVersionsHeld', 'Effect': 'Deny', 'Principal': '*',
         'Action': OBJECT_WRITES + ['s3:DeleteObjectVersion'], 'Resource': f'arn:aws:s3:::{TARGET}/*'},
        {'Sid': 'ArchiveDestinationControlsHeld', 'Effect': 'Deny', 'Principal': '*',
         'Action': CONTROL_WRITES + ['s3:DeleteBucket'], 'Resource': f'arn:aws:s3:::{TARGET}'}]}


def policy_value(config):
    import json
    return json.loads(config['get_bucket_policy']['Policy'])
