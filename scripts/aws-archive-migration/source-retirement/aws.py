"""Metadata adapter and future single-wire transport, pinned to reviewed SDK."""
from safety import SOURCE, DEST, BUCKET, PRINCIPALS, require


def no_retry(*args, **kwargs):
    return False


def guard_mutation_client(c):
    import botocore
    require(botocore.__version__ == '1.43.108', 'UNREVIEWED_SDK')
    require(c.meta.config.retries.get('total_max_attempts') == 1 and
            c._endpoint._needs_retry is no_retry, 'SINGLE_WIRE_GUARD_CHANGED')
    return c


def single_wire_client(session):
    from botocore.config import Config
    c = session.client('s3', region_name='us-east-1',
                       config=Config(connect_timeout=10, read_timeout=25,
                                     retries={'total_max_attempts': 1, 'mode': 'standard'}))
    require(callable(getattr(c._endpoint, '_needs_retry', None)), 'UNSUPPORTED_ENDPOINT')
    c._endpoint._needs_retry = no_retry
    return guard_mutation_client(c)


class AWS:
    def __init__(self):
        import boto3
        from botocore.config import Config
        self.sessions = {SOURCE: boto3.Session(profile_name='cyint-ea-prod'),
                         DEST: boto3.Session(profile_name='quantyra')}
        self.config = Config(connect_timeout=10, read_timeout=25,
                             retries={'total_max_attempts': 3, 'mode': 'standard'})
        self.cache = {}

    def client(self, service, account):
        require(service in ('s3', 'sts') and account in self.sessions, 'READ_API_SCOPE')
        key = service, account
        if key not in self.cache:
            self.cache[key] = self.sessions[account].client(service, region_name='us-east-1', config=self.config)
        return self.cache[key]

    def identity(self, account):
        r = self.client('sts', account).get_caller_identity()
        require(r['Account'] == account and r['Arn'] == PRINCIPALS[account], 'PRINCIPAL_DRIFT')
        return r['Arn']


class FutureMutator:
    """Not constructed by CLI. Integration needs fresh independent review and root gate."""
    def __init__(self, session):
        self.client = single_wire_client(session)

    def delete_version(self, row):
        return guard_mutation_client(self.client).delete_object(
            Bucket=BUCKET, ExpectedBucketOwner=SOURCE, Key=row['key'],
            VersionId=row['source_version'], IfMatch=row['source_etag'])

    def delete_bucket(self):
        return guard_mutation_client(self.client).delete_bucket(Bucket=BUCKET, ExpectedBucketOwner=SOURCE)
