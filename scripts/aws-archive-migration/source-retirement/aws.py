"""Metadata adapter and future single-wire transport, pinned to reviewed SDK."""
from safety import SOURCE, DEST, BUCKET, TARGET, PRINCIPALS, require
from urllib.parse import urlsplit

ENDPOINTS = {'s3': 'https://s3.us-east-1.amazonaws.com',
             'sts': 'https://sts.us-east-1.amazonaws.com',
             'iam': 'https://iam.amazonaws.com'}

def guard_endpoint(c, request=None):
    service = c.meta.service_model.service_name
    require(service in ENDPOINTS and c.meta.partition == 'aws' and
            c.meta.region_name == 'us-east-1' and c._request_signer._region_name == 'us-east-1' and
            c.meta.endpoint_url == ENDPOINTS[service] and
            c._endpoint.http_session._verify is True, 'PRODUCTION_ENDPOINT_DRIFT')
    if request is not None:
        u = urlsplit(request.url)
        hosts = {urlsplit(ENDPOINTS[service]).hostname}
        if service == 's3':
            hosts.update(b + '.s3.us-east-1.amazonaws.com' for b in (BUCKET, TARGET))
        auth = request.headers.get('Authorization', b'')
        if isinstance(auth, bytes):
            auth = auth.decode('ascii')
        require('/us-east-1/' + service + '/aws4_request' in auth, 'PRODUCTION_SIGNING_SCOPE_DRIFT')
        require(u.scheme == 'https' and u.hostname in hosts and u.port in (None, 443) and
                not u.username and not u.password, 'PRODUCTION_WIRE_ENDPOINT_DRIFT')
    return c

def production_client(session, service, config):
    require(config.ignore_configured_endpoint_urls is True, 'AMBIENT_ENDPOINTS_NOT_SUPPRESSED')
    c = session.client(service, region_name='us-east-1', endpoint_url=ENDPOINTS[service],
                       verify=True, config=config)
    guard_endpoint(c)
    def before_send(request, **kwargs):
        guard_endpoint(c, request)
    c.meta.events.register_last('before-send.' + service,
                               before_send,
                               unique_id='archive-official-endpoint-guard')
    return c



def no_retry(*args, **kwargs):
    return False


def guard_mutation_client(c):
    import botocore
    import boto3
    require(botocore.__version__ == boto3.__version__ == '1.43.108', 'UNREVIEWED_SDK')
    require(c.meta.config.retries.get('total_max_attempts') == 1 and
            c._endpoint._needs_retry is no_retry, 'SINGLE_WIRE_GUARD_CHANGED')
    return guard_endpoint(c)


def single_wire_client(session):
    from botocore.config import Config
    c = production_client(session, 's3',
                       Config(ignore_configured_endpoint_urls=True, s3={'addressing_style': 'virtual'},
                              connect_timeout=10, read_timeout=25,
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
        self.config = Config(ignore_configured_endpoint_urls=True, s3={'addressing_style': 'virtual'},
                              connect_timeout=10, read_timeout=25,
                             retries={'total_max_attempts': 3, 'mode': 'standard'})
        self.cache = {}

    def client(self, service, account):
        require((service in ('s3', 'sts') or (service == 'iam' and account == SOURCE))
                and account in self.sessions, 'READ_API_SCOPE')
        key = service, account
        if key not in self.cache:
            self.cache[key] = production_client(self.sessions[account], service, self.config)
        return guard_endpoint(self.cache[key])

    def identity(self, account):
        r = self.client('sts', account).get_caller_identity()
        require(r['Account'] == account and r['Arn'] == PRINCIPALS[account], 'PRINCIPAL_DRIFT')
        return r['Arn']


class Mutator:
    """Constructed lazily after root preflight. TTL/pins checked at actual send."""
    def __init__(self, session, authorize):
        self.client = single_wire_client(session)
        self.authorize = authorize
        for operation in ('DeleteObject', 'DeleteBucket'):
            self.client.meta.events.register_first('before-send.s3.' + operation, self.before_send,
                                                   unique_id='archive-root-final-wire-gate-' + operation)

    def before_send(self, request, **kwargs):
        guard_mutation_client(self.client)
        guard_endpoint(self.client, request)
        self.authorize()

    def delete_version(self, row):
        self.authorize()
        return guard_mutation_client(self.client).delete_object(
            Bucket=BUCKET, ExpectedBucketOwner=SOURCE, Key=row['key'],
            VersionId=row['source_version'], IfMatch=row['source_etag'])

    def delete_bucket(self):
        self.authorize()
        return guard_mutation_client(self.client).delete_bucket(Bucket=BUCKET, ExpectedBucketOwner=SOURCE)
