"""Complete bounded namespaces and exact-version metadata; never GetObject."""
from safety import SOURCE, DEST, BUCKET, TARGET, PRINCIPALS, digest, iso, require

MAX_PAGES = 100
MAX_ROWS = 10000


def full_inventory(client, bucket, owner):
    args = {'Bucket': bucket, 'ExpectedBucketOwner': owner, 'MaxKeys': 1000}
    rows, markers, seen, identities = [], [], set(), set()
    for _ in range(MAX_PAGES):
        r = client.list_object_versions(**args)
        require(r.get('Name') == bucket and not r.get('Prefix'), 'INVENTORY_RESPONSE_SCOPE')
        for kind, field in [('object', 'Versions'), ('marker', 'DeleteMarkers')]:
            for v in r.get(field, []):
                pair = v['Key'], v['VersionId']
                require(pair not in identities, 'DUPLICATE_INVENTORY_ID')
                identities.add(pair)
                x = {'key': v['Key'], 'version': v['VersionId'], 'kind': kind,
                     'owner': v.get('Owner', {}).get('ID'), 'is_latest': v['IsLatest'],
                     'last_modified': v['LastModified'].isoformat()}
                if kind == 'object':
                    x.update(bytes=v['Size'], etag=v['ETag'], storage_class=v.get('StorageClass'))
                    rows.append(x)
                else:
                    markers.append(x)
        require(len(identities) <= MAX_ROWS, 'INVENTORY_BOUND')
        if r.get('IsTruncated') is False:
            break
        require(r.get('IsTruncated') is True, 'MISSING_TRUNCATION_STATE')
        token = (r.get('NextKeyMarker'), r.get('NextVersionIdMarker'))
        require(token[0] is not None and token[1] is not None and token not in seen,
                'VERSION_PAGINATION')
        seen.add(token)
        args.update(KeyMarker=token[0], VersionIdMarker=token[1])
    else:
        require(False, 'VERSION_PAGE_BOUND')
    uploads, seen = [], set()
    args = {'Bucket': bucket, 'ExpectedBucketOwner': owner, 'MaxUploads': 1000}
    for _ in range(MAX_PAGES):
        r = client.list_multipart_uploads(**args)
        require(r.get('Bucket') == bucket and not r.get('Prefix'), 'UPLOAD_RESPONSE_SCOPE')
        uploads.extend({'key': u['Key'], 'upload_id': u['UploadId'],
                        'initiated': u['Initiated'].isoformat()} for u in r.get('Uploads', []))
        require(len(uploads) <= MAX_ROWS, 'UPLOAD_BOUND')
        if r.get('IsTruncated') is False:
            break
        token = (r.get('NextKeyMarker'), r.get('NextUploadIdMarker'))
        require(r.get('IsTruncated') is True and all(token) and token not in seen,
                'UPLOAD_PAGINATION')
        seen.add(token)
        args.update(KeyMarker=token[0], UploadIdMarker=token[1])
    else:
        require(False, 'UPLOAD_PAGE_BOUND')
    return {'bucket': bucket, 'expected_owner': owner,
            'rows': sorted(rows, key=lambda x: (x['key'], x['version'])),
            'markers': sorted(markers, key=lambda x: (x['key'], x['version'])), 'uploads': uploads}


def clean_response(value):
    return {k: v for k, v in value.items() if k != 'ResponseMetadata'}


def version_metadata(client, bucket, owner, key, version):
    args = {'Bucket': bucket, 'ExpectedBucketOwner': owner, 'Key': key, 'VersionId': version}
    head = clean_response(client.head_object(**args))
    require(head.get('VersionId') == version and not head.get('DeleteMarker'), 'VERSION_HEADER')
    tags = client.get_object_tagging(**args)
    require(tags.get('VersionId') == version, 'VERSION_TAG_ID')
    acl = clean_response(client.get_object_acl(**args))
    return {'bucket': bucket, 'expected_owner': owner, 'key': key, 'version': version,
            'head': head, 'tags': sorted(tags['TagSet'], key=lambda x: (x['Key'], x['Value'])), 'acl': acl}


def bucket_continuity(client, bucket, owner):
    """Mutable drift witness, never an immutable bucket instance identifier."""
    args = {'Prefix': bucket, 'BucketRegion': 'us-east-1', 'MaxBuckets': 1000}
    seen, matches = set(), []
    for _ in range(MAX_PAGES):
        r = client.list_buckets(**args)
        require(r.get('Owner', {}).get('ID'), 'BUCKET_MARKER_OWNER_MISSING')
        for b in r.get('Buckets', []):
            require(b['Name'].startswith(bucket), 'BUCKET_MARKER_RESPONSE_SCOPE')
            if b['Name'] == bucket:
                date = b.get('CreationDate')
                require(hasattr(date, 'isoformat') and date.tzinfo is not None and
                        b.get('BucketRegion') == 'us-east-1', 'BUCKET_MARKER_MISSING')
                matches.append({'bucket': bucket, 'expected_owner': owner,
                                'canonical_owner': r['Owner']['ID'], 'region': b['BucketRegion'],
                                'creation_date': date.isoformat()})
        token = r.get('ContinuationToken')
        if not token:
            break
        require(token not in seen, 'BUCKET_MARKER_PAGINATION')
        seen.add(token); args['ContinuationToken'] = token
    else:
        require(False, 'BUCKET_MARKER_PAGE_BOUND')
    require(len(matches) <= 1, 'BUCKET_MARKER_DUPLICATE')
    return matches[0] if matches else None


def configuration(client, bucket, owner):
    args = {'Bucket': bucket, 'ExpectedBucketOwner': owner}
    operations = {
        'get_bucket_location': set(), 'get_bucket_acl': set(), 'get_bucket_versioning': set(),
        'get_public_access_block': set(), 'get_bucket_ownership_controls': {'OwnershipControlsNotFoundError'},
        'get_bucket_encryption': {'ServerSideEncryptionConfigurationNotFoundError'},
        'get_bucket_policy': {'NoSuchBucketPolicy'}, 'get_bucket_policy_status': {'NoSuchBucketPolicy'},
        'get_bucket_tagging': {'NoSuchTagSet'},
        'get_bucket_lifecycle_configuration': {'NoSuchLifecycleConfiguration'},
        'get_bucket_replication': {'ReplicationConfigurationNotFoundError'},
        'get_bucket_logging': set(), 'get_bucket_notification_configuration': set(),
        'get_bucket_website': {'NoSuchWebsiteConfiguration'}, 'get_bucket_cors': {'NoSuchCORSConfiguration'},
        'get_object_lock_configuration': {'ObjectLockConfigurationNotFoundError'},
        'get_bucket_request_payment': set(), 'get_bucket_accelerate_configuration': set(),
    }
    result = {'bucket': bucket, 'expected_owner': owner}
    for operation, absent_codes in operations.items():
        try:
            result[operation] = clean_response(getattr(client, operation)(**args))
        except Exception as e:
            code = getattr(e, 'response', {}).get('Error', {}).get('Code')
            if code not in absent_codes:
                raise
            result[operation] = {'absent': True, 'code': code}
    marker = bucket_continuity(client, bucket, owner)
    require(marker is not None and marker['canonical_owner'] == result['get_bucket_acl']['Owner']['ID'],
            'BUCKET_CONTINUITY_OWNER')
    result['bucket_continuity'] = marker
    require(result['get_bucket_location'].get('LocationConstraint') in (None, 'us-east-1'), 'REGION_DRIFT')
    require(result['get_bucket_versioning'].get('Status') == 'Enabled', 'VERSIONING_REQUIRED')
    # Other configuration is pinned exactly and needs substantive root disposition.
    return result


def compare_inventory(inv, rows, field, canonical_owner):
    require(not inv['markers'] and not inv['uploads'], 'UNACCOUNTED_MARKERS_OR_UPLOADS')
    expected = {(r['key'], r[field]): r['bytes'] for r in rows}
    actual = {(r['key'], r['version']): r['bytes'] for r in inv['rows']}
    require(actual == expected, 'UNACCOUNTED_OR_MISSING_VERSION')
    require(all(r['owner'] == canonical_owner for r in inv['rows']), 'VERSION_OWNER')


def compare_version_metadata(allowlist, metadata, configuration):
    indexed = {(m['bucket'], m['key'], m['version']): m for m in metadata}
    require(len(indexed) == len(metadata) == 410, 'METADATA_FULL205_COVERAGE')
    differences = {'VersionId': 0, 'LastModified': 0, 'ETag': 0}
    for row in allowlist['rows']:
        s = indexed[(BUCKET, row['key'], row['source_version'])]
        d = indexed[(TARGET, row['key'], row['destination_version'])]
        require(s['expected_owner'] == SOURCE and d['expected_owner'] == DEST, 'METADATA_OWNER_BOUND')
        for m, account in [(s, SOURCE), (d, DEST)]:
            canonical_owner = configuration[account]['get_bucket_acl']['Owner']['ID']
            require(m['acl']['Owner']['ID'] == canonical_owner and
                    len(m['acl']['Grants']) == 1 and
                    m['acl']['Grants'][0]['Permission'] == 'FULL_CONTROL' and
                    m['acl']['Grants'][0]['Grantee']['Type'] == 'CanonicalUser' and
                    m['acl']['Grants'][0]['Grantee']['ID'] == canonical_owner, 'OBJECT_PRIVATE_OWNER_ACL')
            require(m['head']['ContentLength'] == row['bytes'], 'EXACT_METADATA_SIZE')
        require(s['head']['ETag'] == row['source_etag'], 'SOURCE_ETAG_DRIFT')
        require(s['tags'] == d['tags'], 'TAG_PRESERVATION')
        for field in s['head'].keys() | d['head'].keys():
            if field in differences:
                differences[field] += s['head'].get(field) != d['head'].get(field)
            else:
                require(s['head'].get(field) == d['head'].get(field), 'HEADER_PRESERVATION')
    return {'versions': 205, 'headers_tags_preserved': True, 'private_owner_acls': True,
            'per_account_owner_canonical_ids': {a: configuration[a]['get_bucket_acl']['Owner']['ID']
                                                for a in (SOURCE, DEST)},
            'expected_copy_identity_differences': differences,
            'etag_is_not_a_payload_hash': True}


def observe(aws, allowlist):
    started = iso()
    identities = {account: aws.identity(account) for account in (SOURCE, DEST)}
    require(identities == PRINCIPALS, 'CURRENT_PRINCIPAL')
    configs, inventories, metadata = {}, {}, []
    for account, bucket, field in [(SOURCE, BUCKET, 'source_version'), (DEST, TARGET, 'destination_version')]:
        client = aws.client('s3', account)
        configs[account] = configuration(client, bucket, account)
        inventories[account] = full_inventory(client, bucket, account)
        canonical_owner = configs[account]['get_bucket_acl']['Owner']['ID']
        compare_inventory(inventories[account], allowlist['rows'], field, canonical_owner)
        for row in allowlist['rows']:
            m = version_metadata(client, bucket, account, row['key'], row[field])
            require(m['head']['ContentLength'] == row['bytes'], 'VERSION_SIZE')
            if account == SOURCE:
                require(m['head']['ETag'] == row['source_etag'], 'SOURCE_ETAG_DRIFT')
            metadata.append(m)
    # Closing full inventory and configuration sweeps catch drift during the long metadata loop.
    for account, bucket in [(SOURCE, BUCKET), (DEST, TARGET)]:
        require(full_inventory(aws.client('s3', account), bucket, account) == inventories[account],
                'INVENTORY_CHANGED_DURING_OBSERVATION')
        require(configuration(aws.client('s3', account), bucket, account) == configs[account],
                'CONFIGURATION_CHANGED_DURING_OBSERVATION')
    require({a: aws.identity(a) for a in (SOURCE, DEST)} == PRINCIPALS, 'CLOSING_PRINCIPAL')
    preservation = compare_version_metadata(allowlist, metadata, configs)
    return {'type': 'archive-retirement-readonly-observation-v1', 'started_at': started,
            'completed_at': iso(), 'distributed_atomicity': False, 'identities': identities,
            'configuration': configs, 'inventories': inventories, 'version_metadata': metadata,
            'metadata_preservation': preservation,
            'configuration_sha256': {a: digest(c) for a, c in configs.items()},
            'version_metadata_sha256': digest(metadata), 'object_payload_downloads': 0,
            'hash_authentication': 'not-reperformed-requires-independent-exact-scope-acceptance',
            'permission_simulation': 'NOT_RUN-source-IAM-out-of-scope-now',
            'cloud_mutations': 0, 'source_eligibility': 'HOLD'}
