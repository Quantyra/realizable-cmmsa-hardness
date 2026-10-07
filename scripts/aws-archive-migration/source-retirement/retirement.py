"""Future execution state machine. Only injected synthetic adapters run today.

The shipped CLI never invokes this engine. No IAM, key, local archive or
destination mutation exists. Adapter integration is a separate reviewed change.
"""
from pathlib import Path
from safety import SOURCE, DEST, BUCKET, TARGET, PRINCIPALS, Journal, execution_lock, digest, iso, require


def permissions(response, resources):
    require(response.get('IsTruncated') is False, 'PERMISSION_TRUNCATED')
    expected = {'s3:DeleteObjectVersion': set(resources),
                's3:DeleteBucket': {f'arn:aws:s3:::{BUCKET}'}}
    evaluations = response.get('EvaluationResults', [])
    require(len(evaluations) == 2, 'PERMISSION_ACTION_COVERAGE')
    require({e.get('EvalActionName') for e in evaluations} == set(expected), 'PERMISSION_ACTIONS')
    for e in evaluations:
        require(e.get('EvalDecision') == 'allowed' and not e.get('MissingContextValues'), 'PERMISSION_DENIED')
        rows = e.get('ResourceSpecificResults', [])
        require(len(rows) == len(expected[e['EvalActionName']]) and
                {r['EvalResourceName'] for r in rows} == expected[e['EvalActionName']],
                'PERMISSION_RESOURCE_COVERAGE')
        require(all(r['EvalResourceDecision'] == 'allowed' and not r.get('MissingContextValues')
                    for r in rows), 'PERMISSION_RESOURCE_DENIED')
    return response


def hash_reuse_scope(allowlist, accepted):
    # A verified:true checkpoint is not this scope. Root must accept complete hash/
    # authentication evidence, exact immutable IDs and full catalog/member pins.
    scope = {'packet_sha256': allowlist['packet_sha256'], 'source': BUCKET, 'destination': TARGET,
             'rows': allowlist['rows'], 'catalogs': allowlist['catalogs'],
             'packet_artifacts': allowlist['packet_artifacts']}
    require(accepted['type'] == 'archive-independent-hash-reuse-v1' and
            accepted['reviewer_role'] == 'root-independent-verifier' and
            accepted['scope'] == scope and accepted['versions'] == 205 and
            accepted['encrypted_chunks'] == 105 and accepted['recovery_catalogs'] == 44 and
            accepted['authentication_proof_sha256'] and accepted['version_metadata_sha256'],
            'INDEPENDENT_EXACT_HASH_SCOPE_REQUIRED')
    return accepted


def run(adapter, allowlist, authorize, journal=None, execute=False):
    require(not execute or journal is not None, 'DURABLE_JOURNAL_REQUIRED')
    if journal is None:
        return _run_locked(adapter, allowlist, authorize, None, False)
    g = authorize()
    require(journal.file.parent.resolve() == Path(g['execution_state_directory']).resolve(),
            'SHARED_EXECUTION_DIRECTORY_PIN')
    with execution_lock(journal.file.parent):
        current = Journal(journal.file, journal.binding['gate_sha256'], journal.binding['allowlist_sha256'])
        require(current.events == journal.events, 'JOURNAL_CHANGED_BEFORE_LOCK')
        return _run_locked(adapter, allowlist, authorize, journal, execute)


def _run_locked(adapter, allowlist, authorize, journal=None, execute=False):
    """authorize reloads external gate/hash, committed proofs, code pins and expiry.

    adapter contract: identities, dependencies, configuration(account), permissions,
    hash_scope, source_state (None only on owned NoSuchBucket), destination_state,
    metadata(row,source_present), delete_version, delete_bucket. States must come
    from full_inventory, with canonical owner checked against accepted configuration.
    No completion cache may implement a current state method.
    """
    rows = allowlist['rows']
    require(not execute or journal is not None, 'DURABLE_JOURNAL_REQUIRED')
    if journal is not None:
        allowed = [[r['key'], r['source_version']] for r in rows]
        require(all(e['operation'] == 'bucket' or e['identity'] in allowed for e in journal.events),
                'JOURNAL_UNKNOWN_VERSION')

    def auth():
        g = authorize()
        if journal is not None:
            require(journal.binding == {'gate_sha256': g['_gate_sha256'],
                                        'allowlist_sha256': g['_allowlist_sha256']}, 'JOURNAL_GATE_BINDING')
        require(adapter.identities() == PRINCIPALS, 'CURRENT_PRINCIPAL')
        return authorize()  # Close identity latency with final local pins/expiry.

    def deps():
        auth()
        adapter.dependencies()  # Root accepted producer shutdown and dependencies.
        return auth()

    def proof():
        g = auth()
        hash_reuse_scope(allowlist, adapter.hash_scope())
        require(digest(adapter.hash_scope()) == g['hash_reuse_scope_sha256'], 'HASH_SCOPE_PIN')
        for account, name in [(SOURCE, 'source'), (DEST, 'destination')]:
            c = adapter.configuration(account)
            if c is None:
                require(account == SOURCE and journal is not None and
                        journal.find('bucket', BUCKET, 'intent'), 'UNEXPECTED_BUCKET_ABSENCE')
            else:
                require(digest(c) == g[f'{name}_configuration_sha256'], 'CONFIGURATION_DRIFT')
        p = permissions(adapter.permissions(), [f'arn:aws:s3:::{BUCKET}/{r["key"]}' for r in rows])
        require(digest(p) == g['permission_proof_sha256'], 'PERMISSION_PROOF_CHANGED')
        require(adapter.hash_scope()['version_metadata_sha256'] == g['version_metadata_sha256'],
                'METADATA_PROOF_BINDING')
        return auth()

    def state():
        source = adapter.source_state()
        destination = adapter.destination_state()
        require(not destination['markers'] and not destination['uploads'], 'DESTINATION_EXTRAS')
        expected_dest = {(r['key'], r['destination_version'], r['bytes']) for r in rows}
        require({(r['key'], r['version'], r['bytes']) for r in destination['rows']} == expected_dest and
                len(destination['rows']) == len(rows), 'DESTINATION_CUSTODY_LOST')
        if source is None:
            require(journal is not None and journal.find('bucket', BUCKET, 'intent'),
                    'UNEXPECTED_BUCKET_ABSENCE')
            present = set()
        else:
            require(journal is None or not journal.find('bucket', BUCKET, 'intent'),
                    'BUCKET_REAPPEARANCE_OR_AMBIGUOUS_DELETE')
            require(not source['markers'] and not source['uploads'], 'SOURCE_MARKERS_OR_UPLOADS')
            present = {(r['key'], r['version'], r['bytes']) for r in source['rows']}
            expected = {(r['key'], r['source_version'], r['bytes']) for r in rows}
            require(present <= expected and len(present) == len(source['rows']), 'SHARED_DATA_OR_SOURCE_DRIFT')
        for row in rows:
            identity = [row['key'], row['source_version']]
            found = (row['key'], row['source_version'], row['bytes']) in present
            intent = journal and journal.find('version', identity, 'intent')
            confirmed = journal and journal.find('version', identity, 'confirmed')
            require(found or intent, 'UNEXPECTED_VERSION_ABSENCE')
            require(not (found and confirmed), 'CONFIRMED_VERSION_REAPPEARED')
            # Fresh exact-version metadata must compare to the accepted complete
            # header/tag/ACL baseline; hashes are independently accepted scope reuse.
            adapter.metadata(row, found)
        auth()
        return source, destination, present

    deps()
    proof()
    source, destination, present = state()
    if not execute:
        deps()  # Long dependency sweep first, then close with full data observations.
        proof()
        started = iso()
        state()
        auth()
        return {'mode': 'check-only', 'started_at': started, 'completed_at': iso(),
                'distributed_atomicity': False, 'mutations': 0, 'permissions_checked': True}

    for row in rows:
        identity = [row['key'], row['source_version']]
        deps()
        proof()
        _, _, present = state()
        exists = (row['key'], row['source_version'], row['bytes']) in present
        if journal.find('version', identity, 'confirmed'):
            continue  # state() already re-observed absence and destination proof.
        if journal.find('version', identity, 'intent'):
            require(not exists, 'AMBIGUOUS_VERSION_DELETE_NO_RETRY')
            journal.append('confirmed', 'version', identity, observed_absent=True,
                           cause='readback-after-intent-not-causal-attribution')
            continue
        require(exists, 'MISSING_BEFORE_INTENT')
        auth()
        journal.append('intent', 'version', identity, destination_version=row['destination_version'])
        auth()  # Even fsync latency can cross expiry.
        try:
            reply = adapter.delete_version(row)
            require(reply.get('VersionId') == row['source_version'] and not reply.get('DeleteMarker'),
                    'UNEXPECTED_DELETE_REPLY')
        except Exception:
            # Preserve intent. Readback may establish absence but must never resend.
            pass
        _, _, present = state()
        require((row['key'], row['source_version'], row['bytes']) not in present,
                'AMBIGUOUS_VERSION_DELETE_NO_RETRY')
        journal.append('confirmed', 'version', identity, observed_absent=True)
        auth()

    deps()
    proof()
    source, _, _ = state()
    if journal.find('bucket', BUCKET, 'intent'):
        require(source is None, 'BUCKET_REAPPEARANCE_OR_AMBIGUOUS_DELETE')
    else:
        require(source is not None and not source['rows'], 'BUCKET_NOT_EMPTY')
        auth()
        journal.append('intent', 'bucket', BUCKET)
        auth()
        try:
            adapter.delete_bucket()
        except Exception:
            pass
        require(adapter.source_state() is None, 'AMBIGUOUS_BUCKET_DELETE_NO_RETRY')
        auth()
    if not journal.find('bucket', BUCKET, 'confirmed'):
        journal.append('confirmed', 'bucket', BUCKET, observed_absent=True)
    # Final dependencies/permissions/configuration BEFORE closing data observations.
    deps()
    proof()
    started = iso()
    source, destination, present = state()
    require(source is None and not present, 'SOURCE_STILL_PRESENT')
    auth()
    observation = {'started_at': started, 'completed_at': iso(), 'distributed_atomicity': False,
                   'source_bucket_absent': True, 'destination_versions': len(destination['rows']),
                   'identities': PRINCIPALS}
    journal.append('terminal', 'bucket', BUCKET, observation=observation)
    auth()  # A terminal journal event alone is never a returned success receipt.
    return {'mode': 'execute', 'observation': observation}
