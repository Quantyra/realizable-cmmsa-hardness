"""Exact per-version IAM simulations, with bounded complete result validation."""
import json
from safety import SOURCE, BUCKET, PRINCIPALS, require, digest, iso
from retirement import permissions


def simulate_one(iam, action, resource, policy, version=None):
    context = [{'ContextKeyName': 'aws:SecureTransport', 'ContextKeyType': 'boolean',
                'ContextKeyValues': ['true']},
               {'ContextKeyName': 'aws:PrincipalArn', 'ContextKeyType': 'string',
                'ContextKeyValues': [PRINCIPALS[SOURCE]]}]
    if version is not None:
        context.append({'ContextKeyName': 's3:VersionId', 'ContextKeyType': 'string',
                        'ContextKeyValues': [version]})
    request = {'PolicySourceArn': PRINCIPALS[SOURCE], 'CallerArn': PRINCIPALS[SOURCE],
               'ActionNames': [action], 'ResourceArns': [resource],
               'ResourceOwner': f'arn:aws:iam::{SOURCE}:root',
               'ContextEntries': context, 'MaxItems': 1000}
    if policy is not None:
        request['ResourcePolicy'] = json.dumps(policy, separators=(',', ':'))
    response = iam.simulate_principal_policy(**request)
    require(not response.get('IsTruncated', False) and not response.get('Marker'), 'PERMISSION_TRUNCATED')
    rows = response.get('EvaluationResults', [])
    require(len(rows) == 1, 'PERMISSION_ACTION_COVERAGE')
    e = rows[0]
    require(e.get('EvalActionName') == action and e.get('EvalResourceName') == resource,
            'PERMISSION_REQUEST_SCOPE')
    require(not e.get('MissingContextValues'), 'PERMISSION_CONTEXT_MISSING')
    rr = e.get('ResourceSpecificResults', [])
    require(len(rr) == 1 and rr[0].get('EvalResourceName') == resource,
            'PERMISSION_RESOURCE_COVERAGE')
    require(not rr[0].get('MissingContextValues'), 'PERMISSION_CONTEXT_MISSING')
    require(e.get('EvalDecision') in ('allowed', 'implicitDeny', 'explicitDeny') and
            rr[0].get('EvalResourceDecision') == e['EvalDecision'], 'PERMISSION_DECISION_SCOPE')
    return {'action': action, 'resource': resource, 'version_id': version,
            'principal': PRINCIPALS[SOURCE], 'decision': e['EvalDecision'],
            'context': context, 'resource_policy_sha256': digest(policy),
            'request_id': response.get('ResponseMetadata', {}).get('RequestId')}


def evaluate(iam, allowlist, policy):
    observations = [simulate_one(iam, 's3:DeleteObjectVersion',
                    f'arn:aws:s3:::{BUCKET}/{r["key"]}', policy, r['source_version'])
                    for r in allowlist['rows']]
    observations.append(simulate_one(iam, 's3:DeleteBucket', f'arn:aws:s3:::{BUCKET}', policy))
    groups = []
    for action in ('s3:DeleteObjectVersion', 's3:DeleteBucket'):
        selected = [x for x in observations if x['action'] == action]
        resources = sorted({x['resource'] for x in selected})
        groups.append({'EvalActionName': action,
                       'EvalDecision': 'allowed' if all(x['decision'] == 'allowed' for x in selected) else 'explicitDeny',
                       'ResourceSpecificResults': [{'EvalResourceName': resource,
                           'EvalResourceDecision': 'allowed' if all(x['decision'] == 'allowed' for x in selected
                                                                   if x['resource'] == resource) else 'explicitDeny'}
                           for resource in resources]})
    # Exclude request IDs from the stable decision identity; retain them separately.
    proof = {'IsTruncated': False, 'EvaluationResults': groups,
             'version_evaluations': [{k: v for k, v in x.items() if k != 'request_id'} for x in observations]}
    return proof, observations


def require_allowed(proof, allowlist):
    permissions(proof, [f'arn:aws:s3:::{BUCKET}/{r["key"]}' for r in allowlist['rows']])
    evaluations = proof['version_evaluations']
    expected = [(r['key'], r['source_version']) for r in allowlist['rows']]
    require(len(evaluations) == len(expected) + 1 and
            [(e['resource'].removeprefix(f'arn:aws:s3:::{BUCKET}/'), e['version_id'])
             for e in evaluations[:-1]] == expected and
            all(e['decision'] == 'allowed' and e['principal'] == PRINCIPALS[SOURCE] for e in evaluations),
            'PER_VERSION_PERMISSION_COVERAGE')
    return proof
