#!/usr/bin/env python3
"""Export a public-safe local receipt only from the completed, pinned replay."""
import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import sys

EXPECTED_BINDING_SHA256 = '2835adefa341b3e783d34bdeff4dc81d4b3357a35a500a398df81f146dcc2263'
FINAL_HEAD = '74643447f52a2df4d05cbb23f50b9e6f2959beaa'
RESULT_ID = 'gao-affine-asymmetric-20261015'
THETA = '21871/25000'
REPOSITORY = 'Gaozhongpai/QuasiRiemannTracker'
HEX64 = re.compile(r'[a-f0-9]{64}')
SOURCE_PATH = re.compile(r'(?:metadata\.json|dependencies/[a-z][a-z0-9-]{2,63}/metadata\.json|src/(?:Candidate|Submissions)/(?:[A-Za-z_][A-Za-z0-9_]*/)*[A-Za-z_][A-Za-z0-9_]*\.lean)')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def regular(path):
    require(path.is_file() and not path.is_symlink(), 'Required regular replay artifact is missing')
    return path


def digest(path):
    with regular(path).open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def read_json(path):
    raw = regular(path).read_bytes()
    require(len(raw) <= 32 * 1024 * 1024, 'JSON artifact exceeds the receipt limit')
    return raw, json.loads(raw)


def valid_hashes(values):
    return isinstance(values, dict) and all(isinstance(v, str) and HEX64.fullmatch(v) for v in values.values())


def export(work, expected, output):
    require(not output.exists() and not output.is_symlink(), 'Refusing to replace an existing public receipt')
    expected_raw, binding = read_json(expected)
    require(hashlib.sha256(expected_raw).hexdigest() == EXPECTED_BINDING_SHA256, 'Expected binding changed')
    raw, report = read_json(work / 'result.json')
    # These match the unmodified workflow result gate, with the exact final head.
    require(report.get('status') == 'PASS', 'Final replay has not passed')
    for name, value in {
        'reviewed_pr_head': FINAL_HEAD, 'source_commit': FINAL_HEAD,
        'source_repository': REPOSITORY, 'result_id': RESULT_ID, 'theta_exact': THETA,
        'targets': ['QRH.canonical_bound'], 'kernels': ['Lean default', 'nanoda', 'con-ron'],
        'sandbox_preflight': 'PASS', 'candidate_mount_preflight': 'PASS',
        'challenge_exported_before_candidate_execution': True, 'receipt_outside_candidate': True,
    }.items():
        require(report.get(name) == value, 'Final replay identity or acceptance gate mismatch: ' + name)
    require(type(report.get('judge_exit_code')) is int and report['judge_exit_code'] == 0, 'Judge did not exit successfully')
    require(sorted(report.get('allowed_axioms', [])) == ['Classical.choice', 'Quot.sound', 'propext'], 'Unexpected axioms')
    verified_at = report.get('verified_at')
    require(isinstance(verified_at, str) and re.fullmatch(r'\d{4}-\d{2}-\d{2}T[\d:.]+(?:Z|[+-]\d{2}:\d{2})', verified_at), 'Invalid verification time')
    require(datetime.datetime.fromisoformat(verified_at.replace('Z', '+00:00')).tzinfo is not None, 'Missing verification timezone')
    for name in ['source_files', 'submission_trees', 'driver_sha256', 'palomar_sha256', 'tool_pins']:
        require(report.get(name) == binding[name], 'Pinned replay input mismatch: ' + name)
    require(valid_hashes(report['source_files']) and all(SOURCE_PATH.fullmatch(p) for p in report['source_files']), 'Unsafe source inventory')
    require(report['source_files'].get('metadata.json') == binding['metadata_sha256'], 'Final metadata mismatch')
    require(valid_hashes(report['tool_pins']), 'Invalid checker pins')
    require(all(re.fullmatch(r'[a-z][a-z0-9-]{2,63}', k) and re.fullmatch(r'[a-f0-9]{40}', v) for k, v in report['submission_trees'].items()), 'Invalid source trees')

    contract_raw, contract = read_json(work / 'contract.json')
    require(contract.get('head_sha') == FINAL_HEAD and contract.get('source_commit') == FINAL_HEAD, 'Wrong final contract')
    require(contract.get('repository') == REPOSITORY, 'Wrong contract repository')
    require(contract.get('manifest', {}).get('id') == RESULT_ID, 'Wrong manifest ID')
    require(contract.get('manifest', {}).get('theta') == {'numerator': '21871', 'denominator': '25000'}, 'Wrong manifest bound')
    for name in ['source_files', 'submission_trees', 'generated_files']:
        require(contract.get(name) == binding[name], 'Contract binding mismatch: ' + name)
    artifacts = report.get('artifacts')
    require(isinstance(artifacts, dict), 'Missing artifact hashes')

    def artifact(name):
        actual = digest(work / name)
        require(HEX64.fullmatch(artifacts.get(name, '')) is not None and actual == artifacts[name], 'Replay artifact changed: ' + name)
        return actual

    require(artifact('contract.json') == hashlib.sha256(contract_raw).hexdigest(), 'Contract changed during checking')
    exports = {name: artifact('exports/' + name + '.export') for name in ['Challenge', 'Solution']}
    judge_hash = artifact('logs/judge.log')
    transcript = regular(work / 'logs/judge.log').read_text()
    require('Your solution is okay!' in transcript, 'Missing canonical acceptance marker')
    require(all(k + ' kernel accepts the solution' in transcript for k in ['Lean default', 'nanoda', 'con-ron']), 'Missing kernel acceptance marker')
    phase_hash = artifact('phases.json')
    _, phases = read_json(work / 'phases.json')
    require(isinstance(phases, list) and phases and phases[-1].get('phase') == 'accepted', 'Replay has not reached its final accepted phase')
    for name, value in report['source_files'].items():
        require(digest(work / 'source' / name) == value, 'Final source changed')
    for name, value in binding['generated_files'].items():
        directory = 'challenge-src' if name == 'Challenge.lean' else 'solution-src'
        require(artifact(directory + '/' + name) == value, 'Generated canonical wrapper changed')
    require(digest(work / 'result.json') == hashlib.sha256(raw).hexdigest(), 'Raw result changed during checking')

    # Explicit whitelist: never serialize a profile, libraries, raw log, tool path,
    # build-cache URL, or arbitrary report/artifact field.
    public = {
        'schema_version': 1, 'kind': 'local-standard-replay', 'status': 'PASS',
        'tracker_admission': 'PENDING',
        'meaning': 'Local canonical proof acceptance; official tracker admission remains pending.',
        'verified_at': verified_at, 'result_id': RESULT_ID, 'theta_exact': THETA,
        'source_repository': REPOSITORY, 'reviewed_pr_head': FINAL_HEAD, 'source_commit': FINAL_HEAD,
        'targets': ['QRH.canonical_bound'], 'allowed_axioms': sorted(report['allowed_axioms']),
        'kernels': report['kernels'], 'judge_exit_code': 0,
        'sandbox_preflight': 'PASS', 'candidate_mount_preflight': 'PASS',
        'challenge_exported_before_candidate_execution': True, 'receipt_outside_candidate': True,
        'metadata_sha256': binding['metadata_sha256'],
        'official_policy_commit': binding['official_policy_commit'], 'policy_sha256': binding['policy_sha256'],
        'driver_sha256': report['driver_sha256'], 'palomar_sha256': report['palomar_sha256'],
        'tool_pins': report['tool_pins'], 'source_files': report['source_files'],
        'submission_trees': report['submission_trees'], 'generated_files': binding['generated_files'],
        'challenge_export_sha256': exports['Challenge'], 'solution_export_sha256': exports['Solution'],
        'judge_transcript_sha256': judge_hash, 'phases_sha256': phase_hash,
        'raw_result_sha256': hashlib.sha256(raw).hexdigest(),
    }
    serialized = json.dumps(public, indent=2) + '\n'
    require(not re.search(r'/(?:mnt|home|tmp|var|run)/|(?:file|ssh):/{2}|[A-Za-z]:\\', serialized), 'Private path detected in public receipt')
    with output.open('x') as stream:
        stream.write(serialized)
    return hashlib.sha256(serialized.encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work', type=Path, required=True, help='Completed final replay directory (read only)')
    parser.add_argument('--expected', type=Path, default=Path(__file__).with_name('expected-verification.json'))
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('public-receipt.json'))
    args = parser.parse_args()
    try:
        value = export(args.work, args.expected, args.output)
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('Receipt not generated: ' + str(error), file=sys.stderr)
        return 1
    print('Public local-proof receipt generated; tracker admission remains pending. SHA256 ' + value)
    return 0


if __name__ == '__main__':
    sys.exit(main())
