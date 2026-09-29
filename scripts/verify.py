"""Check package identity, then a fresh Lake build and the final axiom reports.

Preparation tooling: the real full-source success path has not yet been run.
Uses only Python's standard library. Does not establish prize acceptance.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = 'leanprover/lean4:v4.32.2'
LEAN_COMMIT = 'f3b06c705e6c85f5314019d5d3baab0fec5b580c'
MATHLIB = '905b95818eb32af7874a58b427f50c1711a5e96c'
ROOTS = ['ForestUnimodality.Completed', 'ForestUnimodality']
THEOREMS = ['ForestUnimodality.Completed.' + name for name in (
    'rectangles_valid', 'parents_valid',
    'countIndependent_unimodal_of_isAcyclic', 'completeTarget')]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
STATEMENT = '2c848e50b9e0a3197dd5c238c17b2d726c280d76db6bf6cba7b39a68faa84883'
TEMPLATE = '83459a9fdded8370c8c6fc623a913b220ed44ee4c8d4a4a8814020ce4d9d1e78'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_path(name):
    require(re.fullmatch(r'ForestUnimodality(?:\.[A-Za-z_][A-Za-z_0-9]*)*', name),
            'Invalid project module name: ' + name)
    return Path(name.replace('.', '/') + '.lean')


def configuration():
    require((ROOT / 'lean-toolchain').read_text().strip() == TOOLCHAIN, 'Toolchain changed')
    config = tomllib.loads((ROOT / 'lakefile.toml').read_text())
    require(config['defaultTargets'] == ['ForestUnimodality'], 'Unexpected build target')
    require(config['require'] == [{'name': 'mathlib',
        'git': 'https://github.com/leanprover-community/mathlib4.git', 'rev': MATHLIB}],
        'mathlib configuration changed')
    lock = json.loads((ROOT / 'lake-manifest.json').read_text())
    deps = lock['packages']
    require(len(deps) == len({x['name'] for x in deps}) == 9, 'Expected nine dependencies')
    require(next(x['rev'] for x in deps if x['name'] == 'mathlib') == MATHLIB,
            'mathlib lock revision mismatch')
    for dep in deps:
        require(dep['type'] == 'git' and re.fullmatch(r'[0-9a-f]{40}', dep['rev']),
                'An external dependency is not pinned')
        require(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*', dep['name']), 'Unsafe dependency name')
    return deps


def check_sources(candidate=False):
    configuration()
    path = ROOT / ('verification/development-source-manifest.json' if candidate else 'verification/source-manifest.json')
    require(path.is_file(), 'NOT_READY: accepted final source manifest is absent')
    manifest = json.loads(path.read_text())
    if candidate:
        require(manifest.get('snapshot_kind') == 'unverified_development_candidate', 'Wrong candidate manifest kind')
    require(manifest['roots'] == ROOTS and manifest['source_import_complete'] is True,
            'Incomplete source package')
    order, files = manifest['module_order'], manifest['files']
    require(len(order) == len(set(order)) == len(files) and set(order) == set(files),
            'Duplicate or missing source entries')
    require(set(ROOTS + ['ForestUnimodality.Statement']) <= set(order), 'Missing final roots')
    positions = {name: i for i, name in enumerate(order)}
    for name in order:
        row = files[name]
        require(sha(ROOT / module_path(name)) == row['sha256'], 'Source changed: ' + name)
        require(all(dep in positions and positions[dep] < positions[name] for dep in row['local']),
                'Invalid dependency order: ' + name)
    found, todo = set(), ['ForestUnimodality']
    while todo:
        name = todo.pop()
        if name not in found:
            found.add(name)
            todo.extend(files[name]['local'])
    require(found == set(order), 'Manifest contains missing or unrelated project modules')
    actual = {p.relative_to(ROOT).as_posix() for p in (ROOT / 'ForestUnimodality').rglob('*.lean')}
    actual.add('ForestUnimodality.lean')
    require(actual == {module_path(n).as_posix() for n in order}, 'Project source set differs')
    require(files['ForestUnimodality.Statement']['sha256'] == STATEMENT, 'Statement changed')
    completed = (ROOT / module_path('ForestUnimodality.Completed')).read_text(encoding='utf-8')
    require(hashlib.sha256(completed.encode('utf-8')).hexdigest() == TEMPLATE,
            'Final theorem differs from reviewed template')
    require(set(manifest['configuration_sha256']) == {
        'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'checks/SubmissionCheck.lean'},
        'Configuration binding is incomplete')
    for name, digest in manifest['configuration_sha256'].items():
        require(sha(ROOT / name) == digest, 'Configuration changed: ' + name)
    return manifest


def parse_axioms(text):
    pattern = r"'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    matches = re.findall(pattern, text)
    require([name for name, _ in matches] == THEOREMS, 'Missing, extra or misnamed axiom reports')
    reports = {}
    for name, body in matches:
        axioms = {x.strip() for x in body.split(',') if x.strip()}
        require(axioms <= ALLOWED, 'Unexpected axioms in ' + name + ': ' + str(sorted(axioms)))
        reports[name] = sorted(axioms)
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-only', action='store_true')
    parser.add_argument('--candidate', action='store_true', help='Explicitly check the unverified development snapshot')
    args = parser.parse_args()
    manifest = check_sources(args.candidate)
    manifest_path = ROOT / ('verification/development-source-manifest.json' if args.candidate else 'verification/source-manifest.json')
    if args.source_only:
        print(json.dumps({'source_identity_passed': True, 'modules': len(manifest['files']),
                          'candidate': args.candidate, 'lean_executed': False, 'proof_verified': False}))
        return 0
    require(not (ROOT / '.lake/build').exists(), 'Use a fresh project build directory; existing artifacts preserved')
    env = os.environ.copy()
    for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT'):
        env.pop(key, None)
    env['LEAN_NUM_THREADS'] = '1'
    run = ROOT / 'verification/runs' / datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    run.mkdir(parents=True, exist_ok=False)
    report = {'passed': False, 'commands': [], 'source_manifest_sha256':
              sha(manifest_path), 'candidate': args.candidate, 'axiom_reports': None,
              'external_dependencies_source_rebuilt': False,
              'semantic_review_complete': False, 'organizer_acceptance': False}

    def execute(label, command):
        print(label, flush=True)
        log = run / (label + '.log')
        with log.open('wb') as stream:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
        report['commands'].append({'label': label, 'command': command,
                                   'returncode': result.returncode, 'log_sha256': sha(log)})
        require(result.returncode == 0, label + ' failed; see ' + str(log))
        return log.read_text(encoding='utf-8', errors='replace')

    try:
        for dep in configuration():
            directory = ROOT / '.lake/packages' / dep['name']
            actual = execute('revision-' + dep['name'], ['git', '-C', str(directory), 'rev-parse', 'HEAD']).strip()
            require(actual == dep['rev'], 'Wrong dependency checkout: ' + dep['name'])
            dirty = execute('clean-' + dep['name'], ['git', '-C', str(directory), 'status', '--porcelain', '--untracked-files=no'])
            require(not dirty.strip(), 'Modified tracked dependency source: ' + dep['name'])
        version = execute('lean-version', ['lake', 'env', 'lean', '--version'])
        require('version 4.32.2' in version and LEAN_COMMIT[:12] in version, 'Compiler identity mismatch')
        execute('project-build', ['lake', 'build', 'ForestUnimodality'])
        output = execute('target-axioms', ['lake', 'env', 'lean', '-Dpp.fullNames=true', 'checks/SubmissionCheck.lean'])
        report['axiom_reports'] = parse_axioms(output)
        check_sources(args.candidate)
        require(sha(manifest_path) == report['source_manifest_sha256'],
                'Source manifest changed during verification')
        report['passed'] = True
    except Exception as exc:
        report['error'] = str(exc)
        raise
    finally:
        (run / 'result.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print('PASS: source identity, fresh Lake project build and final axiom reports; semantic review remains separate')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, KeyError, OSError, StopIteration) as exc:
        print(str(exc), file=sys.stderr)
        raise SystemExit(2)
