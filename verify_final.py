#!/usr/bin/env python3
"""Verify the final published statement and proof replacements using the pinned Lean toolchain."""
from pathlib import Path
from collections import Counter
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys

PROJECT = Path(__file__).resolve().parent
SSD = Path('/Volumes/Hongru‘s Second Brain')
PIN = 'leanprover/lean4:v4.33.0-rc2'
EXPECTED_PINS = {
    'mathlib': '641fbd329d4ffb62bef83c51f54088469056bd36',
    'plausible': '123d15766ba49356c02ebad2a4462dfe12d79899',
    'LeanSearchClient': 'f5c090429dff3cf66cb65562526c9ea6e8edfbcb',
    'importGraph': 'bb3469a87774349fe01898d8bf2fc6a1ce6411ca',
    'proofwidgets': '222c58dad7706a6e7cae46c0edd65ea881d3ee27',
    'aesop': '7db8190085343afde2f5d2cdcc9bac719b6ec02c',
    'Qq': 'ef42f8944eaf5b6cbfbe75d1917d824c7dd6cf33',
    'batteries': '76e1c118b0700b4ceafe99532e887d6431625e1a',
    'Cli': '1319485273bf87833fa472afbcefdedecb16b45f',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
EXCLUDED = {'.lake', '.git', 'history', '__pycache__'}
RECEIPT_NAME = 'GITHUB_V2_VERIFICATION.json'
ATTEMPT_PATH = None
ATTEMPT_COMMANDS = []
DENSE = 'LogdetLean.GramHafnian.UltimateHiding.DenseScore.'
EXPECTED_ENDPOINTS = {
    DENSE + 'FriedmanMelloA1.A1_friedmanMello_matrixLaw',
    DENSE + 'A2_takagi_weyl_integration',
    DENSE + 'A3_edelmanSutton_proposition_1_2',
    'MatsumotoPaper.completedMatsumotoTheorem3',
    DENSE + 'FriedmanMelloA1.matrixLaw_external',
    DENSE + 'A2Prime_complexSymmetricTakagiWeyl_symmetricIntegration',
    'MatsumotoPaper.A4_matsumoto_theorem_3',
    'GBSHiding.uniformHiding', 'GBSHiding.normalizedHiding', 'GBSHiding.finiteHaarSmallBall',
    'UniformHiding.theorem2_1', 'UniformHiding.theorem2_1_unscaled',
    'UniformHiding.corollary2_2', 'UniformHiding.corollary2_2_s62',
    'UniformHiding.theorem3_2_route1', 'UniformHiding.theorem3_2_route1_optimized',
    'FinalHidingAudit.all_input_normalized_expanded', 'FinalHidingAudit.all_input_product_expanded',
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def current_files(pattern='*'):
    return sorted(p for p in PROJECT.rglob(pattern) if p.is_file() and
                  not any(part in EXCLUDED for part in p.relative_to(PROJECT).parts))


def source_hashes():
    return {p.relative_to(PROJECT).as_posix(): sha(p) for p in current_files('*.lean')}


def strip_lean(text):
    """Strip nested comments and strings before looking for executable admissions."""
    out = []
    i = depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; out.extend('  '); i += 2
            elif text.startswith('-/', i):
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            if text[i] == '\\' and i + 1 < len(text):
                out.extend('  '); i += 2
            elif text[i] == '"':
                string = False; out.append(' '); i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.extend(' ' * (end - i)); i = end
        elif text[i] == '"':
            string = True; out.append(' '); i += 1
        else:
            out.append(text[i]); i += 1
    require(not depth and not string, 'Unterminated Lean comment/string')
    return ''.join(out)


def check_sources():
    hashes = source_hashes()
    modules = {p.removesuffix('.lean').replace('/', '.') for p in hashes}
    roots = {m.split('.')[0] for m in modules}
    forbidden, missing = [], []
    for name in hashes:
        code = strip_lean((PROJECT / name).read_text())
        for match in re.finditer(r'\b(sorry|admit|axiom|native_decide)\b', code):
            forbidden.append({'file': name, 'line': code.count('\n', 0, match.start()) + 1,
                              'token': match[1]})
        for match in re.finditer(r'(?m)^\s*(?:public\s+)?import\s+([^\n]+)', code):
            for module in match[1].split():
                if module.split('.')[0] in roots and module not in modules:
                    missing.append({'file': name, 'import': module})
    require(not forbidden, 'Executable admissions or scientific axioms: ' + json.dumps(forbidden))
    require(not missing, 'Missing local imports: ' + json.dumps(missing))
    manifest = PROJECT / 'SOURCE_HASHES.json'
    if manifest.exists():
        records = json.loads(manifest.read_text())['files']
        listed = set()
        for item in records:
            relative = Path(item['path'])
            require(not relative.is_absolute() and '..' not in relative.parts, 'Invalid hash path')
            require(relative.as_posix() not in listed, 'Duplicate manifest path')
            listed.add(relative.as_posix())
            p = PROJECT / relative
            require(p.is_file() and not p.is_symlink() and
                    p.resolve().is_relative_to(PROJECT) and sha(p) == item['sha256'],
                    'Source hash mismatch: ' + str(relative))
        listed_lean = {name for name in listed if name.endswith('.lean') and
                       not any(part in EXCLUDED for part in Path(name).parts)}
        require(listed_lean == set(hashes), 'Manifest does not cover exactly the current Lean sources')
        require({'verify_final.py', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
                 'FinalHidingAudit.lean', 'FinalInventory.lean',
                 'verification/' + RECEIPT_NAME} <= listed,
                'Manifest omits the verifier, configuration, audits or final receipt')
    return hashes


def main():
    global ATTEMPT_PATH, ATTEMPT_COMMANDS
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sources-only', action='store_true')
    parser.add_argument('--cache', action='store_true')
    args = parser.parse_args()
    hashes = check_sources()
    if args.sources_only:
        require((PROJECT / 'SOURCE_HASHES.json').is_file(),
                'Freeze SOURCE_HASHES.json before requesting a source-integrity check')
        print(json.dumps({'status': 'source_integrity_checked', 'lean_files': len(hashes),
                          'proof_validation_performed': False}))
        return
    mount_text = subprocess.check_output(['/sbin/mount'], text=True)
    require(' on ' + str(SSD) + ' (' in mount_text, 'Connect the required Lean SSD before compiling.')
    require((PROJECT / 'lean-toolchain').read_text().strip() == PIN, 'Lean pin changed')
    lock = PROJECT / 'lake-manifest.json'
    lock_hash = sha(lock)
    configuration_hashes = {name: sha(PROJECT / name) for name in
                            ['verify_final.py', 'lakefile.toml', 'lean-toolchain']}
    packages = json.loads(lock.read_text())['packages']
    require({p['name']: p['rev'] for p in packages} == EXPECTED_PINS, 'Dependency pins changed')
    lake = PROJECT / '.lake'
    if not lake.exists() and not lake.is_symlink():
        suffix = hashlib.sha256(str(PROJECT).encode()).hexdigest()[:12]
        storage = SSD / 'lean' / ('UniformHidingFinal_20261008_' + suffix)
        (storage / 'lake').mkdir(parents=True, exist_ok=True)
        lake.symlink_to(storage / 'lake', target_is_directory=True)
    require(lake.is_symlink() and lake.resolve().is_relative_to(SSD / 'lean'),
            '.lake must be a link into a project-specific directory on the required SSD')
    storage = lake.resolve().parent
    require(storage.is_relative_to(SSD / 'lean') and storage != SSD / 'lean',
            'Use a separate project directory strictly inside the SSD lean directory')
    env = dict(os.environ, LEAN_NUM_THREADS='4')
    for key, name in [('TMPDIR', 'tmp'), ('TMP', 'tmp'), ('TEMP', 'tmp'),
                      ('MATHLIB_CACHE_DIR', 'mathlib-cache'), ('XDG_CACHE_HOME', 'cache'),
                      ('LAKE_CACHE_DIR', 'cache')]:
        (storage / name).mkdir(exist_ok=True)
        env[key] = str(storage / name)
    elan = shutil.which('elan')
    require(elan is not None, 'Reuse the installed elan toolchain')
    installed = subprocess.check_output([elan, 'toolchain', 'list'], text=True)
    require(PIN in {line.split()[0] for line in installed.splitlines() if line.split()},
            'Install the exact pinned toolchain on the SSD before running this verifier')
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    commands = []
    ATTEMPT_COMMANDS = commands
    run_directory = PROJECT / 'verification' / 'runs' / stamp
    run_directory.mkdir(parents=True)
    ATTEMPT_PATH = run_directory / 'ATTEMPT.json'
    ATTEMPT_PATH.write_text(json.dumps({'status': 'running', 'run_id': stamp,
                                      'source_hashes': hashes}, indent=2) + '\n')

    def check_storage_and_pins(require_all):
        require(' on ' + str(SSD) + ' (' in subprocess.check_output(['/sbin/mount'], text=True),
                'Required SSD disconnected')
        require(lake.resolve().is_relative_to(SSD / 'lean'), 'Build storage left required SSD')
        for key in ['TMPDIR', 'TMP', 'TEMP', 'MATHLIB_CACHE_DIR', 'XDG_CACHE_HOME', 'LAKE_CACHE_DIR']:
            require(Path(env[key]).resolve().is_relative_to(storage), 'Temporary/cache storage left project SSD directory')
        require(sha(lock) == lock_hash, 'Lockfile changed during verification')
        require(all(sha(PROJECT / name) == digest for name, digest in configuration_hashes.items()),
                'Verifier or build configuration changed during verification')
        for pkg in packages:
            p = lake / 'packages' / pkg['name']
            if not p.exists():
                require(not require_all, 'Missing dependency ' + pkg['name'])
                continue
            require(p.resolve().is_relative_to(SSD / 'lean'), 'Dependency left required SSD')
            if (p / '.lake').exists():
                require((p / '.lake').resolve().is_relative_to(SSD / 'lean'), 'Dependency cache left SSD')
            actual = subprocess.check_output(['git', '-C', str(p), 'rev-parse', 'HEAD'], text=True).strip()
            require(actual == pkg['rev'], 'Dependency revision mismatch: ' + pkg['name'])
            changes = subprocess.check_output(
                ['git', '-C', str(p), 'status', '--porcelain', '--untracked-files=no'], text=True)
            require(not changes.strip(), 'Tracked dependency sources modified: ' + pkg['name'])

    def run(label, arguments):
        check_storage_and_pins(False)
        log = storage / (label + '_' + stamp + '.log')
        command = [elan, 'run', PIN, 'lake', *arguments]
        print(json.dumps({'started': label, 'log': str(log)}), flush=True)
        with log.open('w') as stream:
            process = subprocess.run(command, cwd=PROJECT, env=env, stdout=stream, stderr=subprocess.STDOUT)
        record = {'label': label, 'command': command, 'exit_code': process.returncode,
                  'log': str(log), 'sha256': sha(log)}
        commands.append(record)
        print(json.dumps(record), flush=True)
        require(process.returncode == 0, log.read_text()[-10000:])
        check_storage_and_pins(True)
        return log.read_text()

    if args.cache:
        run('pinned_mathlib_cache', ['exe', 'cache', 'get'])
    run('named_public_build', ['build', 'UniformHiding', 'HidingVerification', 'FinalHidingAudit'])
    public = run('expanded_public_and_provider_audit', ['env', 'lean', 'FinalHidingAudit.lean'])
    require('FINAL_PUBLIC_TYPES_AND_AXIOMS_CHECKED' in public.splitlines(), 'Public audit incomplete')
    endpoints = {}
    for line in public.splitlines():
        if line.startswith('FINAL_ENDPOINT\t'):
            _, name, axioms = line.split('\t')
            endpoints[name] = [a for a in axioms.split(',') if a]
            require(set(endpoints[name]) <= ALLOWED, 'Unexpected axiom: ' + name)
    require(set(endpoints) == EXPECTED_ENDPOINTS, 'Provider/public endpoint names do not match the required set')
    inventory = run('complete_imported_local_inventory', ['env', 'lean', 'FinalInventory.lean'])
    require('FINAL_IMPORTED_THEOREM_INVENTORY_COMPLETE' in inventory.splitlines(), 'Inventory incomplete')
    proofs = []
    names = set()
    for line in inventory.splitlines():
        if line.startswith('FINAL_PROOF\t'):
            _, module, name, axioms = line.split('\t')
            require(name not in names, 'Duplicate theorem in inventory')
            names.add(name)
            ax = [a for a in axioms.split(',') if a]
            require(set(ax) <= ALLOWED, 'Unexpected scientific axiom: ' + name)
            proofs.append({'module': module, 'declaration': name, 'axioms': ax})
    require(proofs and set(endpoints) - {
        'LogdetLean.GramHafnian.UltimateHiding.DenseScore.A2_takagi_weyl_integration',
        'LogdetLean.GramHafnian.UltimateHiding.DenseScore.A2Prime_complexSymmetricTakagiWeyl_symmetricIntegration'
    } <= names, 'Public or provider Prop endpoint absent from inventory')
    require(hashes == check_sources(), 'Lean sources changed during verification')
    counts = dict(sorted(Counter(p['module'] for p in proofs).items()))
    directory = PROJECT / 'verification'
    directory.mkdir(exist_ok=True)
    frozen_delivery = (PROJECT / 'SOURCE_HASHES.json').is_file()
    if frozen_delivery:
        captured = json.loads((directory / RECEIPT_NAME).read_text())
        require(captured.get('status') == 'unconditional_uniform_hiding_verified',
                'Frozen delivery receipt does not report completed verification')
        require(captured['source_hashes'] == hashes and captured['counts_by_module'] == counts and
                captured['audited_endpoints'] == endpoints,
                'Fresh verification differs from the frozen delivered proof inventory')
        directory = run_directory
    result = {'status': 'unconditional_uniform_hiding_verified',
              'verified_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'scope': 'GitHub version 2.0 uniform hiding, all 1 <= N,K <= M, coefficient 615172; A1-A4 proved',
              'route_two_comparison_proved': False,
              'published_zenodo_source': 'https://doi.org/10.5281/zenodo.23250190',
              'lean_toolchain': PIN, 'dependency_pins': EXPECTED_PINS,
              'tracked_dependency_worktrees_clean': True,
              'ssd_mounted': True, 'generated_storage_verified': True,
              'lockfile_preserved': True, 'lockfile_sha256': lock_hash,
              'configuration_hashes': configuration_hashes,
              'commands': commands, 'audited_endpoints': endpoints,
              'scientific_axioms': 0, 'allowed_logical_foundations': sorted(ALLOWED),
              'current_lean_source_files': len(hashes),
              'compiled_theorem_declarations_audited': len(proofs),
              'compiled_modules_with_theorems': len(counts), 'counts_by_module': counts,
              'source_hashes': hashes,
              'proof_validation_is_distinct_from_archive_integrity': True}
    result['run_id'] = stamp
    result['frozen_delivery_receipt_preserved'] = frozen_delivery
    (directory / RECEIPT_NAME).write_text(json.dumps(result, indent=2) + '\n')
    (directory / 'COMPILED_THEOREM_INVENTORY.json').write_text(json.dumps(proofs, indent=2) + '\n')
    for command in commands:
        shutil.copy2(command['log'], directory / (command['label'] + '.log'))
    ATTEMPT_PATH.write_text(json.dumps({'status': 'completed', 'run_id': stamp,
                                      'receipt': str(directory / RECEIPT_NAME),
                                      'commands': commands}, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in
                      {'source_hashes', 'counts_by_module', 'audited_endpoints'}}, indent=2), flush=True)


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError, subprocess.SubprocessError, ValueError, KeyError) as error:
        if ATTEMPT_PATH is not None:
            ATTEMPT_PATH.write_text(json.dumps({'status': 'failed', 'error': str(error),
                                              'commands': ATTEMPT_COMMANDS}, indent=2) + '\n')
        print(str(error), file=sys.stderr)
        sys.exit(1)
