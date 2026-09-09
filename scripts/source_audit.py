#!/usr/bin/env python3
"""Portable source/import audit. This does not run Lean or certify mathematics."""
from pathlib import Path
import hashlib
import json
import re
import sys
import os


def stripped(text):
    """Remove nested Lean comments and strings, preserving line positions."""
    out = []
    i = depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                out.extend('  ')
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif string:
            if text[i] == '\\' and i + 1 < len(text):
                out.extend('  ')
                i += 2
            elif text[i] == '"':
                string = False
                out.append(' ')
                i += 1
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out.extend('  ')
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.extend(' ' * (end - i))
            i = end
        elif text[i] == '"':
            string = True
            out.append(' ')
            i += 1
        else:
            out.append(text[i])
            i += 1
    if depth or string:
        raise ValueError('Unterminated comment or string')
    return ''.join(out)


def audit(root):
    cfg = json.loads((root / 'scripts/audit_config.json').read_text())
    paths = []
    for directory, subdirs, names in os.walk(root):
        subdirs[:] = [d for d in subdirs if d not in ['.lake', '.git']]
        paths.extend(Path(directory) / name for name in names if name.endswith('.lean'))
    paths.sort()
    sources = {str(p.relative_to(root)).removesuffix('.lean').replace('/', '.'): p for p in paths}
    graph = {}
    missing = []
    forbidden = []
    axioms = []
    hashes = {}
    for module, path in sources.items():
        rel = str(path.relative_to(root))
        hashes[rel] = hashlib.sha256(path.read_bytes()).hexdigest()
        code = stripped(path.read_text())
        imports = [m for line in code.splitlines()
                   if re.match(r'^\s*(?:public\s+)?import\s', line)
                   for m in re.sub(r'^\s*(?:public\s+)?import\s+', '', line).split()]
        local = [m for m in imports if m.split('.')[0] in cfg['local_roots']]
        graph[module] = local
        missing.extend({'module': module, 'import': m} for m in local if m not in sources)
        for match in re.finditer(r'\b(sorry|admit|unsafe|native_decide)\b', code):
            forbidden.append({'file': rel, 'line': code.count('\n', 0, match.start()) + 1,
                              'token': match[1]})
        for match in re.finditer(r'(?m)^[ \t]*(?:private[ \t]+)?axiom[ \t]+(\S+)', code):
            axioms.append({'file': rel, 'line': code.count('\n', 0, match.start()) + 1,
                           'name': match[1]})
    seen = set()
    active = set()
    cycles = []

    def visit(module, trail):
        if module in active:
            cycles.append(trail + [module])
            return
        if module in seen:
            return
        active.add(module)
        for dependency in graph.get(module, []):
            visit(dependency, trail + [module])
        active.remove(module)
        seen.add(module)

    visit('HidingVerification', [])
    unreachable = sorted(set(sources) - seen)
    actual_axioms = sorted((item['file'], item['name']) for item in axioms)
    expected_axioms = sorted((item['file'], item['name']) for item in cfg['axioms'])
    inherited = json.loads((root / 'docs/ANTICONCENTRATION_SNAPSHOT.json').read_text())['files']
    renaming = json.loads((root / 'docs/MODULE_RENAMING.json').read_text())['files']
    extension = json.loads((root / 'docs/COROLLARY22_RELEASE.json').read_text())['files']
    expected_extensions = {'HidingStatement.lean', 'UniformHiding.lean', 'HidingVerification.lean'}
    extension_errors = []
    if set(extension) != expected_extensions:
        extension_errors.append('Extension must cover exactly the three declared public Lean files')
    for rel, item in extension.items():
        if hashes.get(rel) != item['current_sha256']:
            extension_errors.append(rel + ': new source hash mismatch')
        digest = hashlib.sha256(item['baseline_text'].encode()).hexdigest()
        if digest != item['baseline_sha256']:
            extension_errors.append(rel + ': saved baseline hash mismatch')
    restoration_errors = []
    restored_hashes = {}
    for original_path, entry in renaming.items():
        current_path = entry['current_path']
        if current_path in extension:
            item = extension[current_path]
            if item['baseline_sha256'] != entry['current_sha256']:
                extension_errors.append(current_path + ': baseline differs from historical manifest')
                continue
            if original_path in inherited:
                extension_errors.append(current_path + ': companion changes are not allowed')
                continue
            restored = item['baseline_text']
        else:
            if hashes.get(current_path) != entry['current_sha256']:
                restoration_errors.append(current_path + ': unchanged source hash mismatch')
                continue
            restored = (root / current_path).read_text()
        for edit in reversed(entry['edits']):
            start = edit['start']
            if restored[start:start + len(edit['new'])] != edit['new']:
                restoration_errors.append(current_path + ': reverse edit mismatch')
                break
            restored = restored[:start] + edit['old'] + restored[start + len(edit['new']):]
        digest = hashlib.sha256(restored.encode()).hexdigest()
        restored_hashes[original_path] = digest
        if digest != entry['original_sha256']:
            restoration_errors.append(current_path + ': restored source hash mismatch')
    mapped_paths = [entry['current_path'] for entry in renaming.values()]
    renaming_coverage_matches = len(mapped_paths) == len(set(mapped_paths)) and set(mapped_paths) == set(hashes)
    changed_inherited = [rel for rel, digest in inherited.items() if restored_hashes.get(rel) != digest]
    journal_named_paths = [rel for rel in hashes if re.search(r'prl|prx|physicalreview', rel, re.I)]
    passed = not (missing or forbidden or cycles or unreachable or changed_inherited or restoration_errors or extension_errors or journal_named_paths) and actual_axioms == expected_axioms and renaming_coverage_matches
    result = {'audit_type': 'source-only', 'lean_executed_by_this_script': False,
              'passed': passed, 'module_count': len(paths),
              'inherited_module_count': len(inherited), 'missing_imports': missing,
              'forbidden_tokens': forbidden, 'project_axiom_declarations': axioms,
              'axiom_declarations_match_expected': actual_axioms == expected_axioms,
              'import_cycles': cycles, 'unreachable_modules': unreachable,
              'changed_inherited_sources': changed_inherited, 'source_sha256': hashes,
              'inherited_comparison': 'Exact original bytes restored using the recorded naming-only edits, then compared with the pinned upstream hashes.',
              'semantic_extension_files': sorted(extension),
              'semantic_extension_errors': extension_errors,
              'historical_restoration_scope': 'For three explicitly changed public files, restore the verified v1.1.0 baseline text. For all other files, restore the actual current text. Current proof correctness is checked separately by Lean.',
              'renaming_restoration_errors': restoration_errors,
              'renaming_coverage_matches': renaming_coverage_matches,
              'journal_named_lean_paths': journal_named_paths,
              'scope': 'Checks every shipped Lean source including the companion Challenge and HidingVerification; excludes dependency/build caches.'}
    target = root / 'verification/source_audit.json'
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'source_sha256'}, indent=2))
    return passed


if __name__ == '__main__':
    sys.exit(0 if audit(Path(__file__).resolve().parents[1]) else 1)
