#!/usr/bin/env python3
"""Check Markdown math delimiters and links; browser layout must be checked separately."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]


def expressions(text):
    blocks = re.findall(r'^```math\n(.*?)^```', text, re.M | re.S)
    plain = re.sub(r'^```[\s\S]*?^```', '', text, flags=re.M)
    inline = re.findall(r'\$`(.*?)`\$', plain, re.S)
    residue = re.sub(r'\$`.*?`\$', '', plain, flags=re.S)
    return blocks, inline, residue


def slug(text):
    return re.sub(r'[^\w\- ]', '', re.sub(r'[`*_]', '', text).lower()).replace(' ', '-')


def main():
    paths = sorted([*ROOT.glob('*.md'), *(ROOT / 'docs').glob('*.md'),
                    *(ROOT / 'verification').glob('*.md')])
    errors = []
    records = []
    for path in paths:
        text = path.read_text()
        rel = str(path.relative_to(ROOT))
        blocks, inline, residue = expressions(text)
        if len(re.findall(r'^```', text, re.M)) % 2:
            errors.append([rel, 'Unpaired code fence'])
        if '$' in residue:
            errors.append([rel, 'Unprotected or unmatched math delimiter'])
        if re.search(r'\\tag\*?\{|<mlabeledtr\b', text):
            errors.append([rel, 'Use ordinary Markdown equation labels, outside the math block'])
        for expression in blocks + inline:
            if r'\operatorname' in expression:
                errors.append([rel, 'Use the supported upright math label convention'])
            # Escaped braces are literal delimiters, not TeX grouping braces.
            groups = re.sub(r'\\[{}]', '', expression)
            depth = 0
            for char in groups:
                if char == '{':
                    depth += 1
                elif char == '}':
                    depth -= 1
                if depth < 0:
                    break
            if depth != 0:
                errors.append([rel, 'Unbalanced TeX groups'])
        for url in re.findall(r'\]\(([^)]+)\)', residue):
            if re.match(r'\w+://', url):
                continue
            dest, _, fragment = url.partition('#')
            target = path.parent / dest if dest else path
            if not target.exists():
                errors.append([rel, 'Missing local link: ' + url])
            elif fragment and not re.match(r'L\d+', fragment):
                target_text = target.read_text()
                anchors = set(re.findall(r'<a id="([^"]+)"', target_text))
                anchors.update(slug(s) for s in re.findall(r'^#+ (.+)$', target_text, re.M))
                if fragment not in anchors:
                    errors.append([rel, 'Missing local anchor: ' + url])
        records.append({'file': rel, 'display_math': len(blocks), 'inline_math': len(inline),
                        'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    result = {'passed': not errors, 'files': records, 'errors': errors,
              'math_expression_count': sum(x['display_math'] + x['inline_math'] for x in records),
              'scope': 'Source delimiters, supported equation-label convention, TeX grouping, and local links. A populated math element is not evidence of correct layout; inspect the rendered GitHub page separately.'}
    (ROOT / 'verification/markdown_source_check.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
    return 0 if result['passed'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
