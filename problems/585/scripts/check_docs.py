#!/usr/bin/env python3
"""Check current release metadata, verification counts and selected local links."""
import json
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

from source_modules import check_coverage

ROOT = Path(__file__).resolve().parent.parent
DOCUMENTS = ['README.md', 'findings/FINDINGS.md', 'findings/V0.4.md',
             'findings/V0.4-PROOF.md', 'findings/V0.4.1.md', 'literature/README.md']


def check_docs(root=ROOT, documents=DOCUMENTS):
    metadata = json.loads((root / 'scripts/release-metadata.json').read_text())
    entries = json.loads((root / 'scripts/headline-theorems.json').read_text())
    counts = {'declarations': len(entries), 'oracles': sum(bool(e['oracle']) for e in entries),
              'modules': len(check_coverage(root))}
    if metadata['verification_inventory'] != counts:
        raise ValueError('Release inventory differs from configured sources/registry')
    citation = (root / 'CITATION.cff').read_text()
    for key, expected in [('version', metadata['version']), ('date-released', metadata['date']),
                          ('repository-code', metadata['repository'])]:
        match = re.search(rf'^{key}:\s*["\']?([^"\'\n]+)["\']?\s*$', citation, re.M)
        if not match or match[1] != expected:
            raise ValueError(f'Citation {key} differs from release metadata')
    expected = (f"Current verification inventory: {counts['declarations']} registered declarations, "
                f"{counts['oracles']} whole-file oracle checks, {counts['modules']} configured custom modules.")
    readme = (root / 'README.md').read_text()
    if readme.count(expected) != 1 or readme.count('Current verification inventory:') != 1:
        raise ValueError('README current verification inventory is missing or stale')
    collection = root.parent.parent if root.parent.name == 'problems' and (root.parent.parent / 'problems.json').is_file() else root
    checked = 0
    for document in documents:
        path = root / document
        for target in re.findall(r'\[[^\]\n]*\]\(([^)\n]+)\)', path.read_text()):
            target = target.strip().strip('<>')
            parsed = urlsplit(target)
            if parsed.scheme or parsed.netloc or not parsed.path:
                continue
            dest = (path.parent / unquote(parsed.path)).resolve()
            if not dest.is_relative_to(collection.resolve()) or not dest.is_file():
                raise ValueError(f'Invalid local link in {document}: {target}')
            checked += 1
    return counts, checked


def main():
    try:
        counts, links = check_docs()
        print(f'DOCS: PASS ({counts}; {links} selected local links)')
    except (ValueError, KeyError, OSError) as error:
        print(f'DOCS: FAIL: {error}', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    sys.exit(main())
