#!/usr/bin/env python3
"""Check the frozen statement and axioms of the listed proved declarations."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
# Proof holes, and the ways to skip or extend the kernel listed in the Lean reference's
# "Validating a Lean Proof".
DISALLOWED = (r"\b(?:sorry|admit|native_decide|ofReduceBool|ofReduceNat|implemented_by|extern|unsafe|axiom)\b"
              r"|decide\s*\+native|debug\.skipKernelTC")


def lean_code(text):
    """Remove comments/plain strings; reject unaudited executable interpolation."""
    result = []
    i = depth = 0
    string = False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
                result.append(" ")
            else:
                i += 1
        elif string:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                string = False
                i += 1
                result.append(" ")
            else:
                i += 1
        elif pair == "/-":
            depth = 1
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            previous = next((c for c in reversed(result) if not c.isspace()), '')
            if previous == '!':
                raise ValueError('Interpolated strings cannot be audited by the source scanner')
            string = True
            i += 1
        else:
            result.append(text[i])
            i += 1
    if depth or string:
        raise ValueError("Unterminated source comment or string")
    return "".join(result)


def parse_checks(output, names):
    """Split `#check @name` output into name -> type, with whitespace normalized."""
    types, current = {}, None
    for line in output.splitlines():
        head = next((n for n in names if line.startswith(f"@{n} :") or line.startswith(f"{n} :")), None)
        if head is not None:
            if head in types:
                raise ValueError(f"Duplicate #check output for {head}")
            current = head
            types[current] = line.split(" :", 1)[1]
        elif current is not None:
            types[current] += " " + line
        elif line.strip():
            raise ValueError(f"Unexpected text before #check output: {line}")
    missing = [n for n in names if n not in types]
    if missing:
        raise ValueError(f"No #check output for {missing}")
    return {n: " ".join(t.split()) for n, t in types.items()}


def check_sources(root=ROOT):
    if (root / 'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.33.1':
        raise ValueError('Lean toolchain pin changed')
    config = tomllib.loads((root / 'lakefile.toml').read_text())
    requirements = config.get('require', [])
    if len(requirements) != 1 or requirements[0].get('name') != 'mathlib' or requirements[0].get('rev') != '0df444a360eaa60ab8c11dca51a86af692955474':
        raise ValueError('Mathlib requirement pin changed')
    if config.get('leanOptions'):
        raise ValueError('Package proof options differ from the preserved source defaults')
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    pins = [item.get('rev') for item in manifest.get('packages', []) if item.get('name') == 'mathlib']
    if pins != ['0df444a360eaa60ab8c11dca51a86af692955474']:
        raise ValueError('Mathlib manifest pin changed')
    from source_modules import check_coverage
    sources = list(check_coverage(root).values()) + [root / "Axioms.lean"]
    identities = json.loads((root / "scripts/proof-modules.json").read_text())
    if len(identities) != 81 or len({item["module"] for item in identities}) != 81:
        raise ValueError("Expected 81 distinct registered proof modules")
    for item in identities:
        path = root / item["source"]
        if path.name != item["module"] + ".lean" or hashlib.sha256(path.read_bytes()).hexdigest() != item["sha256"]:
            raise ValueError("Frozen proof source differs: " + item["source"])
    entries = json.loads((root / "scripts/headline-theorems.json").read_text())
    expected = {(item["module"], declaration, item["sha256"]) for item in identities for declaration in item["declarations"]}
    actual = {(item["module"], item["declaration"], item["source_sha256"]) for item in entries}
    if actual != expected or len(entries) != len(actual):
        raise ValueError("Flat theorem registry differs from the source/declaration allowlist")
    for path in sources:
        if re.search(DISALLOWED, lean_code(path.read_text())):
            raise ValueError(f"Disallowed proof token in {path.relative_to(root)}")
    return len(sources)


def main():
    check_sources()
    entries = json.loads((ROOT / "scripts/headline-theorems.json").read_text())
    expected = {entry["declaration"] for entry in entries}
    if len(expected) != len(entries) or not expected:
        raise ValueError("Empty or duplicate theorem list")
    pending = [entry["declaration"] for entry in entries if not entry.get("type")]
    if pending:
        raise ValueError(f"Exact printed type registration pending: {pending}")
    printed = re.findall(r"^#print axioms (\S+)$", (ROOT / "Axioms.lean").read_text(), re.M)
    if len(printed) != len(expected) or set(printed) != expected:
        raise ValueError("Axiom driver does not match the theorem list")
    result = subprocess.run(["lake", "env", "lean", "Axioms.lean"], cwd=ROOT,
                            capture_output=True, text=True, timeout=240)
    print(result.stdout, end="")
    print(result.stderr, end="", file=sys.stderr)
    if result.returncode:
        return result.returncode
    records = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
    records += [(name, "") for name in re.findall(
        r"'([^']+)' does not depend on any axioms", result.stdout)]
    if len(records) != len(expected) or {name for name, _ in records} != expected:
        raise ValueError("Missing, duplicate, or unexpected axiom output")
    for name, axioms in records:
        bad = {x.strip() for x in axioms.split(",") if x.strip()} - ALLOWED
        if bad:
            raise ValueError(f"{name}: disallowed axioms {sorted(bad)}")
    print(f"AXIOMS: PASS ({len(expected)} proved declarations)")
    # Freeze the headline statements: each `#check @name` must print the type recorded in the list.
    imports = sorted({entry["module"] for entry in entries})
    checks = "".join(f"import {m}\n" for m in imports)
    checks += "\n/-! Audit of the frozen headline theorem statements. -/\n"
    checks += "".join(f"#check @{entry['declaration']}\n" for entry in entries)
    result = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT,
                            input=checks, capture_output=True, text=True, timeout=240)
    if result.returncode:
        print(result.stdout, end="")
        print(result.stderr, end="", file=sys.stderr)
        return result.returncode
    printed_types = parse_checks(result.stdout, [entry["declaration"] for entry in entries])
    for entry in entries:
        if " ".join(entry.get("type", "").split()) != printed_types[entry["declaration"]]:
            raise ValueError(f"{entry['declaration']}: statement differs from the recorded type")
    print(f"STATEMENTS: PASS ({len(entries)} recorded types)")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except subprocess.TimeoutExpired as error:
        print(f'AXIOMS: UNKNOWN: {error}', file=sys.stderr)
        sys.exit(124)
    except (ValueError, OSError) as error:
        print(f"AXIOMS: FAIL: {error}", file=sys.stderr)
        sys.exit(1)
