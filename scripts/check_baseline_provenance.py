# SPDX-License-Identifier: Apache-2.0
"""Validate the exact licensed source snapshot ported from the author's baseline."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


def canonical_digest(path):
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def check_baseline_provenance():
    errors = []
    record = json.loads((ROOT / "submission/baseline-source-provenance.json").read_text(encoding="utf-8"))
    if record.get("license") != "Apache-2.0":
        errors.append("Baseline source license is not the recorded Apache-2.0 license")
    license_path = ROOT / record["licenseFile"]
    if canonical_digest(license_path) != record["licenseCanonicalLFSHA256"]:
        errors.append("Baseline license text changed")
    recorded = set()
    for item in record["sourceFiles"]:
        relative = Path(item["file"])
        if relative.is_absolute() or ".." in relative.parts or relative.parts[0] != "HadamardMultibase":
            errors.append("Invalid baseline source path: " + item["file"])
            continue
        name = relative.as_posix()
        if name in recorded:
            errors.append("Duplicate baseline source record: " + name)
        recorded.add(name)
        path = ROOT / relative
        if not path.is_file() or path.is_symlink():
            errors.append("Missing or linked baseline source: " + name)
        elif canonical_digest(path) != item["canonicalLFSHA256"]:
            errors.append("Baseline source differs from the recorded licensed snapshot: " + name)
    current = {p.relative_to(ROOT).as_posix() for p in (ROOT / "HadamardMultibase").rglob("*.lean")}
    if recorded != current:
        errors.append("Baseline source inventory differs from its provenance manifest")
    return errors


if __name__ == "__main__":
    problems = check_baseline_provenance()
    print(json.dumps({"errors": problems, "licensedSourceSnapshotCurrent": not problems}, indent=2))
    raise SystemExit(bool(problems))
