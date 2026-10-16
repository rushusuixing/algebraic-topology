"""Compile the published UCT audit and enforce its transitive axiom allowlist."""

from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
DECLARATIONS = (
    "UniversalCoefficient.algebraic_uct",
    "UniversalCoefficient.algebraicUCT_shortExact",
    "UniversalCoefficient.algebraicUCTSplitting",
    "UniversalCoefficient.algebraicUCTDirectSumIso",
)
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    sys.stderr.reconfigure(encoding="utf-8")
    result = subprocess.run(
        ["lake", "env", "lean", "Audit.lean"],
        cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, encoding="utf-8", errors="replace", check=False,
    )
    print(result.stdout, end="")
    if result.returncode:
        return result.returncode
    if re.search(r"\bsorryAx\b|declaration uses [`']sorry", result.stdout):
        print("Unproved dependency detected.", file=sys.stderr)
        return 1
    for name in DECLARATIONS:
        pattern = re.escape(name) + r"['’]?\s+depends on axioms:\s*\[([^\]]*)\]"
        match = re.search(pattern, result.stdout, re.S)
        if match:
            axioms = {item.strip() for item in match.group(1).split(",") if item.strip()}
        elif re.search(re.escape(name) + r"['’]?\s+does not depend on any axioms", result.stdout):
            axioms = set()
        else:
            print(f"Missing axiom report: {name}", file=sys.stderr)
            return 1
        if axioms - ALLOWED:
            print(f"Unexpected axioms in {name}: {sorted(axioms - ALLOWED)}", file=sys.stderr)
            return 1
    print("PASS: all four UCT declarations use only the standard allowed axioms.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
