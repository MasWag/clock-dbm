"""Independent check of why3find proof certificates.

For every Coma file under the given verif/ directory, require a sibling
`<name>/proof.json` whose goals are all closed: every leaf names a prover and
every tactic node has only closed children. Prints a per-module summary and
exits non-zero on any missing or open goal.
"""
import json
import pathlib
import sys


def closed(node):
    """Return (number of prover leaves, is every leaf closed)."""
    if not isinstance(node, dict):
        return 0, False
    if "prover" in node:
        return 1, True
    if "tactic" in node:
        children = node.get("children") or []
        total, ok = 0, bool(children)
        for child in children:
            n, c = closed(child)
            total += n
            ok = ok and c
        return total, ok
    return 0, False


def main(root):
    root = pathlib.Path(root)
    comas = sorted(root.rglob("*.coma"))
    if not comas:
        print(f"error: no .coma files under {root}")
        return 1
    bad, goals, leaves = 0, 0, 0
    for coma in comas:
        cert = coma.with_suffix("") / "proof.json"
        rel = coma.relative_to(root)
        if not cert.exists():
            print(f"MISSING {rel}: no {cert.relative_to(root)}")
            bad += 1
            continue
        proofs = json.loads(cert.read_text()).get("proofs", {})
        for theory, vcs in proofs.items():
            for vc, node in vcs.items():
                goals += 1
                n, ok = closed(node)
                leaves += n
                if not ok:
                    print(f"OPEN    {rel}: {theory}.{vc}")
                    bad += 1
    print(f"{len(comas)} Coma files, {goals} goals, {leaves} prover-discharged leaves, {bad} problems")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "verif"))
