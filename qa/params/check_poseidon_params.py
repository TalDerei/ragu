"""Check committed Poseidon tables against the Grain generator that produced them.

Run with no arguments to check every table this repository ships, plus the
halo2 tables the port is calibrated against:

    python3 tools/check_poseidon_params.py [--halo2-dir DIR] [--ragu-dir DIR]

The halo2 pass is a self-test of the port, not a check of this repository: those
constants are deployed Orchard consensus parameters, so reproducing them is
evidence that the port matches the reference script. The ragu pass is the real
check.
"""

import argparse
import re
import sys
from pathlib import Path

from poseidon_params import PALLAS_BASE, VESTA_BASE, generate

FROM_RAW = re.compile(
    r"from_raw\(\[\s*((?:0x[0-9a-fA-F_]+,\s*){4})\]\)", re.MULTILINE
)
HEX_LITERAL = re.compile(r"(?:fp|fq)!\(0x([0-9a-fA-F]{64})\)")


def parse_halo2(path, t):
    """ROUND_CONSTANTS and MDS from a halo2_poseidon fp.rs / fq.rs."""
    text = path.read_text()
    values = []
    for match in FROM_RAW.finditer(text):
        limbs = [int(x.replace("_", ""), 16) for x in match.group(1).split(",") if x.strip()]
        values.append(sum(limb << (64 * i) for i, limb in enumerate(limbs)))
    rounds = 64
    rc_flat, rest = values[: rounds * t], values[rounds * t :]
    round_constants = [rc_flat[r * t : (r + 1) * t] for r in range(rounds)]
    mds = [rest[i * t : (i + 1) * t] for i in range(t)]  # MDS_INV follows, ignored
    return round_constants, mds


def parse_ragu(path, t):
    """ROUND_CONSTANTS and MDS_MATRIX from a ragu_pasta poseidon_f*.rs."""
    text = path.read_text()
    head, _, tail = text.partition("const MDS_MATRIX")
    rc_flat = [int(m, 16) for m in HEX_LITERAL.findall(head)]
    mds_flat = [int(m, 16) for m in HEX_LITERAL.findall(tail)]
    rounds = len(rc_flat) // t
    round_constants = [rc_flat[r * t : (r + 1) * t] for r in range(rounds)]
    mds = [mds_flat[i * t : (i + 1) * t] for i in range(t)]
    return round_constants, mds


def check(label, expected_rc, expected_mds, t, r_f, r_p, p):
    actual_rc, actual_mds = generate(t=t, r_f=r_f, r_p=r_p, p=p)
    ok = True

    if len(actual_rc) != len(expected_rc):
        print(f"  {label}: round count {len(expected_rc)} != generated {len(actual_rc)}")
        ok = False
    else:
        bad = [r for r in range(len(actual_rc)) if actual_rc[r] != expected_rc[r]]
        if bad:
            r = bad[0]
            print(f"  {label}: round constants differ in {len(bad)} round(s); first is round {r}")
            print(f"    committed {[hex(v) for v in expected_rc[r]]}")
            print(f"    generated {[hex(v) for v in actual_rc[r]]}")
            ok = False
        else:
            print(f"  {label}: {len(actual_rc) * t} round constants reproduced")

    if actual_mds == expected_mds:
        print(f"  {label}: MDS matrix reproduced (first Cauchy candidate)")
    else:
        print(f"  {label}: MDS matrix is NOT the first Cauchy candidate")
        print("    the reference resamples until its security filter accepts; confirming a")
        print("    later candidate needs the Sage script itself (algorithm_1/2/3)")
        ok = False

    return ok


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument("--halo2-dir", type=Path, default=None,
                        help="path to a halo2 checkout, for the port self-test")
    parser.add_argument("--ragu-dir", type=Path, default=here.parents[1])
    args = parser.parse_args()

    all_ok = True

    if args.halo2_dir:
        print("halo2_poseidon P128Pow5T3 (t=3), self-test of the port:")
        for name, field, p in (("fp", "Fp", PALLAS_BASE), ("fq", "Fq", VESTA_BASE)):
            path = args.halo2_dir / "halo2_poseidon" / "src" / f"{name}.rs"
            if not path.exists():
                print(f"  {field}: {path} not found, skipped")
                continue
            rc, mds = parse_halo2(path, 3)
            all_ok &= check(field, rc, mds, t=3, r_f=8, r_p=56, p=p)

    print("ragu_pasta (t=5):")
    for name, field, p in (("poseidon_fp", "Fp", PALLAS_BASE), ("poseidon_fq", "Fq", VESTA_BASE)):
        path = args.ragu_dir / "crates" / "ragu_pasta" / "src" / f"{name}.rs"
        rc, mds = parse_ragu(path, 5)
        all_ok &= check(field, rc, mds, t=5, r_f=8, r_p=56, p=p)

    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
