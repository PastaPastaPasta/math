#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Check the 11-line TAUT proof printed in W13 Section 6.2 against Lemmas 6.1 and 6.2.

Exact rational arithmetic (Python standard library only). The listing prints one exponent per
quantifier block. Two readings are checked:

  guess:      the printed exponent is the guess exponent (a log n block shown as n^1);
              input constraints are not printed and are taken from Lemma 6.1.
  constraint: the printed exponent is the block's input constraint (superscript);
              guess exponents are taken from Lemma 6.1.

For each reading the kernel exponents are recomputed from the rules with the b term of
Lemma 6.2(1),(2) (the input constraint of the next outer block) and without it, and compared with
the printed values. Printed values carry 9 decimals, so agreement is up to 2e-9.

Usage: python3 w13_listing.py
"""
from fractions import Fraction as F

C = F("1.419")
TOL = F(2, 10**9)
ONE = F(1)

# (blocks outermost first as (quantifier, printed exponent), kernel type, kernel exponent)
LISTING = [
    ([], "NTS", "4.788956584"),
    ([("E", "2.369956583"), ("A", "1")], "NTS", "2.419"),
    ([("E", "2.369956583"), ("A", "1"), ("E", "1.419"), ("A", "1")], "NTS", "1"),
    ([("E", "2.369956583"), ("A", "1"), ("E", "1.419"), ("A", "1")], "coNTS", "1.419"),
    ([("E", "2.369956583"), ("A", "1"), ("E", "1.419")], "NTS", "2.013561000"),
    ([("E", "2.369956583"), ("A", "1")], "coNTS", "2.857243059"),
    ([("E", "2.369956583"), ("A", "2.378351877"), ("E", "1")], "coNTS", "1.181167036"),
    ([("E", "2.369956583"), ("A", "2.378351877"), ("E", "1")], "NTS", "1.676076023"),
    ([("E", "2.369956583"), ("A", "2.378351877")], "coNTS", "2.378351877"),
    ([("E", "2.369956583")], "NTS", "3.374881314"),
    ([], "coNTS", "4.788956584"),
]
LINES = [([(q, F(v)) for q, v in bl], k, F(a)) for bl, k, a in LISTING]
MATCH = {"NTS": "E", "coNTS": "A"}


def classify(i):
    """Name the rule taking line i to line i+1 (determined by the block shapes)."""
    (bl, k, a), (bl2, k2, a2) = LINES[i], LINES[i + 1]
    if len(bl2) > len(bl):
        return "speedNew" if len(bl2) == len(bl) + 2 else "speedMerge"
    if len(bl2) == len(bl):
        return "flip"
    return "pop"


def derive(reading):
    """Fill in the unprinted value of every block from the rules: returns per line a list of
    (quantifier, guess, constraint) and a list of notes on non-tight printed values."""
    full, notes = [], []
    prev = []
    for i, (bl, k, a) in enumerate(LINES):
        if i == 0:
            full.append([])
            continue
        rule = classify(i - 1)
        pk = LINES[i - 1][2]
        if rule == "speedNew":
            b = prev[-1][2] if prev else ONE
            x = pk - a
            new = [(bl[-2][0], x, max(b, x)), (bl[-1][0], F(0), b)]
            cur = prev + new
        elif rule == "speedMerge":
            u = prev[-1]
            x = pk - a
            cur = prev[:-1] + [(u[0], max(u[1], x), max(u[2], x)), (bl[-1][0], F(0), u[2])]
        elif rule == "flip":
            cur = list(prev)
        else:
            cur = prev[:-1]
        for j, (q, printed) in enumerate(bl):
            q0, g, o = cur[j]
            exact = g if reading == "guess" else o
            shown = max(exact, ONE) if reading == "guess" else exact
            if abs(printed - shown) > TOL:
                if printed > shown:
                    notes.append(f"line {i}, block {j + 1}: printed {float(printed):.9f} > rule value "
                                 f"{float(exact):.9f} (non-tight, allowed by the LP form)")
                    cur[j] = (q0, printed, o) if reading == "guess" else (q0, g, printed)
                else:
                    notes.append(f"line {i}, block {j + 1}: printed {float(printed):.9f} < rule value "
                                 f"{float(exact):.9f} (violates the rule)")
        full.append(cur)
        prev = cur
    return full, notes


def check(reading, with_b):
    full, notes = derive(reading)
    bad = []
    for i in range(len(LINES) - 1):
        rule = classify(i)
        _, k, a = LINES[i]
        a_next = LINES[i + 1][2]
        blocks = full[i]
        if rule in ("speedNew", "speedMerge"):
            continue
        u = blocks[-1]
        if rule == "flip":
            pred = C * max(a, u[2])
        else:
            b = (blocks[-2][2] if len(blocks) >= 2 else ONE) if with_b else F(0)
            pred = C * max(u[1], a, u[2], b)
        if abs(pred - a_next) > TOL:
            bad.append(f"step {i}->{i + 1} ({rule}): rules give {float(pred):.9f}, "
                       f"printed {float(a_next):.9f}")
    return notes, bad


def main():
    print(f"c = {C}")
    for i in range(len(LINES) - 1):
        print(f"  step {i}->{i + 1}: {classify(i)}")
    for reading in ("guess", "constraint"):
        for with_b in (True, False):
            notes, bad = check(reading, with_b)
            tag = "with b term" if with_b else "without b term"
            verdict = "consistent" if not bad else "INCONSISTENT"
            print(f"\nreading '{reading}', {tag}: {verdict}")
            for n in notes:
                print("  note:", n)
            for b in bad:
                print("  mismatch:", b)


if __name__ == "__main__":
    main()
