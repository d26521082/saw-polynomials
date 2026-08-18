"""Verification suite for the SAW polynomial project.

Checks, in order:
  A. window method == brute force on small (k, d, n)   [sanity for Lemma 1]
  B. window method reproduces every published OEIS term
  C. exact interpolated polynomial (valid for n >= 2k+1, Theorem) equals the
     conjectured OEIS polynomial, and the window method confirms the
     conjectured smaller validity threshold n0 < 2k+1 directly.

Run:  python3 verify/run_checks.py [2d|3d|4d|small]
"""

import sys
from saw import brute, profile_total, polynomial_from_profile

# Conjectured OEIS polynomials: A-number -> (k, d, n0, coeffs low->high), a(n) for n > n0.
CONJ = {
    # 2D: A188148..A188155, k = 3..10
    "A188148": (3, 2, 1, [8, -24, 12]),
    "A188149": (4, 2, 2, [56, -100, 36]),
    "A188150": (5, 2, 3, [272, -360, 100]),
    "A188151": (6, 2, 4, [1152, -1228, 284]),
    "A188152": (7, 2, 5, [4432, -3960, 780]),
    "A188153": (8, 2, 6, [16096, -12500, 2172]),
    "A188154": (9, 2, 7, [55600, -38192, 5916]),
    "A188155": (10, 2, 8, [186528, -115548, 16268]),
    # 3D: A187164..A187170, k = 3..9
    "A187164": (3, 3, 1, [0, 24, -60, 30]),
    "A187165": (4, 3, 2, [-48, 312, -426, 150]),
    "A187166": (5, 3, 3, [-720, 2688, -2640, 726]),
    "A187167": (6, 3, 4, [-7056, 19536, -15366, 3534]),
    "A187168": (7, 3, 5, [-57312, 128832, -85380, 16926]),
    "A187169": (8, 3, 6, [-418032, 801216, -463074, 81390]),
    "A187170": (9, 3, 7, [-2833872, 4766544, -2452704, 387966]),
    # 4D: A188785..A188789, k = 2..6
    "A188785": (2, 4, 0, [0, 0, 0, -8, 8]),
    "A188786": (3, 4, 1, [0, 0, 48, -112, 56]),
    "A188787": (4, 4, 2, [0, -192, 912, -1128, 392]),
    "A188788": (5, 4, 3, [384, -4416, 11424, -9968, 2696]),
    "A188789": (6, 4, 4, [9984, -64320, 119616, -82552, 18584]),
}

# Published OEIS terms: verify/oeis_data.json, extracted verbatim from the
# OEIS JSON API responses fetched 2026-08-18 (all entries have offset 1).
import json
import os

with open(os.path.join(os.path.dirname(__file__), "oeis_data.json")) as f:
    DATA = {name: e["data"] for name, e in json.load(f).items()}


def parse(s):
    return [int(x) for x in s.split(",")]


def poly_eval(coeffs, n):
    return sum(c * n**p for p, c in enumerate(coeffs))


def check_entry(name, data_limit=None):
    # OEIS/Hardin convention: a "k-step walk" is a sequence of k distinct
    # cells (verified against the example section of A188148: 3-step walks
    # occupy 3 cells), each direction counted separately.  So the walk has
    # ke = k - 1 edges, which is what the engine counts.
    k, d, n0, conj = CONJ[name]
    ke = k - 1
    terms = parse(DATA[name])
    if data_limit:
        terms = terms[:data_limit]
    # B: window method reproduces every published term (offset 1)
    for n, want in enumerate(terms, start=1):
        got = profile_total(ke, n, d)
        assert got == want, f"{name}: a({n}) window={got} != OEIS {want}"
    # C1: exact polynomial for n >= 2*ke+1 equals conjectured polynomial
    exact = polynomial_from_profile(ke, d)
    assert exact == conj, f"{name}: exact poly {exact} != conjectured {conj}"
    # C2: conjectured threshold n0 -- verify polynomial on n0 < n <= 2*ke+1 directly
    for n in range(n0 + 1, 2 * ke + 2):
        got = profile_total(ke, n, d)
        want = poly_eval(conj, n)
        assert got == want, f"{name}: gap check fails at n={n}: {got} != {want}"
    print(f"{name}: OK  (terms 1..{len(terms)} match; exact poly == conjecture; "
          f"threshold n>{n0} verified up to n={2*ke+1})")


def check_small_brute():
    cases = [(k, [n] * d) for k in (2, 3, 4) for d in (2, 3) for n in (2, 3, 4, 5)]
    cases += [(2, [n] * 4) for n in (2, 3)] + [(5, [n] * 2) for n in (3, 6)]
    for k, box in cases:
        b = brute(k, box)
        p = profile_total(k, box[0], len(box))
        assert b == p, f"brute != window at k={k}, box={box}: {b} != {p}"
    print(f"brute == window on {len(cases)} cases: OK")


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    if which in ("small", "all"):
        check_small_brute()
    if which in ("2d", "all"):
        for name in [n for n in CONJ if CONJ[n][1] == 2]:
            check_entry(name)
    if which in ("4d", "all"):
        for name in [n for n in CONJ if CONJ[n][1] == 4]:
            check_entry(name)
    if which in ("3d", "all"):
        for name in [n for n in CONJ if CONJ[n][1] == 3]:
            check_entry(name)
    print("ALL CHECKS PASSED")
