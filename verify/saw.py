"""Fixed-step self-avoiding walk (SAW) counting on finite grid boxes.

Core objects for the A188148-A188155 (2D), A187164-A187170 (3D),
A188785-A188789 (4D) project: count k-step SAWs on an n x ... x n box,
summed over all starting positions (each direction of a walk counts once,
matching OEIS conventions for these entries).

Two independent methods:
  1. brute(k, dims):    direct enumeration over all start cells  -- ground truth
  2. profile(k, d, n):  window method: the number of k-step SAWs starting at a
     cell depends only on its *clipped displacement profile* (distance to each
     face of the box, capped at k).  For n >= 2k+1 the profile counts factor,
     giving a(n) as an explicit polynomial of degree d in n.

The polynomial produced by `profile` is exact for all n >= 2k+1 (see
docs/proof.md for the theorem); agreement with the conjectured OEIS formula
on the finitely many n below that threshold is checked by `brute`.
"""

from itertools import product
from functools import lru_cache


def saw_count_from(start, k, box):
    """Number of k-step SAWs starting at `start` inside `box` (list of side lengths)."""
    d = len(box)
    axes = range(d)

    def rec(pos, visited, steps):
        if steps == 0:
            return 1
        total = 0
        for a in axes:
            for delta in (-1, 1):
                q = list(pos)
                q[a] += delta
                if 0 <= q[a] < box[a]:
                    q = tuple(q)
                    if q not in visited:
                        total += rec(q, visited | {q}, steps - 1)
        return total

    return rec(tuple(start), frozenset([tuple(start)]), k)


def brute(k, box):
    """Total k-step SAWs in `box`, summed over all starting cells."""
    return sum(saw_count_from(c, k, box) for c in product(*(range(s) for s in box)))


def window_count(k, clipped):
    """SAW count for a cell with clipped profile, up to box symmetry.

    Reflecting an axis swaps (lo, hi); permuting axes permutes the pairs.
    Both are bijections on walks, so we normalize before caching.
    """
    return _window_count(k, tuple(sorted(tuple(sorted(p)) for p in clipped)))


@lru_cache(maxsize=None)
def _window_count(k, clipped):
    """SAW count for a cell whose clipped profile is `clipped`.

    `clipped` is a tuple of pairs (lo, hi): the distance from the cell to the
    lower/upper face along each axis, capped at k.  Since a k-step walk stays
    within L-infinity distance k of its start, replacing any true distance
    >= k by the cap k does not change the count: we embed the cell in a
    sufficiently large box realizing exactly these clipped distances.
    """
    box = [lo + hi + 1 for lo, hi in clipped]
    start = [lo for lo, _ in clipped]
    return saw_count_from(start, k, box)


def clip(dist, k):
    return min(dist, k)


def profile_total(k, n, d):
    """a(n) for the n^d box via the window method: O(k^d) windows, not O(n^d) cells."""
    # cells grouped by clipped profile: along each axis the clipped (lo, hi)
    # pair is (i, n-1-i) clipped; count how many i in [0, n) give each pair.
    from collections import Counter
    axis_profiles = Counter()
    for i in range(n):
        axis_profiles[(clip(i, k), clip(n - 1 - i, k))] += 1
    total = 0
    for combo in product(*[axis_profiles.items()] * d):
        pairs = tuple(p for p, _ in combo)
        mult = 1
        for _, m in combo:
            mult *= m
        total += mult * window_count(k, pairs)
    return total


def polynomial_from_profile(k, d):
    """Exact coefficients of the degree-d polynomial equal to a(n) for n >= 2k+1.

    For n >= 2k+1 every axis has exactly one cell at each clipped distance
    pair (i, k) and (k, j) for i, j < k, and n-2k cells with profile (k, k).
    So a(n) is a polynomial in (n-2k) of degree d; we recover its coefficients
    by evaluating profile_total at d+1 points >= 2k+1 and interpolating
    (Lagrange over integers -- exact rational arithmetic via fractions).
    """
    from fractions import Fraction
    xs = [2 * k + 1 + i for i in range(d + 1)]
    ys = [profile_total(k, x, d) for x in xs]
    # Lagrange interpolation -> coefficients in the monomial basis
    coeffs = [Fraction(0)] * (d + 1)
    for i, (xi, yi) in enumerate(zip(xs, ys)):
        # basis polynomial prod_{j!=i} (x - xj)/(xi - xj)
        basis = [Fraction(1)]
        denom = Fraction(1)
        for j, xj in enumerate(xs):
            if j == i:
                continue
            denom *= xi - xj
            new = [Fraction(0)] * (len(basis) + 1)
            for p, c in enumerate(basis):
                new[p] -= c * xj
                new[p + 1] += c
            basis = new
        for p, c in enumerate(basis):
            coeffs[p] += yi * c / denom
    assert all(c.denominator == 1 for c in coeffs)
    return [int(c) for c in coeffs]
