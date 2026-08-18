# Eventual polynomiality of fixed-length self-avoiding walk counts in grid boxes

**Status:** draft v1 (2026-08-18). Target: proves the conjectured formulas in
OEIS A188148–A188155 (2D), A187164–A187170 (3D), A188785–A188789 (4D).

## Setup and conventions

Fix a dimension $d \ge 1$ and let $B_n^d = \{0, 1, \dots, n-1\}^d$ be the
$n \times \cdots \times n$ grid of cells, adjacent when they differ by $\pm 1$
in exactly one coordinate. Following the convention of Hardin's OEIS entries
(confirmed against the example section of A188148), a **$k$-step walk** is a
sequence of $k$ *distinct* pairwise-adjacent cells $c_1, c_2, \dots, c_k$;
it traverses $m = k-1$ edges, and a walk and its reversal are counted
separately. Define
$$a_{k,d}(n) = \#\{\,k\text{-step self-avoiding walks in } B_n^d\,\}.$$

For a cell $c = (c^{(1)}, \dots, c^{(d)}) \in B_n^d$ let
$f_n(c)$ be the number of $k$-step walks *starting* at $c$, so
$a_{k,d}(n) = \sum_{c \in B_n^d} f_n(c)$.

## Lemma 1 (Locality / clipping)

Let $m = k - 1$ and define the **clipped profile** of $c$ as
$$\pi(c) = \big(\min(c^{(i)}, m),\; \min(n - 1 - c^{(i)}, m)\big)_{i=1}^{d}.$$
Then $f_n(c)$ depends only on $\pi(c)$ (not otherwise on $c$ or $n$).

*Proof.* A walk of $m$ edges starting at $c$ stays inside the $L^\infty$ ball
of radius $m$ around $c$; in fact along axis $i$ it stays within the interval
$[c^{(i)} - m,\, c^{(i)} + m]$. The set of cells of $B_n^d$ available to the
walk is therefore the box
$\prod_i [\,c^{(i)} - \ell_i,\; c^{(i)} + r_i\,]$ where
$\ell_i = \min(c^{(i)}, m)$ and $r_i = \min(n-1-c^{(i)}, m)$, and the count of
self-avoiding walks from $c$ inside a box depends only on the box's shape
relative to the start, i.e. on $(\ell_i, r_i)_i = \pi(c)$. Translation gives
the bijection. $\blacksquare$

For a profile $p = (\ell_i, r_i)_i$ write $w(p)$ for the common value of
$f_n(c)$ over cells of profile $p$; $w(p)$ is a finite, explicitly computable
integer (enumerate walks in the box $\prod_i \{0, \dots, \ell_i + r_i\}$
starting at $(\ell_1, \dots, \ell_d)$). By symmetry, $w$ is invariant under
swapping $\ell_i \leftrightarrow r_i$ (reflection) and permuting axes.

## Lemma 2 (Profile census)

Along one axis, the clipped pair of a coordinate $x \in \{0, \dots, n-1\}$ is
$(\min(x, m), \min(n-1-x, m))$. If $n \ge 2m + 1$, the multiset of pairs is:
each of $(0, m), (1, m), \dots, (m-1, m)$ and their mirrors exactly once, and
$(m, m)$ exactly $n - 2m$ times. Hence, grouping cells by profile,
$$a_{k,d}(n) \;=\; \sum_{p} N_n(p)\, w(p), \qquad
N_n(p) = \prod_{i=1}^{d} \nu_n(\ell_i, r_i),$$
where $\nu_n(\ell, r) = n - 2m$ if $(\ell, r) = (m, m)$, and $1$ if exactly
one of $\ell, r$ equals $m$ and the other is $< m$ (and $0$ otherwise), valid
for all $n \ge 2m + 1$.

## Theorem (Eventual polynomiality)

For $n \ge 2m + 1 = 2k - 1$,
$$a_{k,d}(n) = \sum_{j=0}^{d} \binom{d}{j} (n - 2m)^j \, W_j, \qquad
W_j = \sum_{\substack{p:\ j \text{ axes interior} \\ d - j \text{ axes boundary}}} w(p)$$
is a polynomial in $n$ of degree $d$ with leading coefficient
$w(\text{all-interior profile}) > 0$.

*Proof.* Immediate from Lemmas 1 and 2: expanding the product $N_n(p)$, the
only $n$-dependence is the factor $(n-2m)$ for each axis with interior pair
$(m, m)$. $\blacksquare$

The coefficients are determined by finitely many walk enumerations in boxes
of side $\le 2m + 1$. In `verify/saw.py`, `polynomial_from_profile` recovers
them by exact rational interpolation of $a_{k,d}$ at $d+1$ points
$n \ge 2m+1$; this is equivalent and simpler to implement than assembling the
$W_j$ directly.

## Closing the gap to the conjectured thresholds

Each OEIS entry conjectures validity of its polynomial from some threshold
$n > n_0$ with $n_0 < 2m + 1$. Since the window sum of Lemma 2 (in the
general form, with $\nu_n$ the true census of clipped pairs for the given
$n$) is valid for *every* $n \ge 1$, the finitely many remaining cases
$n_0 < n < 2m + 1$ are verified by direct exact computation
(`run_checks.py`, check C2). Below $n_0$ the polynomial genuinely fails
(boundary effects overlap), which is why the entries carry thresholds.

## Verification results (2026-08-18)

`verify/run_checks.py` confirms, for all 20 sequences:

- **A** the window method agrees with brute-force enumeration (28 cases);
- **B** it reproduces every published OEIS term (b-file-length data,
  22–43 terms per entry, fetched verbatim from the OEIS JSON API);
- **C1** the exactly-interpolated polynomial coincides with the conjectured
  formula, coefficient by coefficient;
- **C2** the conjectured threshold $n_0$ is correct: the polynomial holds on
  the full gap $n_0 < n < 2m+1$ by direct computation.

Together with the Theorem, **B + C1 + C2 constitute a complete proof of each
conjectured formula** (the enumerations are finite and reproducible; a Lean
formalization is planned to make the computational steps machine-checked).

## Remarks toward the paper

- The same theorem proves the conjectured g.f.s and linear recurrences in the
  same entries, since a degree-$d$ polynomial for $n > n_0$ is equivalent to
  a rational g.f. with denominator $(1-x)^{d+1}$ and to the recurrence
  $a(n) = \sum_{i=1}^{d+1} (-1)^{i+1} \binom{d+1}{i} a(n-i)$ for
  $n > n_0 + d + 1$.
- The argument is uniform in $d$ and $k$ and extends verbatim to: rectangular
  boxes (multivariate polynomials), king moves (A186861–A186870, partially
  proved by others), knight moves, and step-set variants — a natural
  "further results" section.
- Precedent: A186864 carries a proof by D. A. Corneth (Sep 2023) in this
  spirit for one sequence; our contribution is the uniform meta-theorem plus
  exhaustive verification across the three families (20 sequences).
