# saw-polynomials

Proofs of twenty conjectured ("empirical") formulas from the OEIS on
fixed-length self-avoiding walk counts in grid boxes, with a complete
Lean 4 formalization.

Paper: `paper/main.tex` — *Fixed-length self-avoiding walks in grid boxes
are eventually polynomial: proofs of twenty conjectured formulas from the
OEIS* (Chen-Ting Lin, 2026).

## The result

| Family | OEIS entries | Statement |
|---|---|---|
| 2D | A188148–A188155 | k-step SAWs on n×n, k = 3..10: quadratic in n |
| 3D | A187164–A187170 | n×n×n, k = 3..9: cubic in n |
| 4D | A188785–A188789 | n⁴, k = 2..6: quartic in n |

Here a *k-step walk* is a sequence of k distinct pairwise-adjacent cells
(Hardin's OEIS convention: k cells = k−1 edges, each direction counted
separately), summed over all starting positions. All twenty polynomial
formulas were conjectured by R. H. Hardin in 2011 and remained unproved.

**Theorem** (`docs/proof.md`, Section 3 of the paper): the count from a
given cell depends only on the cell's distances to the faces of the box,
clipped at k−1 (locality). Grouping cells by clipped profile shows that
for n ≥ 2k−1 the total is a polynomial in n of degree d, with
coefficients given by finitely many window enumerations. The finitely
many cases below each conjectured threshold are closed by exact
computation, and all thresholds are verified to be sharp.

## Layout

- `paper/` — LaTeX source and compiled PDF of the paper
- `docs/proof.md` — theorem and proof draft (paper skeleton)
- `docs/literature.md` — novelty check and related-work notes
- `docs/oeis-edits.md` — paste-ready OEIS entry updates (pending arXiv ID)
- `verify/` — Python verification suite (no third-party dependencies)
  - `saw.py` — brute-force and window-method (clipped-profile) engines,
    exact rational interpolation of the polynomials
  - `run_checks.py` — full verification: `python3 run_checks.py all`
    (~3 minutes)
  - `oeis_data.json` — published OEIS terms, fetched verbatim from the
    OEIS JSON API (2026-08-18)
- `lean/` — Lean 4 formalization (see below)

## Lean formalization

All twenty statements are machine-checked end to end:

- `SawProofs/Dim2.lean`, `Dim3.lean`, `Dim4.lean` — for each dimension:
  locality lemma, translation invariance, window reduction, the
  dimension-independent single-axis census (proved once in `Dim2`), the
  polynomial theorem `A_eq_poly` / `A3_eq_poly` / `A4_eq_poly`, and the
  twenty OEIS entry theorems.
- `SawProofs/Basic.lean` — an independent list-based implementation of
  the count, checked by `native_decide` against published OEIS data.

Axiom profile: the polynomial theorems depend only on Lean's standard
axioms (`propext`, `Classical.choice`, `Quot.sound`); the entry theorems
additionally use `Lean.ofReduceBool` (the standard `native_decide`
compiler trust) for the window constants and sub-threshold values.

## Reproducing the verification

On a clean Linux/macOS machine:

```bash
# 1. Install elan (Lean toolchain manager)
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none

# 2. Enter the Lean project (toolchain and mathlib revision are pinned
#    by lean-toolchain / lake-manifest.json)
cd lean

# 3. Fetch the prebuilt mathlib cache (~5.6 GB; avoids hours of compilation)
lake exe cache get

# 4. Re-verify everything from scratch (includes large enumerations;
#    expect 30-60 minutes)
lake build
```

`Build completed successfully` means all twenty theorems check. To audit
the axioms (and confirm there are no `sorry`s — any would surface as
build warnings):

```bash
echo 'import SawProofs
#print axioms SawProofs.D2.A_eq_poly
#print axioms SawProofs.D2.A188148
#print axioms SawProofs.D3.A187170
#print axioms SawProofs.D4.A188789' > /tmp/audit.lean
lake env lean /tmp/audit.lean
```

Expected: the `*_eq_poly` theorems list `[propext, Classical.choice,
Quot.sound]`; the entry theorems add `Lean.ofReduceBool`.

The Python suite: `cd verify && python3 run_checks.py all`.

## Status

- [x] Survey and selection (2026-08-18)
- [x] Window-method engine, cross-checked against brute force
- [x] All 20 conjectures verified computationally (every published OEIS
      term reproduced; exact polynomials = conjectures; threshold gaps
      closed; thresholds sharp)
- [x] Proof write-up and literature/novelty check
- [x] Lean 4 formalization of all 20 statements (2D/3D/4D)
- [x] Paper draft (6 pages, `paper/main.pdf`)
- [ ] arXiv submission (in progress)
- [ ] OEIS entry updates (pending arXiv ID)
