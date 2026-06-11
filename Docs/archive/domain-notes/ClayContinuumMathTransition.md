# Clay Continuum Math Transition

This document is the current compressed Clay-facing state after the scale-graph barrier algebra has been separated from its analytic inhabitants.

The repository is no longer looking for the grammar. The grammar is recorded. The remaining work is continuum mathematics.

## What The Repository Has Built

DASHI is now a precision fault-localisation ledger. It has separated the
shared scale-graph barrier algebra from the continuum mathematics that would
be needed for Clay-facing promotion. The repository can state the blocking
lemmas and their numerical thresholds; it does not prove those lemmas.

Every `clay*Promoted = false` flag remains intentional.

## Parallel Worker Split

- `W-G3`: physical SSP/Hecke 3D taper calibration,
  `sigma_SSP < 0.3025113508228815`.
- `W-Frame`: phase-complete frame factors
  `A_split > 0`, `A_inert > 0`, `A_71 > 0`, then uniform cutoff lift.
- `W-YM`: use connected-animal KP counting as the standard entropy target:
  `sum_d d * p^(d-1) exp(-beta*c_min*d) < 1`, with computed threshold
  `beta* ~= 9.59` and gap `3.59` from physical `beta ~= 6`.  Direct `T7A`
  KP is proved at `beta* ~= 16.56` but is worse as counting; T7A can help
  only through a per-polymer activity-suppression theorem.  Then supply the
  non-perturbative Balaban bridge, followed by OS/Wightman construction.
- `W-NS-A`: publishable `H^{-1/2}` obstruction theorem.
- `W-NS-B`: non-circular `H^{11/8}` Bernoulli-band estimate and `K*` drift
  condition.

Arithmetic guard: the useful `7+7+1` split is the atom/frame grammar.  The
literal `Q(sqrt(-7))` CM audit remains separate as `5 split + 9 inert + 1
ramified`, with `p71` split-not-inert but still terminal SSP sign/carry lane.

## Gate 3 / Gravity 3D Taper

The digit-expansion PAWOTG calculation gives a concrete positive baseline:

- digit spread: `sigma ~= 0.288675`
- three-dimensional gravity threshold: `sigma_SSP < 0.3025113508228815`
- three-dimensional series at the digit baseline:
  `0.7228939450291813 < 1`
- one-dimensional Gate3 threshold: `sigma < 0.5052`

The coordinate grammar consumed by this calculation is now explicit in Agda:
`15SSP = 7 Hecke + 7 mirror-Hecke + p71 sign`.  Each septet is internally
read as `7 = 3D + 3D + sign`, and each 15SSP digit/lane expands through
Bruhat-Tits depth into depth-many nested 15SSP blocks.  This recursive
symmetry-complexity series is the coordinate reason the macroscopic
Archimedean density is `p^(3d)`, rather than the 1D `p^d` count.

The open theorem is not whether the target is numerically plausible. The
baseline passes. The open theorem is whether the actual physical SSP/Hecke
Archimedean embedding satisfies the stricter 3D taper. If
`sigma_SSP < 0.3025` is proved, the one-dimensional Gate3 condition follows
with headroom and the Mosco/no-spectral-pollution bridge can consume it.

Honest difficulty: medium. This is an explicit Hecke/harmonic-analysis
calculation, not a Clay proof by itself.

## Yang-Mills

The local carrier/KP lane is now sharply quantified.  Connected-animal
counting is the corrected standard entropy object:

```text
sum_{d >= 1} d * p^(d-1) * exp(-beta*c_min*d) < 1
beta* ~= 9.59
Delta beta from beta_phys ~= 6 is ~= 3.59
```

The direct `T7A` coefficient sum is also computed:

```text
sum_{d >= 1} c7(d) * exp(-beta*c_min*d) < 1
beta* ~= 16.56
Delta beta from beta_phys ~= 6 is ~= 10.56
```

It is a worse counting route because the small-depth T7A coefficients dominate
the sum.  Its useful role is the still-open per-polymer activity-suppression
lemma.

The physical continuum lane still needs:

- non-perturbative Balaban block-spin transfer from physical `beta ~= 6`
- effective carrier coupling above the connected-animal KP threshold
  `beta_eff > ~9.59`
- OS reflection positivity through the flow
- infinite-volume limit
- Wightman reconstruction `W0-W5`

The measured connected-animal gap is now about `3.59` in beta units.  Perturbative
beta-running is explicitly insufficient in the current ledger. This is the
constructive-QFT scale-transfer problem in the Balaban programme, followed by
the OS/Wightman reconstruction problem.  The older `C0 = 2` line and the
direct `T7A` count are retained as diagnostics; neither is the live standard
KP theorem.

Honest difficulty: very hard. This is the core Yang-Mills Clay work, not a
repo-local bookkeeping problem.

The current programme-frontier receipt consumes the IR/cusp equivalence
surfaces as candidate reductions. That does not close YM: it identifies the
remaining load-bearing target as the flat Euclidean 4D SU(N) mass-gap problem
plus the non-perturbative Balaban and OS/Wightman construction package.

## Navier-Stokes

The `H^{-1/2}` localized dual-norm route is now recorded as an obstruction
surface, not as the active solution path.

Path A is publishable now as an obstruction theorem: the localized
`H^{-1/2}` defect ratio diverges under Kolmogorov scaling, so that route
cannot close NS without importing regularity.

Path B is the Clay route:

- prime-scale Bernstein inequality with `C0 = sqrt(p)` (recorded)
- Leray `L2` band bound
- dissipation cutoff
- upward Bernoulli cascade
- geometric high-band sum
- global `H^{11/8}` bound for carrier-structured data
- density/compactness passage from carrier-structured data to all smooth data

The all-data density step remains conditional: uniform `H^{11/8}` bounds
independent of projection depth and the compactness passage must be proved.

So Bernstein is no longer the live NS gap. The live NS gap is proving the
small-viscosity `H^{11/8}` Bernoulli-band estimate without smuggling in global
regularity, then passing from carrier-structured data to all smooth data.

Honest difficulty: Path A is achievable; Path B is years-level PDE work and
may be structurally as hard as the full Clay problem.

## Recommended Sequencing

1. Publish the NS `H^{-1/2}` obstruction theorem.
2. Attack the small-viscosity `H^{11/8}` Bernoulli-band estimate using the
   recorded `C0=sqrt(p)` Bernstein constant.
3. Compute the physical SSP/Hecke 3D taper over the nested 15SSP coordinate
   grammar and decide whether
   `sigma_SSP < 0.3025` holds.
4. Use the ledger as a collaboration specification for the Balaban programme:
   bridge physical `beta ~= 6` to the active KP margin (`9.59`, `10.11`, or
   safe `13.64`), then prove OS/Wightman.
5. Work CKM higher-order Vub/beta correction separately from Clay promotion.

## Promotion Boundary

`ClayContinuumMathTransitionReceipt.agda` records the target signatures and consumed partial evidence only. It proves no PAWOTG uniform separation theorem, no Balaban physical beta bridge, no OS/Wightman continuum Yang-Mills theorem, no Navier-Stokes global regularity theorem, and no Clay promotion.
