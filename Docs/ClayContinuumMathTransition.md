# Clay Continuum Math Transition

This document is the current compressed Clay-facing state after the scale-graph barrier algebra has been separated from its analytic inhabitants.

The repository is no longer looking for the grammar. The grammar is recorded. The remaining work is continuum mathematics.

## What The Repository Has Built

DASHI is now a precision fault-localisation ledger. It has separated the
shared scale-graph barrier algebra from the continuum mathematics that would
be needed for Clay-facing promotion. The repository can state the blocking
lemmas and their numerical thresholds; it does not prove those lemmas.

Every `clay*Promoted = false` flag remains intentional.

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

The local carrier/KP lane is now sharply quantified, but the physical continuum lane still needs:

- non-perturbative Balaban block-spin transfer from physical `beta ~= 6`
- effective carrier coupling above the T7-compressed absorption regime
  `beta_eff > 15.84`
- OS reflection positivity through the flow
- infinite-volume limit
- Wightman reconstruction `W0-W5`

The measured gap after T7 compression is about `9.84` in beta units. Perturbative
beta-running is explicitly insufficient in the current ledger. This is the
constructive-QFT scale-transfer problem in the Balaban programme.

Honest difficulty: very hard. This is the core Yang-Mills Clay work, not a
repo-local bookkeeping problem.

## Navier-Stokes

The `H^{-1/2}` localized dual-norm route is now recorded as an obstruction
surface, not as the active solution path.

Path A is publishable now as an obstruction theorem: the localized
`H^{-1/2}` defect ratio diverges under Kolmogorov scaling, so that route
cannot close NS without importing regularity.

Path B is the Clay route:

- prime-scale Bernstein inequality with `C0 = sqrt(p)`
- Leray `L2` band bound
- dissipation cutoff
- upward Bernoulli cascade
- geometric high-band sum
- global `H^{11/8}` bound for carrier-structured data
- density/compactness passage from carrier-structured data to all smooth data

The all-data density step remains conditional: uniform `H^{11/8}` bounds
independent of projection depth and the compactness passage must be proved.

Honest difficulty: Path A is achievable; Path B is years-level PDE work and
may be structurally as hard as the full Clay problem.

## Recommended Sequencing

1. Publish the NS `H^{-1/2}` obstruction theorem.
2. Compute the physical SSP/Hecke 3D taper over the nested 15SSP coordinate
   grammar and decide whether
   `sigma_SSP < 0.3025` holds.
3. Use the ledger as a collaboration specification for the Balaban programme.
4. Attempt the NS `H^{11/8}` density route only after the embedding quality is
   settled.

## Promotion Boundary

`ClayContinuumMathTransitionReceipt.agda` records the target signatures and consumed partial evidence only. It proves no PAWOTG uniform separation theorem, no Balaban physical beta bridge, no OS/Wightman continuum Yang-Mills theorem, no Navier-Stokes global regularity theorem, and no Clay promotion.
