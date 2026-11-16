# R2 literal Lean kernel and cofinal-gap source audit — 16 November 2026

**Status: R2 OPEN; 15/28 OPEN.** This audit corrects an important interpretation of the earlier 32-zero numerical controls and identifies the exact source needed for a genuine numerical test. No actual signed compensation value or cofinal epsilon has been certified.

## Verified exact Lean sources (chboishabba/dashi_lean4, branch agent/rh-postmerge-maxcut-20261007)

- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean`:
  `W.signedLiteralPairSourceTerm sigma = mult(sigma)/(t/16)^2 * W.signedNormalizedPairKernel (heightOf(sigma)/(t/16)) ((Im(sigma)-t)/(t/16))`.
  `W.signedNormalizedPairKernel alpha q = W.poleTwo*genericProjectivePairKernel (quarticFourWindowProfile W.R (1/2) W.muHalf) alpha q - W.poleHalf*genericProjectivePairKernel (quarticFourWindowProfile W.R (2/3) W.muTwo) alpha q`.
  **Literal joint quartic in this file**: `W.targetStrength*(alpha²q²-q⁴/6)`; `W.literalJointQuarticRemainder` is defined by exact subtraction. Do not silently replace this remainder with the distinct complete bivariate quartic remainder.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleConeDecomposition.lean`:
  `centeredZeroFinset t n` consists of zeros with `t-n < Im(rho) <= t+n`.
  `literalOffOrdSource rho = if Im(rho)!=t then signedLiteralPairSourceTerm rho else 0`.
  `literalFarExactAt eta n = sum_{rho in centeredZeroFinset t n, |(Im(rho)-t)/(t/16)|>eta} literalOffOrdSource rho`.
  `literalConeDebtAt` is the positive part of the **exact literal source**, not a quartic-only sum. `literalGoodQuarticGainAt` is the negative of the **original joint quartic**, not the complete bivariate quartic.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleQuantitativeBand.lean`: selected witness fields `W.R,W.muHalf,W.muTwo,W.poleHalf,W.poleTwo,W.targetStrength` and actual combined profile; do not use arbitrary replacement profiles.
- `DASHI/Analysis/RiemannQuarticSignedPoleCompensationExact.agda`: complete bivariate jet `S*(alpha²q²-(alpha⁴+q⁴)/6)+R6` and signed sharpened cone compensation; the new jet's fourth-order `alpha⁴` is not interchangeable with the older `literalJointQuarticPolynomial` without adjusting its remainder and debt definitions.

## Crucial correction

**Off-ordinate is NOT off-critical-line.** A zero on `Re(rho)=1/2` with `Im(rho)!=t` is in the original off-ordinate carrier and can contribute through the base kernel `W.signedNormalizedPairKernel(0,q)`. Thus numerical zeros on the critical line can test a **finite off-ordinate** sum, once the literal W profile is evaluated. They do **not** test the nonzero-alpha horizontal mechanism, nor prove RH, nor establish the uniform cofinal gap. The earlier statement that they cannot measure any off-ordinate contribution because alpha=0 was too strong.

## Required literal numerical computation

For each height t, natural cutoff n, and zero (beta,gamma) with multiplicity m:
1. r=t/16, alpha=(beta-1/2)/r, q=(gamma-t)/r.
2. Evaluate **the selected** W profile's `genericProjectivePairKernel` at (alpha,q), including the source's signed pole coefficients.
3. Set `term=m/r² * W.signedNormalizedPairKernel(alpha,q)` if gamma!=t, otherwise 0.
4. Partition with the original `eta=1/(pi+1)` and the original `delta²<=6a²` cone; use exact terms for cone debt and far, the original joint quartic for good gain, and its exact original remainder for local debt.
5. Check finite equality `OffOrdExactAt=ConeExactAt+GoodExactAt+FarExactAt` and inequality `OffOrdExactAt<=LocalDebtAt-SignedCompensationAt`, retaining signed `FarExactAt`.
6. Repeat for increasing centered cutoffs n, with interval enclosures and an **independent uniform cofinal-tail bound** before inferring any eventual epsilon.
7. The exact target `T_W(rho)=4*D_comb(rho)+integral Psi_t*mu` must also be instantiated, not replaced with a guessed constant.

**What was not established:** exact selected profile quadrature, certified zeta zero isolation, numerical `FarExactAt`, the original target threshold, or uniform omitted-tail bounds. No gate closed and no original Clay endpoint claimed.
