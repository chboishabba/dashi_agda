# RH R2 four-window source-specific L1 reduction — 17 November 2026

**Status:** New exact source-specific **raw four-window** derivative-norm reduction; **no expanded portfolio gate closed**. R2 still OPEN, 15/28 OPEN, 0/6 Clay endpoints.

## Source inspected

From `chboishabba/dashi_lean4` branch `agent/rh-postmerge-maxcut-20261007`:
- `Synthesis/RiemannProjectiveQuarticFourWindow.lean`: `quarticFourWindowRaw R lam mu = quantitativeSymBump 0 R - quantitativeSymBump (pi/3) R + lam * quantitativeSymBump (pi/2) R + mu * quantitativeSymBump pi R`; `quarticFourWindowProfile = raw/(quarticWindowMass R)`.
- `Synthesis/RiemannProjectiveQuarticThreeWindow.lean`: `quarticWindowMass R=2R*unitBumpMass0`.
- `Synthesis/RiemannQuantitativeScaledBump.lean`: `unitBump` is a Mathlib `ContDiffBump` (inner radius 1/2, outer radius 1), `scaledUnitBump c R u = unitBump ((u-c)/R)`.
- `Synthesis/RiemannQuantitativeSymmetricBumpMass.lean`: `quantitativeSymBump c R u = scaledUnitBump c R u + scaledUnitBump c R (-u)`.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPolePair.lean`: selected `R=min 1 (min R0 d)/2`; `muHalf=S1.mu` and `muTwo=S2.mu` from existential intermediate-value witnesses, not explicit rational constants.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleTarget.lean`: the *actual* selected signed combined profile uses projective transformed profiles and two `quarticFourSmoothFinitePoleResidual` coefficients.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean`: `signedLiteralPairSourceTerm = mult/(t/16)^2 * signedNormalizedPairKernel alpha q`. This kernel combines two `genericProjectivePairKernel` terms; replacing it by a generic Fourier integral requires the original exact integral identity.

## Exact mathematical result

Let `psi=unitBump`, `B_j=||psi^(j)||_1` for j=0,...,4 with B0>0. For R>0 define
`G_{R,lam,mu}(u)=[symBump(0,R)-symBump(pi/3,R)+lam*symBump(pi/2,R)+mu*symBump(pi,R)]/(2 R B0)`.

By translation, scaling, reflection and triangle inequality:
`||G_{R,lam,mu}^(j)||_1 <= (2+|lam|+|mu|) B_j/(B0 R^j)` for each j=0,...,4.
The support lies in `[-(pi+R),pi+R]` (since the largest center is pi and the base bump is supported on [-1,1]).

For j=0, the bound simplifies to `2+|lam|+|mu|`. For j>=1, `R^{-j}` exposes the potentially large constant when the selected smoothing radius is small. These are genuine estimates on the **raw normalized window**. They do **not** yet bound `quarticFourNormalizedProjectiveProfile`, which is `genericProjectivePhysicalProfile G 1`, or the signed pair kernel; operator derivatives/pole factors must be transported first.

The source `unitContDiffBump` is not a prescribed piecewise polynomial; `B_j` are finite but have not been evaluated to rational intervals. No numerical selection of `R,muHalf,muTwo` is licensed by an existential Lean construction.

## Executed local SymPy diagnostic

`scripts/check_rh_r2_four_window_l1_algebra_20261117.py`: PASS exact weight absolute-value sum, all j=0..4 profile scale identities, rational fixed-height tail antiderivative and monotonicity. This checks symbolic algebra only; analytic change-of-variables/triangle inequality are mathematical deductions from the source. No Lean kernel run.

## Exact remaining producers (R2)

1. `selectedQuarticFourWActualProfileIntegralExact` — exact `genericProjectivePairKernel` integral identity for transformed two-profile signed combination and its base/horizontal components, with pole coefficients.
2. `selectedQuarticFourWDerivativeNormsExplicit` — norm bounds `M_j` for **transformed profile**, including `B_0..B_4`, selected R/mu and pole coefficients, not only raw G.
3. `originalActualZetaUnitShellCountA160` — classical A=160 has been derived from published zero count; native transfer into original `Zeros` carrier still open.
4. `originalLiteralFarExactCertifiedFinite` — actual signed finite far sum, zero multiplicities and canonical exhaustion; current zero table alone is insufficient.
5. `originalSelectedTargetThresholdCertified` — exact selected target `4D_comb + integral Psi_t dmu`.
6. `originalSelectedFiniteSignedSurplusStrict` — strictly positive certified correct-polarity local signed surplus. Important: known on-critical-line zeros cannot instantiate a hypothetical off-critical-line selected rho, so numerical finite checks cannot by themselves prove the universal implication.
7. `originalSelectedUniformCofinalTail` — uniform quantifiers in t,rho and, if quantified, W; fixed-height absolute convergence is inadequate.
8. `originalR2EventualSignedCompensationGap` — prove the strict eventual epsilon inequality on the original carrier with exact source and no surrogate bounds.
9. `originalR2NativeKernelWeld` — exact-head native theorem acceptance and gate-ledger update only if 8 is discharged.

**Quantifier firewall:** A fixed t finite signed surplus and vanishing tail gives a fixed-t statement, not a universal `exists eps>0, exists N, forall t,rho,W, forall n>=N` theorem. Conversely some original formal statements quantify t/rho outside or inside the eventual gap: inspect the precise owner theorem and preserve that order before assuming uniformity. Neither Li's criterion nor a generic positivity analogy establishes equivalence of this *particular* signed-gap proposition to RH.

**No gate closure:** R2 analytic signed margin still open; 13/28 settled, 15/28 open, 0/6 Clay endpoints.
