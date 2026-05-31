# Paper 6 Final Draft Outline: Carrier Matter, CKM Boundaries, and NS Transfer

Date: `2026-05-31`
Status: prewrite baseline; fail-closed; non-promoting

## Abstract

Paper 6 records what the current DASHI matter programme actually proves,
what it has retired, and what remains open.  The proved material is narrow:
the `p=7` CKM lane is selected by independent CM/Hurwitz consistency
arguments, NS lane separation is represented by incompatible discrete and
profinite carrier actions, the Klein quartic supplies a genuine
three-generation object through `J(K) ~= X_0(49)^3`, and the carrier NS bound
admits a precise Kolmogorov/Serrin interpretation.  New frontier receipts add
three bounded items: Kolmogorov-calibrated viscous tail dominance,
the corrected `PSL(2,F7)` texture constraint, and a finite `Z/7` spectral-gap
calculation.  The p-adic carrier coordinate and programme-lineage remarks are
included only as origin/consistency bookkeeping.  The paper does not derive the
physical CKM matrix, the CP phase, or the Clay Navier-Stokes theorem.

## 1. Claim Boundary

The opening section must state the governance line first.

- `lambda` is a Georgi-Jarlskog literature compatibility, not a new DASHI
  CKM theorem.
- `|Vub| ~= alpha1*alpha2` survives only as a leading-order structural
  hypothesis in the `U_d ~= I` approximation.
- `|Vcb|`, `gamma`, `beta`, `alpha`, `rho`, and `eta` are not carrier
  predictions in the present state.
- The `PSL(2,F7)` texture statement is a representation constraint, not a
  derived down-type Yukawa matrix.
- The finite `Z/7` spectral gap is finite evidence only, not a continuum gap.
- Paper 8 does not depend on the CKM sector.
- No Clay promotion follows from the NS or YM receipts.

## 2. Gate A(a): Why The CKM Lane Is `p=7`

This section records the positive arithmetic result.

- The CM smooth-point check eliminates the elliptic values `j=0` and `j=1728`
  and leaves `D=-7` as the smooth class-number-one CM point at the active CKM
  lane.
- The Hurwitz uniqueness argument independently selects the prime triple
  `(2,3,7)` as the unique hyperbolic prime triple of maximal reciprocal sum.
- NS lane separation is represented by a discrete `Z` band-shift action, while
  the CKM `p=7` carrier is profinite through the CM Tate module.
- The structural bottleneck at `p=7` should be stated as a consistency remark:
  `F_7^x` has six nonzero directions, pairing as three sign-opposite
  direction classes, which is the first odd-prime lane with enough directional
  room for a three-slot carrier while remaining tied to the Hurwitz
  `(2,3,7)` constraint.
- The fuller `p=7` bottleneck remark has six bounded readings:
  spectral (`Z/7` is the product-gap bottleneck), dynamical (`log2(7)=2.81`
  is the deepest generation-prime depth but below physical viscous cutoffs),
  geometric (`49=7^2` and the `p=7` Bruhat-Tits/Cerednik-Drinfeld surface),
  algebraic (the full `PSL(2,F7)` no-go for bilinear invariants), CM
  arithmetic (`chi_V3(Frob7)=tau_-7`), and origin/Hurwitz uniqueness.
  These are consistency checks, not CKM promotions.
- These independent constraints agree at `p=7`; this closes Gate A(a), not the
  CKM phase.

## 2A. P-Adic Coordinate And Programme Lineage Remarks

This subsection is diagnostic/origin material, not a theorem source.

- The carrier coordinate should be defined by splitting a real comparison
  value into an integer projection and a defect:
  `x = floor(x) + frac(x)`.  The integer part is the `Z -> Z_p` projection
  used by the p-adic carrier; the decimal/fractional part is not silently
  promoted into `Z_p` and is instead recorded as the residual defect in
  `C`-space.
- In the ternary lane, the 3-adic fixed attractor
  `x = -1/2 = 1 + 3 + 3^2 + ...` matches
  `Re(tau_-7)` for `tau_-7 = (-1+i*sqrt(7))/2`.  This is a coordinate
  alignment with the CM point, not a derivation of a CKM phase.
- The programme lineage has two independent paths: a ternary/3-adic path
  through carrier coordinates and fixed attractors, and a braid path through
  `B_3`, Yang-Baxter consistency, and the `(2,3,7)` Hurwitz constraint.
- The convergence point of these two paths is the Klein quartic / `p=7`
  architecture.  This convergence is evidence for the carrier origin story,
  not a promotion to a physical CKM matrix.

## 3. Retiring The Direct CP-Angle Shortcut

The formula `gamma = arctan(sqrt(7))` is retired.

- The pure angle is `69.30°`, while HFLAV 2023 gives `65.5 ± 0.7°`; the
  tension is `5.4 sigma`.
- The seven 7-isogeny images were audited and none lands near the experimental
  angle.
- The Atkin-Lehner and Frobenius arguments confirm that `arctan(sqrt(7))` is
  the canonical `D=-7` CM angle, not an adjustable physical prediction.
- The CKM phase must come from the full Yukawa diagonalisation, not from
  reading an angle directly off the modular curve.

## 4. Klein Quartic And The Three-Generation Object

This is the central positive CKM architecture result.

- The Klein quartic is the genus-3 Hurwitz curve for `(2,3,7)`.
- Its Jacobian satisfies `J(K) ~= X_0(49)^3` as an abstract abelian variety.
- `X_0(49)` has CM by `O_-7`; the rational endomorphism algebra is
  `M_3(Q(sqrt(-7)))`.
- The `PSL(2,F7)` 3-dimensional character at order-seven elements gives the
  CM period `tau_-7 = (-1+i*sqrt(7))/2`.
- This supplies three CM factors, hence a real three-generation object.
- The corrected `PSL(2,F7)` character constraint gives
  `V3 tensor V3 = V3' + V6`; it contains no trivial representation.
- The open task is not generation counting; it is the carrier morphism that
  labels the three factors and then the symmetry-breaking dynamics that derive
  `Y_d`.

## 5. Clean Negatives

These are not side notes; they prevent later overclaiming.

- McKay-Thompson values at `tau_-7` do not give the CP phase.
- Ring-class-field and Selmer/deformation routes do not provide the missing
  generation architecture.
- Weierstrass stabiliser ordering fails: the relevant orbits do not provide
  non-isomorphic stabilisers that canonically label three factors.
- The ultrametric Yukawa hierarchy in the tested single-`alpha` form fails by
  inconsistent fitted `alpha` values.
- These negatives leave the three-factor morphism and `Y_d` as the honest CKM
  frontier.

## 6. Navier-Stokes Carrier/Kolmogorov/Serrin Boundary

The NS section should use `NSCarrierKolmogorovSerrinReceipt`.

- For a Kolmogorov spectrum `E(K) ~ K^{-5/3}`, dyadic band energy obeys
  `||u_k||^2 ~ 2^{-2k/3}`.
- The natural carrier decay parameter is
  `alpha_K = 2^{-2/3} ~= 0.6299605`.
- The standard `H^{11/8}` contribution is
  `2^{11k/4} * 2^{-2k/3} = 2^{25k/12}`.  The corrected exponent is `25/12`,
  not `41/12`.
- Viscous tail dominance gives the calibrated active-tail threshold
  `K*(nu)=3/4 log2(1/nu)`.  This is Kolmogorov-calibrated carrier evidence
  only; it does not promote a Clay Navier-Stokes claim.
- Finite active depth gives a norm comparison to standard `H^{11/8}`;
  Sobolev embedding gives `L^24`, and the Serrin value is `3/24 = 1/8 < 1`.
- Unbounded depth does not imply blow-up.  It means this carrier route to
  Serrin regularity can fail.

The one-sentence formulation:

> The carrier localises the Clay difficulty to control of the high-depth
> cascade: finite active depth gives standard Serrin regularity; unbounded
> depth is where the norm comparison can fail.

## 7. YM Boundary

Paper 6 may briefly point to the Paper 8 YM ledger.

- The cusp-to-flat Yang-Mills statement is a continuum-to-continuum
  biconditional, not a lattice regularisation.
- It places the carrier YM gap in the same equivalence class as flat 4D
  Yang-Mills.
- It does not prove the mass gap; the remaining problem is the Clay problem
  itself.

## 7A. Finite Spectral-Gap Evidence

The finite `Z/7` receipt belongs in the evidence ledger, not the promotion
ledger.

- The unnormalised finite cycle gap is `2 - 2 cos(2*pi/7) ~= 0.753`.
- The normalised random-walk gap is half of that value,
  `1 - cos(2*pi/7) ~= 0.3765`.
- The product carrier `Z/7 x Z/3 x Z/2` has unnormalised factor gaps
  `0.753`, `3`, and `2` respectively, so `Z/7` remains the bottleneck.
- This is a finite spectral calculation on `Z/7`.
- It is not a continuum Yang-Mills mass gap and not a Clay promotion.

## 8. Remaining Mathematics

The paper closes with three precisely bounded fronts.

| Front | What Remains | Type |
| --- | --- | --- |
| NS | depth-control / carrier-to-standard norm comparison beyond Kolmogorov-calibrated `K*(nu)` | functional analysis |
| CKM | three-factor morphism into `T_7(X_0(49))^3`, then symmetry breaking for full `Y_d` | algebra then dynamics |
| p-adic origin | formal carrier map from integer projection plus `C`-space decimal defect, and a proof-grade account of the 3-adic/braid lineage convergence | foundations / exposition |
| finite gap | bridge, if any, from finite `Z/7` evidence to a continuum operator | spectral analysis |
| YM | flat 4D Yang-Mills mass gap | Clay problem |

## 9. Conclusion

The paper's conclusion should be direct: DASHI has a clean `p=7`
three-generation architecture and a precise NS carrier/Kolmogorov boundary,
but it has not derived the physical CKM matrix or solved either Clay problem.
The value of the paper is the fail-closed ledger: proved statements,
retired shortcuts, and open problems that are no longer vague.
