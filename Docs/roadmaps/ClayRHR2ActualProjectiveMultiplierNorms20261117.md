# RH R2 — exact projective multiplier and derivative norms (2026-11-17)

**Classification:** original Lean source inspection plus independent SymPy algebra; no Lean kernel check, no original R2 closure. Portfolio **15/28 open**.

## Sources and attribution

Original definitions and proofs remain owned by `chboishabba/dashi_lean4`, branch `agent/rh-postmerge-maxcut-20261007`. Do not copy their theorems as new results.

- `Synthesis/RiemannProjectiveCircularHyperbolicDuality.lean` defines
  `genericProjectivePhysicalProfile g r u = 4*g u*twoRadiusBracket g r u`.
  Its exact bracket is `twoRadiusBracket g r u = evenResp g 0 r*cos(2*r*u) - evenResp g 0 (2*r)*cos(r*u)`.
- `Synthesis/RiemannProjectiveQuarticFourWindow.lean` defines the raw four-center smooth profile at centers `0,pi/3,pi/2,pi`, divided by `quarticWindowMass R=2R*unitBumpMass0`.
- `Synthesis/RiemannQuantitativeScaledBump.lean` constructs `unitBump` using Mathlib `ContDiffBump`, not an explicit polynomial.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPolePair.lean` constructs `R=min 1 (min R0 d)/2`, `muHalf=S1.mu`, `muTwo=S2.mu` by existence/IVT. No numeric values supplied by that construction.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleTarget.lean` defines the signed combined profile `Pcomb=kappa2*P_half-kappa1*P_two` with `kappa1=poleHalf`, `kappa2=poleTwo` given by `quarticFourSmoothFinitePoleResidual`.
- `Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleJointHorizontalJet.lean` expresses the literal normalized pair via two `genericProjectivePairKernel` components and the exact `signedLiteralPairSourceTerm` physical scaling.

## New exact transport theorem (mathematical proof outside kernel)

For normalized raw window `g=G_{R,lambda,mu}` let `Q=2+|lambda|+|mu|`, `b_j=||psi^(j)||_1`, `b_0>0`, and `q_0=Q`, `q_j=Q*b_j/(b_0 R^j)` for j>=1.

At projective sampling radius **one** put
`A_1=∫g(v)cos(v)dv`, `A_2=∫g(v)cos(2v)dv`.
Then the **literal operator has differential order p=0**:
`P_g(u)=4g(u)*(A_1*cos(2u)-A_2*cos(u))`.
Since `|A_1|,|A_2| <= ||g||_1 <=Q`, Leibniz and the trigonometric derivative suprema give, for j=0,...,4,

`||P_g^(j)||_1 <= E_j(lambda,mu,R) := 4 Q * Σ_(k=0)^j binom(j,k)*(2^(j-k)+1)*q_k`.

Explicitly:
`E_0=8Q²`;
`E_1=4Q²*(3+2*b1/(b0*R))`;
`E_2=4Q²*(5+6*b1/(b0*R)+2*b2/(b0*R²))`;
`E_3=4Q²*(9+15*b1/(b0*R)+9*b2/(b0*R²)+2*b3/(b0*R³))`;
`E_4=4Q²*(17+36*b1/(b0*R)+30*b2/(b0*R²)+12*b3/(b0*R³)+2*b4/(b0*R⁴))`.

For the *original signed combined profile* `Pcomb=kappa2*P_half-kappa1*P_two`, an explicit symbolic envelope is

`M_j^comb=|kappa2|*E_j(1/2,muHalf,R)+|kappa1|*E_j(2/3,muTwo,R)`.

Support lies in `[-(pi+R),pi+R]`. In particular **no b5 or b6 is required** for a fourth-derivative transform bound; the projective operator multiplies g by a smooth trig polynomial, not by a differential operator.

Subject to the original exact pair-kernel identity
`K_W(alpha,q)=∫Pcomb(u)cosh(alpha*u)cos(q*u)du`, four integrations by parts give
`|K_W(alpha,q)| <= exp(aL)/|q|⁴ * Σ_(j=0)^4 binom(4,j)*a^(4-j)*M_j^comb`, `|alpha|<=a`.
For `r=t/16`, `a=1/(2r)`, the earlier source physical scaling gives conditional
`C(t,W)=16*r²*exp(aL)*Σ_(j=0)^4 binom(4,j)*a^(4-j)*M_j^comb`.

**Important scope:** This is a rigorous paper-level envelope given the stated definitions, but it is NOT a fully instantiated rational bound: Mathlib's `ContDiffBump` does not expose numeric `b_1,...,b_4` in these Lean source files, and the selected `R,muHalf,muTwo,kappa1,kappa2` are not numeric. No literal signed R2 target was evaluated.

## Next exact lemmas

1. `selectedQuarticFourWActualProfileIntegralExact`: transport source's exact `genericProjectivePairKernel` representation onto `Pcomb` at the source definition, preserving its cosh/base conventions and pole normalization; this source equality is plausibly a short Lean theorem, but has NOT been kernel checked here.
2. `selectedQuarticFourWDerivativeNormsExplicit`: prove the `E_0...E_4` envelope in Lean for the selected profile, instantiate explicit `b_j` bounds for Mathlib's *actual* `ContDiffBump`; numeric constants cannot be inferred from the support and `C^∞` property alone.
3. `originalSelectedPoleCoefficientsExplicit`: source `kappa_{1,2}` from `quarticFourSmoothFinitePoleResidual`, with admissible bounds for IVT-selected `R,muHalf,muTwo`.
4. `originalLiteralFarExactCertifiedFinite` and `originalSelectedTargetThresholdCertified`: original finite signed sum and threshold, not surrogate.
5. `originalSelectedFiniteSignedSurplusStrict`: certified correct-polarity surplus, including multiplicity and (if conditional off-line zero) a valid hypothetical off-line carrier.
6. `originalSelectedUniformCofinalTail`: rigorous omitted-tail estimate with the exact owner theorem's quantifiers (not only fixed-t).
7. `originalR2EventualSignedCompensationGap`: prove actual strictly positive epsilon and eventual n threshold, preserving the original quantified t,rho,W.
8. `originalR2NativeKernelWeld`: exact-head Lean/Agda typechecking and ledger update.

Attribution rule: the source definitions, projective operator and original literal kernel belong to prior Lean/DASHI contributors; this note adds only an independent derivative-envelope reduction and SymPy regression. R2 **OPEN**, expanded 15/28 **OPEN**, Clay endpoints 0/6.
