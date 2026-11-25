# Paper 9 — original Ramanujan system and small hypergeometric q-transport

Agda parent 9936fae439999c40149394b61c61c441c8c09afe. Lean companion commits dd30fc1016177e08a4f13588e55247e2ad671c5c and 9ee290cd9343a85aa0e3710651c42672812f1d87 on research/paper9-original-eisenstein-derivative-20261125. No new compilation, arithmetic execution, CI, kernel or benchmarks. All new Lean proof terms are intended source proofs; may require elaboration/API repairs. No proof-status promotion.

## A2 — original eta-product regularization and negative-weight closure

Existing MoonshineEtaProductPinned.differentiableOn_tprod_one_sub_pow_pow and MoonshineEta24CuspPinned.eta24_cuspFunction_eqOn, with the actual normalizedDelta_eq_eta24, supply Delta(q)=q U(q) on the disk, U(q)=prod(1-q^n)^24. U analytic, U(0)=1; nonzero at nonzero q by the actual inverse qParam chart and canonical Delta nonvanishing. Differentiate the local function identity, not just its value. E2Q=1+q U'/U is analytic on disk and equals original e2=DDelta/Delta at every upper-half-plane point. The zero mode is exactly 1. No independent E2 source.

Differentiate original E2 transformation at each actual H point, using the previously source-written Mobius chain rule: with j=c tau+d and r=c/(2 pi i), DE2(gamma tau)=j^4 DE2+2r j^3 E2+12r^2 j^2. The existing polynomial identity cancels signed anomalies in 12 DE2-E2^2+E4. Its actual analytic q function vanishes at q=0 by E2Q0=E4_0=1 and the Euler q factor. Thus package actual weight4 CuspForm, not an assumed cusp form. Existing generalized cusp_isBigO_eta24 at any weight gives bounded quotient by eta24 (=actual Delta) of weight -8, adapting existing weight12 quotient owner. levelOne_nonpos_wt_const implies constant. At tau=2i, S covariance multiplies that constant by (2i)^(-8)=1/256, forcing zero. This yields originalRamanujan2 and originalRamanujanSystem in Integration/Paper9E2CorrectedClosure.lean with intended unconditional types and existing actual imports. No kernel accepted. In particular a Lean classical theorem, even if accepted, is not automatically a native Bishop theorem.

## A6 — original small differential system, not an arbitrary three-value carrier

Use actual x=E4, y=E6, e=E2Q, D=q d/dq, L=(x/y)D. Define
 a=(e x/y-1)/6,
 h=x^3/y^2-1,
 z=1-y^2/x^3.
On the original disk where x,y are apart, the Ramanujan system gives
 L a=-a^2/2+h(a/2+5/72),
 L h=h(h+1),
 L z=z.
Here h retains the signed rational observation; (1-z)h=z, and 1-z nonzero. No inverse coordinate is needed. Lean Integration/Paper9HypergeometricQTransport.lean source-writes ramanujanQ (transport back through actual qParam chart for q!=0), aVectorField,hVectorField,zVectorField and intended actual aTransport,hTransport,zTransport. These are not finite sample extrapolations. At q=0, handle separately by analytic continuity or Taylor coefficient, not divide by q. All statements explicitly preserve denominator conditions.

For the actual binomial branch F=sqrt(x), F0=1, differentiation of F^2=x gives LF=aF, using 3Dx=ex-y. Introduce b=a^2/2+h(a/2+5/72). Then L^2F=(La+a^2)F=bF. Product rule gives
 L^3F=[(a+h/2)La+(a/2+5/72)Lh+a b]F
      =h(3b/2+23a/36+5/72)F.
The last is an exact universal polynomial identity, source-written thirdMultiplier, together with secondMultiplier and odeFromMultiplier. Multiply by 1-z and use (1-z)h=z:
 L^3F=z(L^3F+3L^2F/2+23 LF/36+5F/72)
      =z(L+1/6)(L+1/2)(L+5/6)F.
This is a short ordinary derivation on named differential premises. Source implementation still requires the actual binomial analytic branch, derivative LF=aF, its iterated product-rule equalities, and convergent power-series interpretation. These are not hidden in a claim of completed ODE proof.

The actual h and z are mutually recoverable where denominators are apart: z=h/(1+h), h=z/(1-z). a alone does not recover e without x/y. Retain original x,y,e and q (including q=0); this is a consumer-specific differential reduction, not a globally reversible state compression. At q=0, a=h=z=0, F=1; the original q and derivative orders retained. Avoid assigning these to unrelated 369 values. No new P0 fibre obligation.

## Next actual endpoint

Original direct-q uniqueness remains: U_L=x/y has constant1, z constant0. For two analytic solutions with constant1, their difference's nth coefficient is forced by n^3 times that coefficient on the left and earlier terms on the right. Need formal coefficient/analytic interpretation and actual factorial recurrence; |q|<=2^-36, |z|<1 available on named analytic premises. The actual period consumer follows from LF=aF and s2=(x/y)(e-3/(pi Im tau)):
 LF+(1-s2)F/6 = F (x/y)/(2 pi Im tau) = 1/(2 pi Im tau sqrt(1-z))
using the selected positive real branches. A3–A5 actual degree41 Hecke, root isolation and Taylor source reflection still unpaid, no replacement by level3. A1 phase/native original binding and A7 positive normalization remain. F1 original factorial split, F2–F4 unverified source terms, F5 universal rational cross, F6–F9 acceptance/termination/cost/benchmark unchanged. Original classical Ramanujan, Rankin–Cohen, Serre, Dedekind eta, hypergeometric and Chudnovsky attributions retained, existing DASHI owners preserved. The two-coordinate algebra is a source-consumer simplification of the existing differential weld, not a claim of new classical identities.

## 25 November — selected hypermetric comparison and cusp-order transport (SOURCE, UNVERIFIED)

See `Docs/proofs/Paper9HypermetricCuspOrderFactorial20261125.md`. Actual RG two-metric, H3 residual and indexed chart transport donors audited; no 369/analytic metric identification. Fixed-radical reciprocal adjacent widths have exact shared-endpoint distortion S_n/S_(n+2), at most 2 on actual source band; signed sum contraction 2^-41 transfers to <=2^-40, radical refinement separately bounded. Lean companion `e9b8e422c4b8503074dbf45d6bf6632bd711bbae` writes actual normalized log sqrt branch/first derivative, cusp-order leading multiplier n and residual n^3*g0, all-index factorial ratio and actual CM leaf ratio, exact rational metric comparison. Actual H analytic ODE, germ uniqueness assembly and native prefix/rational reflection remain. All new terms uncompiled; no execution, kernel, CI or benchmark; A3–A5/F5 and acceptance remain open.
