# NS physical rate-Cauchy radical: exact source geometry and remaining C1/C2

## 23 November 2026 — source-produced Galerkin physical attachment paid at executable level; two signed obstructions

[**Actual finite Galerkin source-produced doubleForcing/doubleCell exact weld and rigorously signed witnesses**](NSR568OriginalGalerkinHelicityRateSignCountercontrol20261123.md), executable [check_ns_r568_physical_source_weld_exact_20261123.py](../../scripts/check_ns_r568_physical_source_weld_exact_20261123.py), exact Git blob `efad812d7699118ccb0396eb0165d4e6ba323fa8`. Unlike previous independent D/M rational PROXIES, the new 64/64 tests compute a common divergence-free conjugate-real u, its complete original ordered projected -iP_k quadratic network G(u), exact +/- curl eigenprojectors and original R225/R388 M/D. They verify full direct ordered R566 forcing pair == rate bucket == rate projector, complete R225/R230/R542 fold factors and R687 rate-lift normalization. Two deterministic seeds 61 and 63 at k=(1,0,0), C=1 strictly **reverse the sign** between unweighted F and rate-lift L in opposite directions; exact rational outward algebraic sqrt sign certificates. Hence arbitrary-rate positivity-only AND unconditional **same-physical-state pointwise** sign transfer are DISPROVED as candidate payment mechanisms, not the genuine R568 signed spacetime estimate. The original C=1 real physical helical scalars include sqrt2 and sqrt3; fixed rational F=Q in the native owner cannot exactly accommodate those, so Agda/Bishop **algebraic field transport remains open** and the executable is not an Agda theorem. Previous source-centred kernel rank/midpoint theorem, 37-source-fibre census and BIDI remain correct. P0 now: native field weld if formalizing sign firewall; more importantly **new dynamic compensated signed C1 upper + original C2 lower**, R565 scalar FTC and 3D PDE proof. Do not count the sign obstruction as a Clay theorem.



**23 November 2026.** This is an original-source finite lattice theorem and an exact executable proxy regression. It is NOT a bound on physical Navier–Stokes nonlinear forcing, a proof of R568, or an Agda kernel result. Preserve already-merged original numbered source owners. Semantic names for new artifacts follow Docs/SemanticNamingInventory20261123.md and config/semantic-name-registry.json; do NOT mechanically rename original modules.

## 1. Original source owners on master (do not rebuild)

- NSTriadKNPhysicalTriadEnumeration.agda constructs actual PhysicalTriadIncidence (p,q,k, resonance) and enforces **p,q,k ALL within the original cutoff**. NSTriadKNPhysicalOutputFiber.agda filters that enumeration; canonical live R568 k also excludes the zero output. This corrects an earlier broader p+q arithmetic diagnostic: k outside C is NOT a source-admissible original R568 output.
- NSTriadKNMixedHelicityFixedOutputSwapRound224Exact.agda already proves p/q swap is a permutation of the complete original output fibre. NSTriadKNCellRateSwapInvariantWeightRound295Exact and NSTriadKNPhysicalCyclicCellRateDefectBidiExact distinguish p/q rate invariance from the GENERALLY FALSE three-leg cyclic rate invariance.
- R541 NSTriadKNSpectatorResolventR294WeightRound541Exact and R567 NSTriadKNFactoredFullCommutatorOnlyRound567Exact own the same-source positive pair resolvent and real-Hermitian forcing scalar. R687 NSTriadKNR650RateLiftedR568ToC2CommutatorRound687Exact identifies rate-lifted forcing with 8 times genuine coherent commutator work; its unlifted-to-lifted bound remains OPEN.
- R568 NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact owns the actual R240/R405 full nonzero-output time-integrated forcing; NSTriadKNLiveSpectatorResolventNestedLeafABidiExact already proves its four-sign nested BIDI.
- R596/R624/R628/R634 own the self/flux, canonical external, helicity and time-slice signed decompositions. R688/R689 own rate-lifted tangent/input-Laplacian cancellation. R652/R653 own the original C1/C2 same-source signed sandwich. All original signed spacetime analytic estimates remain OPEN.
- Existing R236 covariance/padding and its C^5 signed behaviour are a DIFFERENT instantaneous source and are not R568 theorems.

## 2. Exact original midpoint geometry with forward/reverse

Fix C>=1, ORIGINAL output k in [-C,C]^3 with k!=0. The ordered source incidence fibre is I(C,k)={(p,q): p+q=k, p and q in [-C,C]^3}. Define d=p-q=2p-k. The integer inverse is p=(k+d)/2, q=(k-d)/2, with **d_i congruent k_i mod 2** and **|d_i|<=2C-|k_i|**. Swap p/q acts exactly as d->-d and has one fixed incidence precisely when all k_i are even. No original order, signs, phases or source indices are lost if the incidence sidecar is retained.

Let m(p,q)=|p|^2+|q|^2 and r=nu*m for rational nu>0. Then

    2m=|k|^2+|d|^2
    m congruent |k|^2 mod 2.

Writing o(k)=number of odd k coordinates, the genuine minimum mass is m_min=(|k|^2+o(k))/2; the genuine maximum is m_max=(|k|^2+sum_i(2C-|k_i|)^2)/2. Every mass differs from m_min by an even integer. Thus the number R of ACTUALLY ATTAINED rate classes satisfies

    R <= floor((m_max-m_min)/2)+1 <= 3 C^2+1.

The actual multiplicity polynomial is a **product of one-dimensional source-incidence factors**:

    P_(C,k)(z)
       = product over i of [
           sum over d_i congruent k_i (mod 2), |d_i|<=2C-|k_i|
               z^((k_i^2+d_i^2)/2) ]
       = sum over original (p,q) in I(C,k) z^(|p|^2+|q|^2).

Coefficient at z^m is n_m, the number of original ordered incidences in mass class m. P(1) gives total incidence count; P'(1) gives total input-mass sum, overlapping the ALREADY-existing R236 lattice moment owners. The new use is the Cauchy-rate spectral quotient, not re-proving original count algebra.

## 3. New strongest finite fact: EXACT Cauchy kernel rank and radical

Let N=#I, R=#distinct masses, and let B be the R-by-N rate-class incidence matrix B_(m,a)=1 if m_a=m and 0 otherwise. For positive nu let C_(m,n)=1/[nu(m+n)] and K_(a,b)=1/[nu(m_a+m_b)]. Source-resolvent scalarization gives

    K = B^T C B.

Every class is inhabited, so rank B=R. The classical Cauchy determinant for distinct positive rates x_m=nu*m is

    det C = product_(m<n)(x_n-x_m)^2 / product_(m,n)(x_m+x_n) > 0,

and the same formula on every leading principal minor makes C strictly positive definite. Therefore **rank K=R** and

    ker K = ker B = { v: for each mass m,
                           sum_(a: m_a=m) v_a=0 }.

Radical dimension is EXACTLY N-R per scalar coordinate. The orthogonal rational quotient projector

    Pi = B^T diag(1/n_m) B

obeys Pi^2=Pi, Pi K=K Pi=K. In particular, for ANY rational or real-Hermitian vector carrier families D and M (including the actual source TYPES doubleForcing and doubleCell),

    sum_a,b K_a,b Re<D_a,M_b>
        =sum_a,b K_a,b Re<(Pi D)_a,(Pi M)_b>.

This is **not a positivity claim** about a mixed cross: D and M need not coincide. It removes every within-mass zero-sum direction while preserving the full signed pairing. Swap-odd vectors D^-(p,q)=[D(p,q)-D(q,p)]/2 lie in that radical, even if the original D is not pointwise swap invariant. The radical is LARGER than just swap-odd, because distinct swap-orbits may share a mass. Bucket vector SUMS or Pi alone are non-injective; reverse reconstruction requires the original complete ordered incidence sidecar with p,q,rate,phase/helicity and source vector values.

At k=(5,0,0), source admissible C=5: N=726, R=42, radical=684. Swap-odd dimension=363 and additional EVEN within-rate radical=321. At C=6: N=1352, R=67, radical=1285, swap-odd=676 and further even-null=609. These are exact finite-source numbers, NOT a spacetime bound or a proof that a true physical forcing occupies every algebraic class.

## 4. Executed acceptance and corrections

- Local independent standard Python Fraction test: **37/37 source-admissible complete output fibres**, **26,934** exact original p/q/midpoint/parity incidences. The earlier 44 broad arithmetic fibres (27,452 incidences) included seven invalid |k_i|>C outputs; do NOT reuse those counts as original source acceptance.
- Exact product-of-1D rate polynomial equals independently enumerated mass multiplicities for every admissible fibre. P(1), P'(1), parity and upper rate-class ceilings verified.
- Both-currency rate-class projector and swap-odd kernel invariance checked on all 37 fibres; 8 direct uncompressed O(N^2) rational pair sums; 4 strict distinct-rate Cauchy determinant cases with exact rational elimination and product formula. The general rank theorem follows from classical Cauchy determinant algebra, NOT extrapolation from four tests.
- The earlier independent R568 signed-bucket control (scripts/check_ns_r568_rate_bucket_bidi_exact_20261123.py) still gives unlifted F=46/16575>0 and rate-lifted L=-1/5<0 on two source-allowed rates (13,17) with arbitrarily supplied rational vector proxy carriers. It does NOT exhibit a single Galerkin trajectory producing those carriers.

New checker on PR #1543: scripts/check_ns_r568_centered_rate_radical_20261123.py, corrected to original k-within-C admissibility. Its source is committed and independently read back; the 37/37 executed tests above used a locally equivalent implementation. Agda, Lean and GitHub CI were NOT run.

## 5. Exact remaining original theorem obligations

1. **Native source partition/quotient:** instantiate B, Pi on literal PhysicalTriadIncidence and Output.physicalOutputFiber with original cutoff C, nonzero k, p/q swap and complete source/provenance sidecar. Preserve actual d->-d fixed point and non-injective quotient distinction. Prefer semantic module naming; don't rename the historical owners.
2. **Actual nonlinear D/M weld:** use precisely R567/R687 Row.D.doubleForcing and Row.doubleCell from the same physicalSystem at the same (C,k,time); consume R541's reciprocal law and existing Hermitian bilinearity. Do NOT infer actual forcing from arbitrary test vectors.
3. **Live source time lift:** use R240/R405/R495 on the real nonzero output and spacetime family, preserving sign before norms, reusing R624/R628/R634 integrations.
4. **UNPAID C1 analytic upper:** cutoff-independent signed original R568 inequality 4F_C(T,R,t) <= B(T,R,t). New rank compression alone does not bound the actual bucket amplitudes as C increases.
5. **UNPAID C2 analytic lower:** genuine original strict-margin 2 S_delta+G+H<=4F on same live packet, equivalent to original R653 payment. R687's rate lift does NOT produce an upper/lower comparison without additional signed source structure.
6. **R565 FTC / terminal / continuum:** actual scalar FTC, nonnegative self-flux terminal calibration, R406/R504 original and admissible 3D PDE global regularity. No universal Clay theorem follows from a finite kernel quotient.

**Status:** finite geometric theorem classically exact; tested source-admissible arithmetic and proxy vector algebra PASS; native Agda source implementation OPEN; C1/C2 signed spacetime estimates OPEN; Clay original endpoint 0/6.
