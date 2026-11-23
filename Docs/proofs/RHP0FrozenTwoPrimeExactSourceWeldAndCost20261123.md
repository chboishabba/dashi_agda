# RH/GRH P0 — frozen-online two-prime source weld, exact arithmetic coefficient, and E2 cost (23 Nov 2026)

**Mathematical and repository status:** Original Lean main **already** has an exact original-Zeta23 two-prime source via `Synthesis/RiemannSelectedPrimeSensitiveTwoScale.lean`. The current tranche does NOT re-invent that primitive. A source-native, **conditional** generalized frozen-online pair carrier with full theorem bodies has been added on [Lean PR #116](https://github.com/chboishabba/dashi_lean4/pull/116), `research/rh-p0-prime-aperture-frozen-source-20261123`, file `Synthesis/RiemannSelectedPrimeSensitiveFrozenApertureExact.lean`. Its inhabitance by a same-original-selected-W smooth eight-invariant aperture is still NOT proved in Lean. There has been **NO Lean 4.28 kernel compilation, no CI and no new Lean axiom-check receipt**. Local exact SymPy and numeric smooth-fixture regression is in [check_rh_p0_frozen_two_prime_weld_20261123.py](../../scripts/check_rh_p0_frozen_two_prime_weld_20261123.py). This is neither a proof of RH/GRH nor evidence that the original external Lean 4.33.1 root import has passed.

## 1. Reconcile ORIGINAL native prime source (E1 preexisting vs true E0 gap)

`Synthesis/RiemannSelectedPrimeSensitiveTwoScale.lean` already proves:

- `detectorTwoScale_at_log_two` and `detectorTwoScale_at_log_three`: independent exact translated source samples `e2*g(0)`, `e3*g(0)` for `|supp g|<1/4` at `t≥300`; `detectorTwoScale_at_log_nat_eq_zero_of_four_le`: every prime-power n≥4 is zero.
- `detectorTwoScale_primeTerm_eq_two_real_terms`: literal `vonMangoldt(n)/sqrt(n)` weights, retaining `cos((s-t)log n)`; `quarticFourPhysicalDetector_twoScale_primeChannel_eq`: *both* even-cone phases `cos(s log p) cos(t log p)`.
- `quarticFourPhysicalDetector_twoScale_primeProjective_eq` and `twoScaleSignedPrimeCombination_eq`: actual two-radius projective determinant with CHANGED on-line responses, and hence generally a **quadratic** function of the translation strengths.
- `twoScaleCompletedCluster_eq_off_add_arithmetic` and `twoScaleCompletedIncrement_exactPrime`: exact same-detector four-channel `cluster=offOrd+prime+Gamma+pole`; appearance of a prime summand changes the other channels too. Hence the prime term is not an independently signed completed gap.
- `Synthesis/RiemannSelectedPrimeSensitiveThreeTapMaxCutDecision.lean`, `...AdverseFinalCut.lean`: preexisting analytic PASS/FAIL compilers with unpaid signed budget. The P0 programme MUST reuse these rather than reauthor their theorem graph.

**New actual gap:** the translated `detectorTwoScale` has on-line Fourier changes. An eight-invariant correction can freeze the original two on-line responses, the original signed M2/M4/M6/M8 and both original pole coordinates. The new extended detector no longer is of the unmodified four-window `QuarticFourSignedPolePair` type. E0 must prove the new conditional carrier is inhabited by a real smooth `h` constructed from the original W, not just postulate the source fields.

## 2. Original normalized coefficient and the exact frozen prime formula (NO dropped factors)

Let r=t/16. For each signed endpoint `j=H,T`, take original physical detector `g_j` with

    A1_j = ∫_R g_j(u) cos(r u)du,
    A2_j = ∫_R g_j(u) cos(2r u)du,
    B_j(L) = A1_j cos(2rL) - A2_j cos(rL).

Its selected original pole coefficient is `P_H=W.poleHalf` or `P_T=W.poleTwo`. For any **even** extended `g'_j` with original source A1/A2 frozen and `g'_j(log n)=0` for n≥4, the exact original literal Zeta23 even-cone source is

    primeTerm(sampleTest g'_j t s)
      = 2 sum_(p=2,3) (log p/sqrt p)
            *g'_j(log p)*cos((s-t)log p)

    primeChannel g'_j t s
      = 4 sum_(p=2,3) (log p/sqrt p)
            *g'_j(log p)*cos(s log p)*cos(t log p).

The factor **4** is essential and is exactly sourced from the original `primeTerm` plus the symmetric `s/-s` cone: NOT a guessed factor 2 or 8. Therefore the original **signed pole-weighted projective prime** is EXACTLY

    P'_prime = 4 sum_(p=2,3) (log p/sqrt p) cos(t log p)
                [P_T*g'_H(log p)*B_H(log p)
                 -P_H*g'_T(log p)*B_T(log p)].

This is **linear in four prime-point amplitudes** only because the A1/A2 on-line projective columns are frozen. The old ordinary two-scale source is quadratic: shifting g by e2/e3 multiplies its A_s by `1+2e2 cos(s log2)+2e3 cos(s log3)`, with different factors at s=r and 2r; the eight constraints eliminate both changes EXACTLY, not just infinitesimally.

For the same **extended** physical pair, the original source's four-channel theorem and the frozen original pole coefficients yield

    Cluster' = OffOrd' + Prime' + Gamma' + Pole',
    Pole' = 0,
    Cluster' = OffOrd' + Prime' + Gamma'.

The **zero and Gamma channels here are evaluated on the new g'**, with the actual zeta multiplicities, the horizontal β and ordinate γ retained, and exact original `mu`. This is NOT an independent upper bound: algebraically it is the same Weil equality, now with a prime term. To get a contradiction one must independently bound `OffOrd'+Gamma'` and prime/local costs against the same-ordinate target, not choose a prime sign by hand.

## 3. Strong geometric nondegeneracy for suitably narrow original smooth W

The exact original atomic Fourier-response vectors are

    (A1_H,A2_H)=(1/2-muHalf,1+muHalf),
    (A1_T,A2_T)=(1/2-muTwo,5/6+muTwo).

Their determinant

    D = -1/12 -(4/3)muHalf +(3/2)muTwo.

At the original atomic null coordinates `muHalf=-1/78`, `muTwo=1/162`, `D=-20/351`. In the **entire source robustness corridor** `|muHalf+1/78|≤1/10000` and `|muTwo-1/162|≤1/10000`, the drift is bounded by `17/60000`, so

    D ≤ -20/351 + 17/60000 < 0.

This exact corridor inequality now has a theorem body `quarticFourPrimeApertureAtomicResponseDet_neg` in Lean PR #116 (kernel NOT checked). To transport D to ACTUAL smooth W, the original `RiemannProjectiveQuarticFourWindowLocalization.exists_radius_quarticFourWindowPairing_close_atomic` gives an arbitrarily small smooth A-vector error at small common R; choose R sufficiently small also for the selected `targetStrength≥7π^4/1600` and original signed moment constructor. Separately, `RiemannProjectiveQuarticFourWindowPoleLocalization.exists_radius_quarticFourSmoothPole_pos` gives both ORIGINAL pole coefficients >0 at sufficiently small R, for each t≥200. These are EXISTENTIAL small-R refinements, **not** a theorem that every arbitrary pre-existing W automatically has nonzero smooth determinant or strictly positive individual poles.

For any real z, `(cos(2z),-cos z)≠(0,0)`; indeed `cos z=0` implies `cos(2z)=-1`. Hence two nonproportional endpoint A-vectors cannot both have zero B_j(L) at the same L. And the phases `cos(t log2)` and `cos(t log3)` cannot both vanish (otherwise log3/log2 is a ratio of odd integers, impossible by unique factorization). Thus with *small-R selected original W* and independent original four-port evaluations one has a **nonzero available signed prime coefficient at every fixed high t**, after a supported smooth eight-invariant aperture. This is source-derived geometry; formalizing the smooth determinant positivity and full carrier inhabitation is E0, still OPEN.

## 4. Critical phase negative control: never simultaneously zero, yet arbitrarily close

The arithmetic pair of phases has **NO height-uniform positive lower bound**. The irrational number `log3/log2` generates a dense rotation: along `t_k=(k+1/2)π/log2`, `cos(t_k log2)=0` exactly, while the fractional parts of `(k+1/2)log3/log2` are dense mod 1. Therefore for every ε>0 and arbitrarily large t one has

    max(|cos(t log2)|, |cos(t log3)|) < ε.

High precision mpmath numerical controls (NOT theorem proof) give:

| k | t_k | exact first phase | abs second phase |
|---:|---:|---|---:|
| 485 | 2200.4608488571 | 0 | 0.00221764805529 |
| 7800 | 35354.6752863230 | 0 | 0.0000412322135520 |
| 39667 | 179787.3959259302 | 0 | 0.00000830491695953 |

Consequently **prime visibility does not furnish a uniform positive arithmetic signal or sign** for bounded port amplitudes. The unconditional all-height strict bound must handle *arbitrarily near-resonant* heights without dividing by either cosine or assuming a phase floor.

## 5. True smooth four-window finite-projection preflight: measured E2 debt

Executed locally with SymPy exact algebra, SciPy root solve and 160-point Gaussian quadrature using `b(x)=exp(-1/(1-x^2))` for |x|<1, 0 outside, R=0.0035. This is a **C∞ fixture**, NOT the actual noncomputably selected Mathlib `unitContDiffBump`. The source-constructed J2 nulls are solved numerically:

    muHalf = -0.012820708515659971,
    muTwo  = +0.006172574313334669,

and both J4 moments <0. Smooth Fourier-response determinant `D≈-0.0569799179318`, both original normalized pole responses positive and target `T≈2.08≥7π^4/1600`. Both endpoint eight-weight projection matrices (two Fourier responses, four projective moments, two literal pole weights) solve a source-specific RHS for each independent log2/log3 point port. 16 numerical solves at four heights, worst eight-row residual **1.87025×10^-18** and worst condition number about **9.06×10^6**. This is NOT exact proof of carrier inhabitance or a source-W kernel receipt.

Measured signed prime gradients (four independent endpoint/prime ports) and a **conservative triangle upper bound**, not an unavoidable minimum, for `||h''||_1` of this specific width-`δ=min(0.0014,0.14/t)` solver:

| t | max absolute signed prime gradient per unit port | max triangle ||h''||1 | source target strength |
|---:|---:|---:|---:|
| 300 | 0.048605 | 1.331×10^5 | 2.081652 |
| 1000 | 0.013566 | 4.066×10^5 | 2.080914 |
| 80000 | 0.0003694 | 3.627×10^7 | 2.080841 |
| 1000000 | 0.00002292 | 4.403×10^8 | 2.080841 |

The exact affine scaling of a height-one even bump gives `||∂^k h_δ||_1∝δ^(1-k)`, and of a normalized mass-one auxiliary gives `δ^(-k)`. The poor cost-versus-gain ratio in THIS narrow-bump construction is an E2 quantitative warning; **it is NOT a rigorous lower bound over all possible apertures**. Investigate fixed-width/oscillatory correction and adaptively selected smooth bases before asserting any general no-go.

## 6. Concrete source implementation, acceptance and priority

- [Lean PR #116](https://github.com/chboishabba/dashi_lean4/pull/116), base `main`, new `Synthesis/RiemannSelectedPrimeSensitiveFrozenApertureExact.lean`: generic exact prime 2+3 term, exact even cone and projective formula; explicit `QuarticFourFrozenPrimeAperture` conditional structure with original selected `W`, both smooth even endpoints, n≥4 sample zeros, frozen A1/A2, source M2/M4/M6/M8, and literal pole response; exact signed frozen linear prime coefficient, pole cancellation, and full four-channel and reduced source balance. Atomic nonproportionality theorem body also added. **Kernel/axiom check not run; draft.** Explicit carrier existence is NOT yet asserted.
- [DASHI RH PR #1533](https://github.com/chboishabba/dashi_agda/pull/1533), base `master`: executable new numerical regression, exact corridor and phase checks, full proof and P0 roadmap reconciliations. No GitHub CI used.

**Acceptance gates, source-first:** **E0** attach a real `C∞` finite-codimension eight-invariant solution to the Lean carrier, and prove the *same* selected W target band with perturbation amplitude and robust small-R nondegeneracy. **E1** completed generic original Weil channel exists conditionally and literal 2/3 source is now reused; kernel-check proposed weld rather than rebuild the existing TwoScale theorem. **E2** independently certify the FULL enlarged-support absolute sixth/eighth/Schwartz/far-shell and post-sixth local costs, including near-resonance heights, not just M4 or an SVD. **E3** prove a **new independent** signed arithmetic–zero/Gamma bound strong enough for the ACTUAL extended same-object strict terminal, with no hidden RH-positive assumption. No R2-S0/S1 closure, no RHS strict inequality, and **RH/GRH OPEN**.

**Attribution:** original Lean Zeta23 literal Weil source, TwoScale/ThreeTap source graph and RvM/zero/Gamma owners; elementary finite linear functionals versus point evaluations, unique factorization/irrational rotations, original four-window smooth robustness/pole localizations; DASHI exact frozen-online projection and source-specific local regression. Keep user-established original author/source reuse and JMD/DASHI distinctions.


## 7. NEW E0 exact constructive solution — even monic 52nd-order source-annihilator (not a numerical rank assumption)

The original eight source constraints are weighted integrals against the exact **physical** even weight family:

    w1(u)=cos(r*u),       w2(u)=cos(2*r*u),
    w3..w6(u)=u^k [A1*cos(2r*u)-A2*cos(r*u)], k=2,4,6,8,
    w7..w8(u)=cosh(u/2)*cos(t*u)*cos(c*r*u), c=1,2.

Here r=t/16 and A1,A2 are the **true original selected endpoint responses**. The original pole weights are read directly from `RiemannProjectiveQuarticFourWindowPoleSameObject.lean` and `quarticFourNormalizedPoleWeight`; no replacement source or assumed zero configuration is introduced.

Define the following constant-coefficient differential operator, **for every fixed t and original W**:

    D=d/du,
    A_(t,r)(D) = (D²+r²)^9 * (D²+4r²)^9
       * Π_{c=1,2} Π_{sigma∈{-1,+1}}
           [((D−1/2)²+(t+sigma*c*r)²)
            ((D+1/2)²+(t+sigma*c*r)²)].

This has degree 2·9+2·9+4·4=52 and **leading coefficient one**. Each four-degree pole factor is

    ((D−1/2)²+omega²)((D+1/2)²+omega²)
       = (D²+omega²+1/4)²−D²,

so the entire operator is EVEN in D: `A_(t,r)(-D)=A_(t,r)(D)`.

- For k≤8, `(D²+omega²)^(k+1)` annihilates `u^k cos(omega u)`, since the multiplier has roots ±i omega of multiplicity at least k+1. Power 9 hence annihilates every w1–w6 for omega=r,2r, for any actual A1,A2.
- `cosh(u/2)cos(tu)cos(c r u)` is the finite sum of exponential modes with `lambda=±1/2`, `omega=t±c r`. The four-pole factors annihilate each exactly, covering w7,w8 for both c=1,2.
- Choose an **even**, compact C∞ bump b supported in a tiny symmetric neighborhood of ±log2 and disjoint from ±log3, ±log n(n≥4), and the original core. Define `h_2=A_(t,r)(D)b`. Differentiation preserves compact support; evenness of the operator preserves evenness of the input.
- Integration by parts **52 times**, without boundary terms on the compact source, gives `∫ h_2(u)w_j(u)du=∫ b(u)A_(t,r)(-D)w_j(u)du=0` for EVERY one of the eight original constraints.
- Prescribe the **jet** of the starting bump at L=log2 by `b^(j)(L)=0` for 0≤j<52 and `b^(52)(L)=1`. For example, take `b(u)=(u-L)^52 *chi(u-L)/(52!*chi(0))` locally with `chi(0)≠0`, and symmetrize in a disjoint negative neighborhood. Because A is monic, `h_2(log2)=1`; disjoint supports force `h_2(log3)=0`. Repeat with log3 to produce `h_3(log2)=0,h_3(log3)=1`.

This is an explicit **mathematical C∞ construction** of the two independent eight-invariant prime-port basis functions, with NO generic rank hypothesis, NO t-dependent matrix inverse, and NO substitution of an atomic witness for the selected original W. It is stronger than the earlier abstract finite-codimension evaluation lemma. It applies separately to both original source endpoint detectors. The original `W` remains fixed and its same-object moment/pole fields unchanged exactly by adding arbitrary linear combinations of h2,h3.

**Acceptance:** Independently executed exact SymPy `scripts/check_rh_p0_exact_differential_annihilator_20261123.py` passed the even/monic/degree52 factors, all Fourier-polynomial root annihilations, the ±1/2 exponential pole modes, 52-jet values and the formal-adjoint identity. **Exact locally executed Git blob d06af1995d8b4f0e579122a31036e78db74a893e read back identical from PR #1533.** The source-construction strategy is also attached as a marked **non-kernel note** to Lean PR #116.

**Non-promotion:** This pays **E0 mathematical existence**, not **E0 Lean kernel inhabitation** or E2. The 52nd derivative raises severe source-specific smoothness costs: operator coefficients depend on t and r, the normalized v=r u support moves to O(t), and all sixth/eighth/Schwartz and full far-tail budgets must be redone. The current original `quarticSignedPoleExplicitK0` is NOT valid for this extension, and the old `combinedCluster_eq_offGamma` cannot be used after prime support opens. An order-8 variable-coefficient Wronskian adjoint, or a lower-norm finite projection, might be cheaper, but requires separate boundedness and possible Wronskian-zero controls; do not promote this possibility as proven. An independent strict signed RH bound remains E3.
