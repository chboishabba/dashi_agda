# YM P0 — original Wilson C3 source Gram to same-OS spectral faithfulness (22 Nov 2026)

**Status:** source-first audit + standard conditional spectral theorem + independently executed exact SymPy negative control. No original continuous SU(N) Haar / full complex reflected OS form / continuum physical Hamiltonian / Clay mass gap is constructed or certified here. No Agda 2.9 kernel run.

## Owned, nonduplicate source chain

- `YMClaySide4SpatialC3WilsonNaturalityExact`: spatial xyz rotation FIXES Euclidean time and acts on original periodic side-four gauge fields and closed Wilson holonomies; this is **not** internal gauge conjugation.
- `YMClayNativeSideFourC3VectorWeldExact`, `YMClaySUNMatrixProductHaarC3Exact`, `YMClaySUNMatrixSpatialC3RealFubiniExact`: native 1,024 positive bonds, C3 vector permutation and actual product-Haar change-of-variables.
- `YMClayOriginalWilsonC3WeightedHaarTransferExact`: the literal original Wilson Gibbs density/partition; normalized C3 invariance follows **conditional on** the canonical label identity and actual full-density invariance (including selected CMP119 E/R/B/V terms). Product-Haar permutation alone is not weighted Gibbs invariance.
- `YMClayOriginalC3WeightedOSGramBidiExact` on master-based PR #1536: finite REAL Wilson reflected-Gram C3 invariance and null predicate, conditional on original weighted invariance and an original reflection commuting with the same spatial C3. This is not full complex positive-time OS reflection positivity.
- `YMClayOriginalR445PublishedWilsonRPWordWeldExact`, `BalabanClayT5OSGramTopologyExact`, `YangMillsClayPinnedCMP119OSReconstructionExact`: original Wilson RP/source, complete complex Gram convergence and SAME CMP119 pre-gap OS system, respectively; their physical source identification and analytic hypotheses are NOT furnished by finite real Gram transport.
- Existing `YMClayD2ObservedDecayDoesNotForceFullSpectralGapExact` and `Docs/physics/YMClayOriginalOSDenseTestAutocorrelationGapCut20261109.md` already contain the hidden-mode and no-uniform-rate controls and the dense SAME-OS spectral theorem. This note refines their **C3** application; it does not duplicate those results.
- The 22-Nov original affine W1/W3 bad-sector and finite labelled marked Wilson Mayer sources on PR #1536 take precedence over generic KP analogies. In particular the literal unrenormalized microscopic Mayer singleton does NOT satisfy the physical small-activity hypothesis at large beta. The renormalized original global affine-label CMP116/119/122 response attachment remains necessary.


## New native full-Gram-row source consumer (22 Nov follow-up)

`DASHI/Physics/YangMills/YMClayOriginalC3GramRowEquivalenceBidiExact.agda` is now SOURCE-WRITTEN on original master-based YM #1536, explicitly imported into `DASHI/Unified/YMClayOriginalWilsonPhysicalRegression.agda` and targeted by the fail-closed local Agda runner. It consumes the *same original weighted finite real reflected Gram* (no new measure): defines `F ~_G G` precisely when `Gram(F,K)=Gram(G,K)` for **every** original test K, proves reflexivity/symmetry/transitivity, and derives spatial C3 preservation of this full row relation for arbitrary unrotated K via the original C3³=id and original reflection-weighted invariance. It separately preserves a full zero Gram row. That is stronger than looking only at a zero diagonal and uses no arbitrary equivalence between Fourier cancellation and OS null.

The carrier is still the finite real source bilinear form. The positive-semidefinite complex OS radical, quotient completion, actual E1 physical C3 unitary and time-semigroup commutation remain unpaid. This new Agda source has **NOT** been kernel checked because the local Agda executable is unavailable here; it must not be cited as kernel-accepted. The original 54/54 SymPy numerical/symbolic countermodel checks are independent and DO NOT test this Agda declaration.

## The physical, typed correspondence required

Let `D_+` be the **actual** gauge-invariant, positive-Euclidean-time original Wilson cylinder algebra for the same E1 limit, `theta` its published Wilson time reflection, and `S` the original spatial xyz C3 pullback. The desired complex sesquilinear form is

    <F,G>_OS := E_E1[ conjugate((theta F)) G ].

The **whole finite complex Gram quadratic** must be RP-nonnegative and converge in the existing T5 Gram topology, not just a diagonal real expression. Define `N={F:<F,F>_OS=0}`; by Cauchy–Schwarz for a positive semidefinite form this is its radical. Need (a) literal weighted source invariance and theta*S=S*theta; (b) <SF,SG>_OS=<F,G>_OS on ALL cross terms; (c) S preserves the positive-time algebra and `N` so `U_C3[F]=[SF]` extends as a unitary on the **same** completed `H_OS`; (d) `U_C3 Omega=Omega`; and (e) `U_C3 T(t)=T(t) U_C3` for that SAME physical `T(t)=exp(-tH_OS)`, all real t>=0. Temporal commutation is not a consequence of a single-time Gram identity.

The Eisenstein coefficient `omega` is a primitive complex cubic root, *not* scalar zero and not the nontrivial zero-energy state. On the complexified same OS Hilbert space, after a genuine unitary C3 action, define `P_chi=(I+conj(chi)U_C3+conj(chi)^2 U_C3^2)/3` for chi in {1,omega,omega²}. These are mutually orthogonal Hermitian projections with sum I and commute with H_OS only once (e) holds. An internal gauge C3 that acts trivially on gauge-invariant Wilson tests cannot substitute for the original spatial rotation.

## Exact density lemma (standard, not a new physical estimate)

If `D = span{[F]-<Omega,[F]> Omega : F in D_+}` is already norm dense in `Omega^perp` of the **same** OS Hilbert space, then `P_chi D` is dense in `P_chi(Omega^perp)` for each chi: for y=P_chi y choose x_n in D with x_n -> y and use boundedness to obtain P_chi x_n -> y. In particular the THREE projected original sectors together are dense; separate axioms postulating sector-density are unnecessary. The uninhabited physical input is the original dense `D`, its E1 identification and the complete C3/semigroup transport.

A single exponent `m>0` shared by all projected actual original physical-time autocorrelations `<psi,T(t)psi> <= C_psi exp(-mt)` (with finite psi-dependent prefactors) then excludes every spectral interval [0,lambda] below m on the full nonvacuum space by the spectral theorem. Different exponents for different sectors, or dependence on cutoff, are insufficient. This is precisely the already existing 9-Nov dense-D2 theorem, instantiated to C3—not a new Hamiltonian.

## Local exact source-Gram / countermodel regression

`scripts/check_ym_c3_gram_os_sector_faithfulness_20261122.py`: 54/54 exact SymPy 1.14 symbolic checks PASS (independently executed; no CI). Input `mu=13684/15451`, original Q8 Wilson three-observable raw Gram `M_ii=1`, `M_ij=12541/15451` (i != j), exactly as enumerated by the existing `check_ym_eisenstein_c3_original_wilson_gram_20261122.py` over 4,096 finite Q8 link configurations. Centering yields eigenvalues

    lambda_1 = 64519815/238733401 > 0;
    lambda_omega = lambda_omega2 = 2910/15451 > 0.

The new script checks all three exact Eisenstein projectors; C3 equivariance of the ORIGINAL finite covariance; a rank-four finite isometry from a five-coordinate form containing one added vacuum and one **explicitly artificial** null fibre; and formal-quotient C3 descent. A nonzero cancelling Fourier vector remains physically nonzero **in this finite model**. The vacuum and artificial null remain distinct.

A deliberately MODEL-ONLY, C3-commuting self-adjoint quotient family is `H_n=diag(0,2,1/n,1/n)` in vacuum, 1, omega, omega² coordinates for integers n>=2. Its invariant Wilson observable decays at exponent 2; the two nontrivial C3 sectors decay at 1/n. Each finite n has gap 1/n, but across n there is no common positive gap: for any m>0 choose n>1/m. The script verifies same-model intertwining, noncollapse and C3 commutation for n=2,3,7,31,127. **H_n is NOT the actual Wilson/OS Hamiltonian**; this only rules out a false inference from a selected C3 sector. The earlier repository negative controls remain the canonical general references.

## Source-specific maximum cut and receipts

1. Prove original ordered SU(N) plaquette trace/inversion and the closed native C3 canonical-label equality for the **entire** CMP119 Gibbs action, including E/R/B/V. No arbitrary C3-invariant surrogate weighting.
2. Prove the selected original Wilson theta commutes with native spatial C3; attach original finite Wilson RP to its full COMPLEX positive-time reflected Gram (not merely the existing finite REAL product) and original marked W1/W3 source.
3. Prove cutoff-compatible whole Gram limits and actual SAME E1 `PinnedCMP119PreGapOSReconstruction` quotient/semigroup unitary, preserving N, Omega and all three sectors.
4. Pay the actual full SU(N), all-cutoff D1 marked renormalized CMP116 response, GOOD discrepancy, BAD channel and physical rooted-shell common rate on the actual dense source family, then invoke the existing dense D2 spectral theorem. The original affine global two labels and all 896 residual links remain in the same Wilson source.
5. Maintain BSD E32 2-isogeny/dual Kummer/kernel and Lean E36 Eisenstein j=0 as **different curves**. Neither has a defined map to YM H_OS. Keep H05 six-face binary address cube, full zero-aware 27 strata and independent indices separate from the C3 projector algebra.

**Evidence classification:** original source owners SOURCE-WRITTEN; local finite checks LOCAL_REFERENCE_PASS; complex OS time/RP and renormalized D1 SOURCE_UNPAID; Agda kernel KERNEL_PENDING; E1/D1/D2/N1/G1 OPEN. Credit Wilson, Haar, Osterwalder–Schrader, Menotti–Pelissetto, Bałaban and the existing DASHI theorem owners; no novelty or proof-completion claim for standard finite-group or spectral-theorem facts.

## 22 November P0 exact original C3/time-mirror junction

The same-source module `DASHI/Physics/YangMills/YMClayOriginalWilsonSpatialC3TimeMirrorBIDIExact.agda` is now written and imported into the original physical regression root. It reuses `YMClayOriginalR445ReflectedPointwiseWordWeldExact.reflectOriginalFineLinks` **without changing temporal-link inversion**, and the native `YMClayNativeSideFourC3VectorWeldExact.forwardBond/forwardVector`. The four original axes are split explicitly; pointwise field compatibility is lifted using the original canonical 1024-link `Codec.encodeOriginalBonds/decodeOriginalBonds` (no function extensionality). The resulting `actualOriginalMirrorC3Vector` instantiates the earlier weighted real Gram and full-row theorems with the ACTUAL selected R445 time mirror instead of a caller-invented reflection.

Local independent exact SymPy 1.14.0 reference: `scripts/check_ym_original_wilson_c3_time_mirror_20261122.py`, 11,268/11,268 checks PASS, including all 1,024 original bonds, 8,192 Q8 inverse probes, exact `S^3=1`, `theta^2=1`, commuting index permutations and a rejected time/space-swap negative control. Agda source is **not kernel accepted**: the executable is unavailable in this environment; the local runner includes the module but has NOT been run.

**What this pays:** the original finite native time-mirror/spatial-C3 index compatibility, *conditional on kernel acceptance*. **What it does not pay:** the original six-plane CMP119 E/R/B/V physical-density invariance, the source canonical-label certificate, continuous Haar, positive-time Wilson-test closure, full complex reflection-positive Gram, E1 cutoff-convergent OS Hilbert quotient, a same-Hamiltonian semigroup or D1/D2 common positive rate. In particular, a Q8/finite pointwise test is not a proof of physical Wilson Gibbs covariance.


### Same-source pure Wilson versus extra CMP119 terms: correction

The selected finite density in `YMClayOriginalWilsonC3WeightedHaarTransferExact` is **definitionally** `YMClaySUNVariablePeriodicGibbsGaugeExact.periodicSUNGibbsDensity` at `n=3`. Inspection of its body shows `exp(-beta * periodicSUNSixDeficit)`, with all 256 original sites and six plaquettes per site. **It does not, by that definition alone, contain any additional independently selected CMP119 E/R/B/V contributions.** Do not accidentally treat a theorem about this six-plane density as a theorem about extra action terms.

Existing upstream producer `YMClaySUNNativeSixPlaneFullC3FromInverseTraceExact.nativeSUNWilsonGibbsDensityC3` already derives native finite six-plane C3 density invariance **conditional on the actual SU(N) real trace-of-inverse authority**, using `YMClaySUNMatrixNativeSixPlaneC3FromInverseTraceExact` and `YMClaySUNMatrixSpatialC3RealFubiniExact`. Therefore the next original P0 weld is specifically: (1) establish a *source-verified*, pointwise same-field/same-sum `periodicSUNSixDeficit(n=3)` ↔ `nativeSUNSixWilsonDeficit` identification (including source site order and original link field), (2) compose the **existing** native full-C3 density theorem with the original native-vector codec without assuming function extensionality, (3) separately account for any genuinely additional CMP119 terms and their own covariance instead of silently smuggling them into the pure Wilson measure. None of these three steps is claimed completed by the time-mirror commit. Full original Haar/canonical-label closure remains another independent premise.

## 22 Nov 2026 — P0 native n=3/Variable pure-Wilson C3 density BIDI, exact local acceptance

**Source-written on master-based YM PR #1536; Agda kernel NOT RUN.** New `DASHI/Physics/YangMills/YMClayOriginalWilsonN3NativeC3DensityBIDIExact.agda` is imported into the original physical regression root and included in the fail-closed **local** Agda acceptance runner (not CI). It establishes a conditional, same-source chain:

```text
original n=3 periodicSUNSixDeficit
  -> (original positive signed SU(N) plaquette identity)
  -> (flat canonical 4^4-site fold = original native nested sum)
  -> original nativeSUNSixWilsonDeficit
  -> SAME original exp(-beta * deficit) Gibbs density
  -> existing native full-six-plane C3 theorem (real trace-inverse donor)
  -> native 1024-vector codec/pointwise density
  -> original actual WilsonC3 weighted Gibbs action C3 condition
  -> prior original weighted-Haar normalized expectation
  -> prior actual R445 temporal-mirror real Gram C3
```

This **removes the need to postulate a separate pure-Wilson C3 density-invariance premise**, *provided* the actual native real trace-inversion authority and Agda kernel acceptance are supplied. The independent 1024-label adjacent-swap permutation certificate is **still unproved**, and genuine SU(N) continuous Borel Haar/integrability is still missing.

The flat canonical `Torus.elements (periodicTorus4Finite 4)` sum is **not literally definitionally the same expression** as `Gibbs.sumSitesReal`: four nested right-associated sums carry intermediate real zero terms. The new source uses original additive associativity and identity to prove `realSumCartesian`, plus the literal four-index equality, instead of incorrectly claiming `refl`. The original `Variable.sideFourPlaquetteSameNativeWilsonTrace` owns positive-plaquette identity, while `YMClaySUNNativeSixPlaneFullC3FromInverseTraceExact` owns the physical native C3 producer. Neither theorem is reimplemented.

**Local exact SymPy 1.14.0 acceptance:** `scripts/check_ym_original_six_plane_native_variable_20261122.py`, **29,774/29,774 PASS**; the committed blob is byte-for-byte equal to the locally run file (Git blob SHA `657ce62e19f687ce067caa51c86be4c799196921`). Original 256 sites, 1,024 bonds, all six positive planes (1,536 per field), 8 deterministic noncommutative Q8 link fields; 12,288 signed-path versus independent explicit four-factor holonomies, 12,288 C3 plaquette real traces, 2,048 same-site deficits; C3^3, theta^2, pointwise orientation/inversion and field commutation, local gauge and full-action/density agreements, and rejected anisotropic/time-mixing negative controls. This is a **finite Q8 exact regression**, not a general SU(N) proof or continuous Haar/OS acceptance.

**Important physical-source firewall:** `Variable.periodicSUNGibbsDensity n=3` is the original **pure six-plane Wilson** exponential. The conditional C3 theorem does **not** establish covariance of any additional independently selected CMP119 E/R/B/V terms. Those terms require their own actual action/source correspondence and symmetry proof, or a demonstrated identity to the selected pure-Wilson action. Nothing here constructs the complex positive-time RP form, cutoff-dependent E1 physical continuum, same-H OS unitary/semigroup, full D1 quantitative rooted-shell rate, D2 all-three-sector gap, N1/G1. Keep the independent Eisenstein C3 characters and all H05 zero/ternary distinctions.

**Receipt:** SOURCE_WRITTEN; LOCAL_SYMPY_EXACT_PASS; KERNEL_PENDING; ORIGINAL_COMPLEX_OS_AND_FULL_CLAY_OPEN. Standard Wilson, Bałaban, Haar, Osterwalder–Schrader and earlier DASHI producers retain attribution.

