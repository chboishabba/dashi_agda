# BSD Agda-golden K1–K5 maximum cut — 13 November 2026

Selected ORIGINAL curve: `E : y² = x³ - x`, conductor 32, CM by `ℤ[i]`.
The Agda repository is the golden original-source carrier; Lean PR #107,
external libraries and papers are attributed DONORS only. No merge,
CI or source-description flag constitutes Agda 2.9 acceptance.

## Repositories and relevant checked source owners

Agda master owners audited directly:
- `DASHI/Mathematics/Arithmetic/EllipticCurveTwoTorsionAndBadPrimeExact.agda`:
  four actual affine/infinity torsion codes, xor group law, discriminant.
  It explicitly DOES NOT identify xor with the geometric group law.
- `DASHI/Mathematics/Arithmetic/EllipticCurveFiniteTwoDescentSeedExact.agda`:
  finite C₂×C₂ Kummer code homomorphism, injection and surjection only.
- `DASHI/Mathematics/Arithmetic/EllipticRationalKummerOpenExact.agda`:
  original rational x-T square-class pair ([x],[x-1]) for nonexceptional
  coordinates and literal cubic factorization.
- `DASHI/Mathematics/Arithmetic/EllipticRationalTwoTorsionKummerExact.agda`:
  original global representative dictionary below.
- `DASHI/Mathematics/Arithmetic/RationalSquareClassBitInvariantExact.agda`:
  quotient/setoid-respecting BIT compiler. It explicitly says original
  sign and v₂ arithmetic classifiers are still missing.
- `DASHI/Mathematics/Arithmetic/EllipticRationalPlaceSelmerExact.agda`:
  rational-place compiler, but NO actual local Q_v H¹/Kummer realization.
- `DASHI/Mathematics/Arithmetic/EllipticTwoDescentRoadExact.agda`:
  abstract Selmer element and Mordell–Weil/Sha interface, with no
  classical cohomological exactness producer.
- `DASHI/Mathematics/Arithmetic/EllipticFiniteSeedToSelmerExact.agda`:
  a conditional compiler requiring `FiniteSeedGlobalRealization`.
- `DASHI/Mathematics/Arithmetic/EllipticCurveSmallPrimeFrobeniusExact.agda`:
  seven actual fibre-count/Frobenius traces p=3,5,7,11,13,17,19.
- `DASHI/Mathematics/Arithmetic/SmallPrimeTruncatedEulerProductExact.agda`,
  `DASHI/Mathematics/Automorphic/TruncatedLFunctionExact.agda`,
  `DASHI/Mathematics/Automorphic/EllipticModularityReceiptExact.agda`:
  exact finite Euler polynomials/product agreements; modularity receipt
  is an interface and is not instantiated by the copied candidate traces.
- `DASHI/Mathematics/Automorphic/EllipticInfiniteLFunctionRoadExact.agda`,
  `DASHI/Mathematics/Automorphic/MellinSplitFunctionalEquationExact.agda`:
  infinite L/Mellin interfaces; Mellin concrete example is toy polynomial,
  NOT an integral over the original level-32 newform.
- `DASHI/Foundations/BishopBaselReciprocalSquareConvergenceExact.agda`:
  genuine constructive Basel series convergence.
- `DASHI/Mathematics/Automorphic/EllipticDirichletBaselMajorantExact.agda`:
  constructive comparison IF a literal original elliptic majorant
  is supplied; no all-n coefficient bounds provided.
- `DASHI/Analysis/BishopComplexSeriesConvergenceExact.agda`:
  componentwise Bishop-complex limit machinery, not the elliptic L-value.
- `DASHI/Mathematics/Arithmetic/BirchSwinnertonDyerBoundary.agda`:
  rank and leading-coefficient CONJECTURE records, no canonical inhabitants.

Relevant PRs/branches checked:
- Agda #449 and #457: historical arithmetic/automorphic frontiers, closed
  unmerged; their relevant original source owners are present on master.
- Agda #1408: current arithmetic/Bishop cross-domain branch; check exact
  applicable files before any source import; no automatic BSD admission.
- Agda #1478: Bishop-complex/log/exp convergence donors, not an elliptic L(E,1)
  identity or selected CM modularity proof.
- Agda #1497: Bishop/fast-Cauchy setoid and zeta witnesses, not selected BSD.
- Lean #39 merged and Lean #107 draft: genuine original local Qp and
  cohomological sources are donors with a DIFFERENT kernel; no Lean file
  proves an Agda declaration unless the same-object semantics are imported
  and locally checked.

## This PR: actual finite proofs, conditional source-preserving bridge

1. `EllipticSupportedSquareClassSieveExact.agda`
   - Four independent sign/2-valuation bits of a supported rational
     square-class pair; literal original torsion code dictionary.
   - Real diagonal-sign filter gives exactly 8 listed candidates.
   - Dyadic necessary condition first v₂ parity 0 gives exactly 4.
   - Constructive dependent proof `filteredSupportedCodeHasTorsionPreimage`,
     finite seed projection `filteredSupportedCodeRecoversFiniteSeed`.
   - Proof-relevant exhaustive membership for ALL 16 supported pairs,
     ALL 8 real-diagonal pairs, and ALL 4 filtered torsion pairs.
   - Four classifier projection on ORIGINAL RationalSquareClassPairRepresentative
     respects ORIGINAL RationalSquareClassPairEquivalent setoid.
   - **No** pretense that concrete rational sign, v₂ valuations, good
     prime unramifiedness or Q₂ full image are already realized in Agda.

2. `EllipticRationalPlaceTwoDescentProducerExact.agda`
   - Takes original RationalPlaceTwoDescentData and genuine SelmerTwoElement.
   - Demands EXPLICIT original square-class realization and original
     real/dyadic image ⇒ necessary-filter proofs.
   - Then produces an actual original TwoTorsionCode and its existing
     finiteKummerMap, WITH matching four-bit projection.
   - Does NOT identify the global H¹ class with the torsion class or
     declare the local-comparison evidence inhabited.

3. `EllipticSelectedHeckePrimePowerExact.agda`
   - Uses seven original checked Frobenius rows (NOT candidate newform data)
     and defines a_{p^k} via the genuine good-prime recurrence
       a_1=1, a_p=original trace,
       a_{p^(k+2)}=a_p a_{p^(k+1)}-p a_{p^k}.
   - Proves first/second coefficient and recurrence on literal checked rows;
     reuses the existing exact seven-prime Euler agreement.
   - Does NOT assert all-prime Frobenius, coprime multiplicativity,
     modularity, infinite Euler product, or analytic continuation.

## Exact unclosed mathematical gates (no Boolean promotion)

K1. Original H¹(G_Q,E[2]) ↔ rational square-class setoid and original
    H¹(G_Qv,E[2]) for ALL finite primes and real. Actual definition/proof
    of the sign and v₂ classifiers; good-prime support proof; actual
    Q₂ and real local elliptic Kummer images; all-place naturality.
    Even the four-bit map is NOT faithful on arbitrary global square classes.

K2. Actual geometric group, Galois action, and continuous Kummer connecting
    LES; same-object local E(Qbar_v); cohomological identification of
    Sel² / δ(E(Q)/2E(Q)) with CLASSICAL Sha(E/Q)[2].
    Defining an explicit cokernel does not by itself make it classical Sha.
    Correct sequence:
      0 → E(Q)/2E(Q) → Sel²(E/Q) → Sha(E/Q)[2] → 0.

K3. The finite sieve gives exactly four CODE values conditional on genuine
    arithmetic localization, NOT yet the full global Selmer subgroup.
    Prove original S-supported square-class completeness, injectivity/
    faithfulness, four actual local image certificates, and original
    rank=0 transport (MW finite-generation or Fermat descent).
    Then only Sha[2]=0 follows, NOT full Sha=0.

K4. Actual all-prime Hecke a_p (including correct bad p=2 local factor),
    all-n multiplicative coefficients, original level-32 newform f32
    and actual q/eta identity, explicit Fricke transformation,
    Bishop exponential/Mellin/infinite series limit with certified
    numerical/enclosure or exact Gamma/Beta same-object proof.
    The Basel-majorant comparison alone DOES NOT establish s=1.

K5. Odd-primary Sha(E)[p^∞] and full Sha cardinality,
    actual period/regulator/Tamagawa/torsion coefficient proof,
    original L(E,1)=BSD RHS in Bishop reals.
    Finiteness or corank-zero of odd p-primary Sha does NOT give
    vanishing. Universal BSD remains independent, unresolved.

## Attachment corrections: do not erase these types

- The correct 2-Kummer connecting target is H¹(G,E[2]), NOT H¹(G,E).
  E[2] ≅ μ₂×μ₂ only; the entire geometric E is NOT μ₂×μ₂.
- The actual original rational x-T torsion dictionary is:
    O→(1,1), (0,0)→(-1,-1), (1,0)→(1,2), (-1,0)→(-1,-2).
  The attachment's proposed (2,2) and (-2,1) survivors have odd
  first v₂ parity, and its (-1,-2) is NOT the global (-1,-1) class.
  Do not replace global classes by claimed local equivalences.
- Real necessary image is the diagonal {(+, +),(-,-)}, NOT x>0 only.
- Original conductor-32 curve has c₂=2 and Kodaira type III
  (not I₀*). Different isogenous curves have different local data.
- Published external nonzero L(E,1) formulas and numerical decimals
  do not become definitional equalities of the Agda Bishop object.
- Universal BSD is not solved by one rank-zero CM curve.

## Verification / authority boundary

Run from original repo in a local Agda 2.9/Nix environment:
  bash scripts/check_bsd_agda_k1_k5_local_maxcut.sh

This uses scripts/run_agda29_parallel_check.sh and rejects missing
sources, explicit postulates or known bypass switches.
**No Agda executable in the current session**: these are
source-written, GitHub-readback-only declarations, not kernel receipts.
Keep the PR draft and do not upgrade the status without exact local logs.
Attribution boundaries: Silverman/BSD arithmetic sources; original Agda
owners; CM/modular and Rubin/Kolyvagin published literature; Lean/mathlib
donors; Bishop/Murray vendored constructive real owners.


## Additional named-term donor audit: Hecke & Bishop

- `DASHI/Moonshine/AristotleHeckeGeneralPrimePowerDecompositionExact.agda`
  on master is a substantial *generic* source. It contains
  `agreeOnPrimePowerDecomposition` and
  `agreeOnAllowedPrimePowerDecomposition`, proving coefficient
  equality on a proof-carrying coprime prime-power decomposition
  from source prime agreement and valid Hecke systems. Its own
  boundary marks the raw-prime-factorisation → grouped-coprime-
  prime-powers normalization still false. It is NOT automatically
  an all-n selected elliptic Hecke theorem. In this audit a direct
  fetch of its imported `AristotleHeckeRecurrenceCoreExact.agda`
  at that master path returned 404, so the imported dependency
  must be reconciled locally before adopting the generic module
  into the original BSD dependency graph.
- `DASHI/Mathematics/NumberTheory/FiniteMultiplicativeDirichletExact.agda`
  proves finite monomial and coefficient multiplicativity on a
  supplied factorisation list, not actual unique factorization,
  the chosen `a_n`, or an infinite sum.
- Agda PR #1408 owns
  `DASHI/Analysis/BishopDirichletUniformBaselTailsExact.agda`,
  constructing uniform tail cutoffs from the **actual Bishop
  Basel series** under an all-index region majorant. This is
  a cross-PR donor; still need an actual original level-32
  Hecke/coefficient exponential majorant and same-object Mellin
  expression before transporting it into the elliptic L-function.
- Agda PR #1478 owns additional complex exp/finite convolution
  convergence donors, not the conductor-32 newform identity.
- Agda PR #1497's rational setoid transport is zeta-oriented,
  not the elliptic square-class and original L-series identity.

Next smallest useful K4 source cut is to reconcile the generic
Hecke recurrence import graph and connect the selected row recurrence
to its `NatHeckeClosureSystem` only after the actual all-prime
source coefficient and coprime multiplicativity are constructed.
Next K1 cut remains actual Agda sign and v₂ square-generator invariants,
then real/Q₂ Kummer image source proofs; the finite sieve does not
supply those physical/local-field arithmetic lemmas.
