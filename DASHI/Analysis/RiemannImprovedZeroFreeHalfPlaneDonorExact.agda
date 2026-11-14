module DASHI.Analysis.RiemannImprovedZeroFreeHalfPlaneDonorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG21ActualZetaHeightSeparationBoundary as G21Height

------------------------------------------------------------------------
-- External theorem/source authority.
--
-- This owner does NOT import a Lean proof term into Agda.  It pins the
-- independently replayed source and provides proof-relevant attachment sockets
-- for consumers that want to use its stronger zero-free region.
--
-- Liu Baiying's repository at the pinned revision below reports a strict Lean
-- 4.34.1 replay of the OAI foundation plus Parts I-IV and exports
-- CombineV22.zeta_nonzero for
--
--   Re(s) > B_inf = 0.874957019420098946...
--
-- with B_inf defined algebraically from the isolated cubic root.  The same
-- source explicitly states that this is neither RH nor boundary nonvanishing.
------------------------------------------------------------------------

record ImprovedZeroFreeLeanSource : Set where
  field
    repository : String
    revision : String
    replayDocument : String
    exportedZetaTheorem : String
    sourceBoundDecimal : String
    sourceOwnsKernelReplay : Bool
    sourceOwnsKernelReplayIsTrue : sourceOwnsKernelReplay ≡ true
    sourceClaimsRH : Bool
    sourceClaimsRHIsFalse : sourceClaimsRH ≡ false

open ImprovedZeroFreeLeanSource public

canonicalImprovedZeroFreeLeanSource : ImprovedZeroFreeLeanSource
canonicalImprovedZeroFreeLeanSource = record
  { repository =
      "https://github.com/liubaiying101/Improved-zero-free-half-planes-for-the-quasi-Riemann-hypothesis"
  ; revision = "46d612c2b63a163665ef560afca1965f7c8f434b"
  ; replayDocument = "README_on_lean.md"
  ; exportedZetaTheorem = "CombineV22.zeta_nonzero"
  ; sourceBoundDecimal = "0.874957019420098946..."
  ; sourceOwnsKernelReplay = true
  ; sourceOwnsKernelReplayIsTrue = refl
  ; sourceClaimsRH = false
  ; sourceClaimsRHIsFalse = refl
  }

------------------------------------------------------------------------
-- Exact rational safety cap used by the Agda consumers.
--
-- We deliberately round the externally proved decimal UP to
--
--   beta <= 0.874958 = 437479 / 500000
--
-- so the cross-prover adapter never depends on decimal equality.  On the
-- right half of the critical strip this gives
--
--   alpha = beta - 1/2 <= 187479 / 500000 = 0.374958.
--
-- The improvement over the old 3/8 target radius is certified without any
-- rational-order library: after cross multiplication,
--
--   3*500000 - 8*187479 = 168 = 8*21 > 0.
--
-- These normalization identities reduce by computation.
------------------------------------------------------------------------

safeBetaNumerator : Nat
safeBetaNumerator = 437479

safeDenominator : Nat
safeDenominator = 500000

safeAlphaNumerator : Nat
safeAlphaNumerator = 187479

sevenEighthsNumeratorAtSafeDenominator : Nat
sevenEighthsNumeratorAtSafeDenominator = 437500

safeBetaHalfShiftCrossProduct :
  2 * safeBetaNumerator ≡ safeDenominator + 2 * safeAlphaNumerator
safeBetaHalfShiftCrossProduct = refl

safeBetaImprovesSevenEighthsBy21Units :
  sevenEighthsNumeratorAtSafeDenominator ≡ safeBetaNumerator + 21
safeBetaImprovesSevenEighthsBy21Units = refl

safeAlphaImprovesThreeEighthsCrossProduct :
  3 * safeDenominator ≡ 8 * safeAlphaNumerator + 168
safeAlphaImprovesThreeEighthsCrossProduct = refl

crossProductGapIsEightTimes21 : 168 ≡ 8 * 21
crossProductGapIsEightTimes21 = refl

------------------------------------------------------------------------
-- Cross-prover theorem attachment.
--
-- `ImprovedRightBound rho` is intentionally supplied by the adapter.  Source
-- metadata alone cannot inhabit it.  This is the precise place where a future
-- theorem-bearing Lean<->Agda transport or an Agda re-proof plugs in.
------------------------------------------------------------------------

record ImprovedZeroFreeZetaAttachment : Set₁ where
  field
    Zero : Set
    IsNontrivialZero : Zero → Set
    RightOfCriticalLine : Zero → Set
    ImprovedRightBound : Zero → Set

    source : ImprovedZeroFreeLeanSource

    improvedBoundFromExternalTheorem :
      (rho : Zero) →
      IsNontrivialZero rho →
      RightOfCriticalLine rho →
      ImprovedRightBound rho

    exactSameZetaObject : Set
    exactSameZetaObjectReceipt : exactSameZetaObject

open ImprovedZeroFreeZetaAttachment public

------------------------------------------------------------------------
-- G21 consumer recut.
--
-- G21 currently knows only 0 < |alpha| < 1/2 on actual zeta zeros.  The new
-- donor can sharpen the upper domain to the safe 187479/500000 cap, but that
-- still does NOT prove x*coth(x) monotonicity, continuum moment separation,
-- Taylor remainder control, either actual parity minor, or transversality.
------------------------------------------------------------------------

record G21ImprovedHeightDomain
    (strictSource : G21Height.ActualZetaStrictStripSource)
    (heightProducer : G21Height.ActualZetaHeightSeparationProducer strictSource) : Set₁ where
  field
    SafeCap : Set
    safeCap : SafeCap
    ImprovedStrictlyBelow :
      G21Height.Height heightProducer → SafeCap → Set

    improvedHeightBound :
      (rho : G21Height.Zero strictSource) →
      G21Height.IsNontrivialZero strictSource rho →
      G21Height.offLineNoncritical heightProducer rho →
      ImprovedStrictlyBelow
        (G21Height.offLineHeight heightProducer rho)
        safeCap

    safeCapRepresents187479Over500000 : Set
    safeCapRepresents187479Over500000Receipt :
      safeCapRepresents187479Over500000

    sameOffLineHeightAsG21 : Set
    sameOffLineHeightAsG21Receipt : sameOffLineHeightAsG21

open G21ImprovedHeightDomain public

------------------------------------------------------------------------
-- Hybrid-bootstrap / scalar-obstruction probe.
--
-- The external optimality result is explicitly scoped to its supplied
-- positive/moment estimate system.  This generic interface tests the only
-- scientifically useful cross-pollination question: does a SAME-OBJECT signed
-- correction change the terminal scalar?  It cannot manufacture such a
-- correction.  If one is supplied, `hybridStepChanges` makes the required
-- non-collapse proof explicit.
------------------------------------------------------------------------

record SignedHybridObstructionProbe {Scalar : Set} : Set₁ where
  field
    positiveSystemStep : Scalar
    signedHybridStep : Scalar
    SameScalar : Scalar → Scalar → Set
    StrictlyBetter : Scalar → Scalar → Set

    signedCorrectionSameObject : Set
    signedCorrectionSameObjectReceipt : signedCorrectionSameObject

    hybridStepChanges :
      SameScalar signedHybridStep positiveSystemStep → Set

    hybridStrictImprovement : Set
    hybridStrictImprovementReceipt : hybridStrictImprovement

    provesConvergenceToHalf : Bool
    provesConvergenceToHalfIsFalse : provesConvergenceToHalf ≡ false

open SignedHybridObstructionProbe public

------------------------------------------------------------------------
-- Terminal accounting.
------------------------------------------------------------------------

record ImprovedZeroFreeDonorBoundary : Set where
  constructor improved-zero-free-donor-boundary
  field
    externalLeanSourcePinned : Bool
    externalLeanSourcePinnedIsTrue : externalLeanSourcePinned ≡ true

    externalKernelReplayReported : Bool
    externalKernelReplayReportedIsTrue : externalKernelReplayReported ≡ true

    exactLeanTheoremImportedIntoAgda : Bool
    exactLeanTheoremImportedIntoAgdaIsFalse :
      exactLeanTheoremImportedIntoAgda ≡ false

    rationalTargetWindowStrictlySharperThanSevenEighths : Bool
    rationalTargetWindowStrictlySharperThanSevenEighthsIsTrue :
      rationalTargetWindowStrictlySharperThanSevenEighths ≡ true

    g21HeightDomainSharpeningAvailable : Bool
    g21HeightDomainSharpeningAvailableIsTrue :
      g21HeightDomainSharpeningAvailable ≡ true

    g21ParityMinorPaidByDonor : Bool
    g21ParityMinorPaidByDonorIsFalse : g21ParityMinorPaidByDonor ≡ false

    signedHybridProbeInterfaceConstructed : Bool
    signedHybridProbeInterfaceConstructedIsTrue :
      signedHybridProbeInterfaceConstructed ≡ true

    externalPositiveSystemOptimalityRulesOutSignedMethods : Bool
    externalPositiveSystemOptimalityRulesOutSignedMethodsIsFalse :
      externalPositiveSystemOptimalityRulesOutSignedMethods ≡ false

    signedA1A2BProducerPaidByDonor : Bool
    signedA1A2BProducerPaidByDonorIsFalse :
      signedA1A2BProducerPaidByDonor ≡ false

    riemannHypothesisDerived : Bool
    riemannHypothesisDerivedIsFalse : riemannHypothesisDerived ≡ false

    highestAlphaReading : String

canonicalImprovedZeroFreeDonorBoundary : ImprovedZeroFreeDonorBoundary
canonicalImprovedZeroFreeDonorBoundary =
  improved-zero-free-donor-boundary
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    "The pinned Liu/OpenAI Lean development supplies an independently kernel-audited zeta zero-free half-plane B_inf=0.874957019420098946...; this Agda owner uses the conservative rational cap beta<=437479/500000 and hence alpha<=187479/500000 once an exact same-zeta cross-prover attachment is supplied. The cap is strictly inside 7/8 (and its horizontal radius strictly inside 3/8) by exact Nat normalization. G21 may consume the smaller height domain, but its sinh/cosh TP2, continuum moment, Taylor/minor and pole-quotient transversality producers remain open. G2/A1/A2/Route-B signed producers also remain open. The external optimality statement is scoped to its supplied positive estimate system, so a same-object signed correction is a lawful frontier probe rather than being ruled out by that optimality. No RH theorem is promoted."
