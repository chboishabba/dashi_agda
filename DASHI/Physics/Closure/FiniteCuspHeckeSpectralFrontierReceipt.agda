module DASHI.Physics.Closure.FiniteCuspHeckeSpectralFrontierReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Finite cusp/Hecke spectral frontier receipt.
--
-- This receipt records the finite Hecke spectral target for the weight-2
-- newform attached to X_0(49).  It is deliberately not the Z/7 Cayley graph
-- Laplacian receipt: the entries below are Hecke eigenvalues a_p.  The
-- CM distinction is explicit: good inert primes for Q(sqrt(-7)) vanish,
-- split primes need not vanish, and the ramified prime p=7 is separated
-- from the good-prime CM-vanishing rule.

data FiniteCuspHeckeSpectralStatus : Set where
  frontierHeckeEvidenceNoContinuumPromotion :
    FiniteCuspHeckeSpectralStatus

data FiniteCuspHeckeSpectralObject : Set where
  heckeOperatorOnS2X049 :
    FiniteCuspHeckeSpectralObject

data PreviousFiniteCarrierObject : Set where
  z7CayleyGraphLaplacian :
    PreviousFiniteCarrierObject

data CuspHeckeEvidenceComponent : Set where
  modularCurveX049 :
    CuspHeckeEvidenceComponent

  weightTwoCuspSpace :
    CuspHeckeEvidenceComponent

  newform49aOne :
    CuspHeckeEvidenceComponent

  heckePrimeEigenvalueTableUpTo20 :
    CuspHeckeEvidenceComponent

  cmVanishingDistinction :
    CuspHeckeEvidenceComponent

  normalizedScalarDiagnosticConventionSmallPrimes :
    CuspHeckeEvidenceComponent

canonicalCuspHeckeEvidenceComponents :
  List CuspHeckeEvidenceComponent
canonicalCuspHeckeEvidenceComponents =
  modularCurveX049
  ∷ weightTwoCuspSpace
  ∷ newform49aOne
  ∷ heckePrimeEigenvalueTableUpTo20
  ∷ cmVanishingDistinction
  ∷ normalizedScalarDiagnosticConventionSmallPrimes
  ∷ []

data CuspHeckeVerificationBoundary : Set where
  tableRecordedNotMatrixDiagonalizationProof :
    CuspHeckeVerificationBoundary

  normalizedScalarDiagnosticConventionOnly :
    CuspHeckeVerificationBoundary

  noContinuumMassGapPromotion :
    CuspHeckeVerificationBoundary

canonicalCuspHeckeVerificationBoundary :
  List CuspHeckeVerificationBoundary
canonicalCuspHeckeVerificationBoundary =
  tableRecordedNotMatrixDiagonalizationProof
  ∷ normalizedScalarDiagnosticConventionOnly
  ∷ noContinuumMassGapPromotion
  ∷ []

data CMPrimeClass : Set where
  cmSplitGood :
    CMPrimeClass

  cmInertGoodVanishes :
    CMPrimeClass

  cmRamifiedBadSeparated :
    CMPrimeClass

record PrimeHeckeEigenvalue : Set where
  constructor primeHeckeEigenvalue
  field
    prime :
      Nat

    ap :
      Nat

    cmClass :
      CMPrimeClass

open PrimeHeckeEigenvalue public

p2-ap : PrimeHeckeEigenvalue
p2-ap =
  primeHeckeEigenvalue 2 1 cmSplitGood

p3-ap : PrimeHeckeEigenvalue
p3-ap =
  primeHeckeEigenvalue 3 0 cmInertGoodVanishes

p5-ap : PrimeHeckeEigenvalue
p5-ap =
  primeHeckeEigenvalue 5 0 cmInertGoodVanishes

p7-ap : PrimeHeckeEigenvalue
p7-ap =
  primeHeckeEigenvalue 7 0 cmRamifiedBadSeparated

p11-ap : PrimeHeckeEigenvalue
p11-ap =
  primeHeckeEigenvalue 11 4 cmSplitGood

p13-ap : PrimeHeckeEigenvalue
p13-ap =
  primeHeckeEigenvalue 13 0 cmInertGoodVanishes

p17-ap : PrimeHeckeEigenvalue
p17-ap =
  primeHeckeEigenvalue 17 0 cmInertGoodVanishes

p19-ap : PrimeHeckeEigenvalue
p19-ap =
  primeHeckeEigenvalue 19 0 cmInertGoodVanishes

canonicalPrimeHeckeEigenvalueTableUpTo20 :
  List PrimeHeckeEigenvalue
canonicalPrimeHeckeEigenvalueTableUpTo20 =
  p2-ap
  ∷ p3-ap
  ∷ p5-ap
  ∷ p7-ap
  ∷ p11-ap
  ∷ p13-ap
  ∷ p17-ap
  ∷ p19-ap
  ∷ []

data SmallPrimeGapAvailability : Set where
  goodPrimeScalarDiagnosticAvailable :
    SmallPrimeGapAvailability

  ramifiedPrimeGapExcluded :
    SmallPrimeGapAvailability

record NormalizedGapConvention : Set where
  constructor normalizedGapConvention
  field
    prime :
      Nat

    availability :
      SmallPrimeGapAvailability

    convention :
      String

    normalizedGap :
      String

open NormalizedGapConvention public

normalizedGapConventionStatement : String
normalizedGapConventionStatement =
  "For good primes one may record the normalized scalar alpha_p = a_p/(2 sqrt p) and diagnostic delta_p = 1 - |alpha_p|; because S_2(X_0(49)) is one-dimensional, this is not an intrinsic Hecke eigenvalue-spacing gap."

p2-normalized-gap : NormalizedGapConvention
p2-normalized-gap =
  normalizedGapConvention
    2
    goodPrimeScalarDiagnosticAvailable
    normalizedGapConventionStatement
    "delta_2 = 1 - 1/(2 sqrt 2)"

p3-normalized-gap : NormalizedGapConvention
p3-normalized-gap =
  normalizedGapConvention
    3
    goodPrimeScalarDiagnosticAvailable
    normalizedGapConventionStatement
    "delta_3 = 1"

p5-normalized-gap : NormalizedGapConvention
p5-normalized-gap =
  normalizedGapConvention
    5
    goodPrimeScalarDiagnosticAvailable
    normalizedGapConventionStatement
    "delta_5 = 1"

p7-normalized-gap : NormalizedGapConvention
p7-normalized-gap =
  normalizedGapConvention
    7
    ramifiedPrimeGapExcluded
    normalizedGapConventionStatement
    "p=7 is ramified in conductor 49, so the good-prime normalized gap convention is not applied"

canonicalSmallPrimeNormalizedGapConventions :
  List NormalizedGapConvention
canonicalSmallPrimeNormalizedGapConventions =
  p2-normalized-gap
  ∷ p3-normalized-gap
  ∷ p5-normalized-gap
  ∷ p7-normalized-gap
  ∷ []

data CuspHeckePromotionToken : Set where

cuspHeckePromotionImpossibleHere :
  CuspHeckePromotionToken →
  ⊥
cuspHeckePromotionImpossibleHere ()

replacementStatement : String
replacementStatement =
  "Replace the finite Z/7 torsion Cayley graph with the actual Hecke operator on S_2(X_0(49)) as the finite cusp spectral target."

frontierStatement : String
frontierStatement =
  "The p<=20 Hecke eigenvalue table for the X_0(49) weight-2 CM newform is recorded here as finite frontier evidence."

distinctObjectsStatement : String
distinctObjectsStatement =
  "The Hecke scalar action on the one-dimensional cusp space and the Cayley-graph Laplacian gap on Z/7Z are distinct spectral objects; no Cayley graph gap is reused as a Hecke gap."

apTableStatement : String
apTableStatement =
  "Prime a_p table through 20: a_2=1, a_3=0, a_5=0, a_7=0, a_11=4, a_13=0, a_17=0, a_19=0."

cmVanishingStatement : String
cmVanishingStatement =
  "CM distinction: good inert primes p=3,5,13,17,19 vanish; split primes p=2,11 do not have to vanish; ramified p=7 has a_7=0 recorded as level-prime CM/ramified vanishing, not as a generic spectral-gap statement."

noContinuumStatement : String
noContinuumStatement =
  "This is finite cusp/Hecke spectral evidence only; it gives no continuum Yang-Mills result and no Clay Yang-Mills promotion."

oneDimensionalGapBoundaryStatement : String
oneDimensionalGapBoundaryStatement =
  "Since S_2(X_0(49)) is one-dimensional in the usual trivial-character convention, T_p acts by a scalar; no intrinsic multi-eigenvalue Hecke spectral gap is computed here."

record FiniteCuspHeckeSpectralFrontierReceipt : Set where
  field
    status :
      FiniteCuspHeckeSpectralStatus

    statusIsFrontierNoContinuumPromotion :
      status ≡ frontierHeckeEvidenceNoContinuumPromotion

    targetObject :
      FiniteCuspHeckeSpectralObject

    targetObjectIsHeckeOnS2X049 :
      targetObject ≡ heckeOperatorOnS2X049

    previousObjectReplaced :
      PreviousFiniteCarrierObject

    previousObjectReplacedIsZ7Cayley :
      previousObjectReplaced ≡ z7CayleyGraphLaplacian

    level :
      Nat

    levelIsFortyNine :
      level ≡ 49

    weight :
      Nat

    weightIsTwo :
      weight ≡ 2

    modularCurve :
      String

    modularCurveIsX049 :
      modularCurve ≡ "X_0(49)"

    cuspSpace :
      String

    cuspSpaceIsWeightTwo :
      cuspSpace ≡ "S_2(X_0(49))"

    heckeOperatorTargetRecorded :
      Bool

    heckeOperatorTargetRecordedIsTrue :
      heckeOperatorTargetRecorded ≡ true

    usesZ7CayleyGapAsHeckeGap :
      Bool

    usesZ7CayleyGapAsHeckeGapIsFalse :
      usesZ7CayleyGapAsHeckeGap ≡ false

    heckeAndCayleyGapsDistinct :
      Bool

    heckeAndCayleyGapsDistinctIsTrue :
      heckeAndCayleyGapsDistinct ≡ true

    exactApValuesReceiptedHere :
      Bool

    exactApValuesReceiptedHereIsTrue :
      exactApValuesReceiptedHere ≡ true

    heckeSpectralGapComputedHere :
      Bool

    heckeSpectralGapComputedHereIsFalse :
      heckeSpectralGapComputedHere ≡ false

    normalizedGapConventionRecorded :
      Bool

    normalizedGapConventionRecordedIsTrue :
      normalizedGapConventionRecorded ≡ true

    components :
      List CuspHeckeEvidenceComponent

    componentsAreCanonical :
      components ≡ canonicalCuspHeckeEvidenceComponents

    primeEigenvalueTable :
      List PrimeHeckeEigenvalue

    primeEigenvalueTableIsCanonical :
      primeEigenvalueTable ≡ canonicalPrimeHeckeEigenvalueTableUpTo20

    smallPrimeNormalizedGapConventions :
      List NormalizedGapConvention

    smallPrimeNormalizedGapConventionsAreCanonical :
      smallPrimeNormalizedGapConventions
      ≡ canonicalSmallPrimeNormalizedGapConventions

    verificationBoundary :
      List CuspHeckeVerificationBoundary

    verificationBoundaryIsCanonical :
      verificationBoundary ≡ canonicalCuspHeckeVerificationBoundary

    replacementSummary :
      String

    replacementSummaryIsCanonical :
      replacementSummary ≡ replacementStatement

    frontierSummary :
      String

    frontierSummaryIsCanonical :
      frontierSummary ≡ frontierStatement

    distinctObjectsSummary :
      String

    distinctObjectsSummaryIsCanonical :
      distinctObjectsSummary ≡ distinctObjectsStatement

    apTableSummary :
      String

    apTableSummaryIsCanonical :
      apTableSummary ≡ apTableStatement

    cmVanishingSummary :
      String

    cmVanishingSummaryIsCanonical :
      cmVanishingSummary ≡ cmVanishingStatement

    oneDimensionalGapBoundarySummary :
      String

    oneDimensionalGapBoundarySummaryIsCanonical :
      oneDimensionalGapBoundarySummary ≡ oneDimensionalGapBoundaryStatement

    continuumYangMillsPromoted :
      Bool

    continuumYangMillsPromotedIsFalse :
      continuumYangMillsPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    promotionFlags :
      List CuspHeckePromotionToken

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open FiniteCuspHeckeSpectralFrontierReceipt public

canonicalFiniteCuspHeckeSpectralFrontierReceipt :
  FiniteCuspHeckeSpectralFrontierReceipt
canonicalFiniteCuspHeckeSpectralFrontierReceipt =
  record
    { status =
        frontierHeckeEvidenceNoContinuumPromotion
    ; statusIsFrontierNoContinuumPromotion =
        refl
    ; targetObject =
        heckeOperatorOnS2X049
    ; targetObjectIsHeckeOnS2X049 =
        refl
    ; previousObjectReplaced =
        z7CayleyGraphLaplacian
    ; previousObjectReplacedIsZ7Cayley =
        refl
    ; level =
        49
    ; levelIsFortyNine =
        refl
    ; weight =
        2
    ; weightIsTwo =
        refl
    ; modularCurve =
        "X_0(49)"
    ; modularCurveIsX049 =
        refl
    ; cuspSpace =
        "S_2(X_0(49))"
    ; cuspSpaceIsWeightTwo =
        refl
    ; heckeOperatorTargetRecorded =
        true
    ; heckeOperatorTargetRecordedIsTrue =
        refl
    ; usesZ7CayleyGapAsHeckeGap =
        false
    ; usesZ7CayleyGapAsHeckeGapIsFalse =
        refl
    ; heckeAndCayleyGapsDistinct =
        true
    ; heckeAndCayleyGapsDistinctIsTrue =
        refl
    ; exactApValuesReceiptedHere =
        true
    ; exactApValuesReceiptedHereIsTrue =
        refl
    ; heckeSpectralGapComputedHere =
        false
    ; heckeSpectralGapComputedHereIsFalse =
        refl
    ; normalizedGapConventionRecorded =
        true
    ; normalizedGapConventionRecordedIsTrue =
        refl
    ; components =
        canonicalCuspHeckeEvidenceComponents
    ; componentsAreCanonical =
        refl
    ; primeEigenvalueTable =
        canonicalPrimeHeckeEigenvalueTableUpTo20
    ; primeEigenvalueTableIsCanonical =
        refl
    ; smallPrimeNormalizedGapConventions =
        canonicalSmallPrimeNormalizedGapConventions
    ; smallPrimeNormalizedGapConventionsAreCanonical =
        refl
    ; verificationBoundary =
        canonicalCuspHeckeVerificationBoundary
    ; verificationBoundaryIsCanonical =
        refl
    ; replacementSummary =
        replacementStatement
    ; replacementSummaryIsCanonical =
        refl
    ; frontierSummary =
        frontierStatement
    ; frontierSummaryIsCanonical =
        refl
    ; distinctObjectsSummary =
        distinctObjectsStatement
    ; distinctObjectsSummaryIsCanonical =
        refl
    ; apTableSummary =
        apTableStatement
    ; apTableSummaryIsCanonical =
        refl
    ; cmVanishingSummary =
        cmVanishingStatement
    ; cmVanishingSummaryIsCanonical =
        refl
    ; oneDimensionalGapBoundarySummary =
        oneDimensionalGapBoundaryStatement
    ; oneDimensionalGapBoundarySummaryIsCanonical =
        refl
    ; continuumYangMillsPromoted =
        false
    ; continuumYangMillsPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        replacementStatement
        ∷ frontierStatement
        ∷ distinctObjectsStatement
        ∷ apTableStatement
        ∷ cmVanishingStatement
        ∷ oneDimensionalGapBoundaryStatement
        ∷ noContinuumStatement
        ∷ []
    }

finiteCuspHeckeDoesNotReuseZ7Gap :
  usesZ7CayleyGapAsHeckeGap
    canonicalFiniteCuspHeckeSpectralFrontierReceipt
  ≡ false
finiteCuspHeckeDoesNotReuseZ7Gap =
  refl

finiteCuspHeckeApValuesReceiptedHere :
  exactApValuesReceiptedHere
    canonicalFiniteCuspHeckeSpectralFrontierReceipt
  ≡ true
finiteCuspHeckeApValuesReceiptedHere =
  refl

p2HeckeEigenvalueIsOne :
  ap p2-ap ≡ 1
p2HeckeEigenvalueIsOne =
  refl

p3CMInertHeckeEigenvalueVanishes :
  ap p3-ap ≡ 0
p3CMInertHeckeEigenvalueVanishes =
  refl

p5CMInertHeckeEigenvalueVanishes :
  ap p5-ap ≡ 0
p5CMInertHeckeEigenvalueVanishes =
  refl

p7RamifiedHeckeEigenvalueSeparated :
  cmClass p7-ap ≡ cmRamifiedBadSeparated
p7RamifiedHeckeEigenvalueSeparated =
  refl

p7RamifiedHeckeEigenvalueIsZero :
  ap p7-ap ≡ 0
p7RamifiedHeckeEigenvalueIsZero =
  refl

p11SplitHeckeEigenvalueIsFour :
  ap p11-ap ≡ 4
p11SplitHeckeEigenvalueIsFour =
  refl

p13CMInertHeckeEigenvalueVanishes :
  ap p13-ap ≡ 0
p13CMInertHeckeEigenvalueVanishes =
  refl

p17CMInertHeckeEigenvalueVanishes :
  ap p17-ap ≡ 0
p17CMInertHeckeEigenvalueVanishes =
  refl

p19CMInertHeckeEigenvalueVanishes :
  ap p19-ap ≡ 0
p19CMInertHeckeEigenvalueVanishes =
  refl

p7GoodPrimeNormalizedGapExcluded :
  availability p7-normalized-gap ≡ ramifiedPrimeGapExcluded
p7GoodPrimeNormalizedGapExcluded =
  refl

finiteCuspHeckeNoClayPromotion :
  clayYangMillsPromoted canonicalFiniteCuspHeckeSpectralFrontierReceipt
  ≡ false
finiteCuspHeckeNoClayPromotion =
  refl

finiteCuspHeckeNoPromotion :
  CuspHeckePromotionToken →
  ⊥
finiteCuspHeckeNoPromotion =
  cuspHeckePromotionImpossibleHere
