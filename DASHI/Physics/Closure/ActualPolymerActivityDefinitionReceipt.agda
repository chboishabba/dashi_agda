module DASHI.Physics.Closure.ActualPolymerActivityDefinitionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMKPActivityRatioMarginReceipt as ToyRho

------------------------------------------------------------------------
-- Actual polymer activity definition frontier.
--
-- This receipt guards the earlier toy rho(k) margin profile.  The toy rho
-- profile is retained only as a diagnostic witness.  A promotable KP margin
-- must instead be stated against an actual carrier Wilson activity:
--
--   activity(P) = Wilson-action weight of a same-prime p=7 carrier polymer P
--
-- together with the p=7 Bruhat-Tits branching data, polymer support,
-- overlap predicate, compatibility weight, and local KP sum target.  This
-- file defines that interface and the promotion boundary only.  It does not
-- prove the analytic Kotecky-Preiss estimate, Balaban/RG transfer,
-- continuum Yang-Mills, a mass gap, or Clay.

data ActualPolymerActivityStatus : Set where
  actualCarrierWilsonActivityFrontierRecorded :
    ActualPolymerActivityStatus

data PolymerActivityKind : Set where
  toyDepthRhoDiagnostic :
    PolymerActivityKind

  actualCarrierWilsonActivity :
    PolymerActivityKind

data P7PolymerSupportDatum : Set where
  samePrimeP7Lane :
    P7PolymerSupportDatum

  finiteBTPathOrSubtree :
    P7PolymerSupportDatum

  plaquetteWilsonLoopBoundary :
    P7PolymerSupportDatum

  carrierDepthAndScale :
    P7PolymerSupportDatum

canonicalP7PolymerSupportData :
  List P7PolymerSupportDatum
canonicalP7PolymerSupportData =
  samePrimeP7Lane
  ∷ finiteBTPathOrSubtree
  ∷ plaquetteWilsonLoopBoundary
  ∷ carrierDepthAndScale
  ∷ []

data CarrierWilsonActivityDatum : Set where
  wilsonLoopPhase :
    CarrierWilsonActivityDatum

  wilsonActionWeight :
    CarrierWilsonActivityDatum

  polymerBoundaryTrace :
    CarrierWilsonActivityDatum

  activityNormOrAbsoluteWeight :
    CarrierWilsonActivityDatum

  betaCMinMinusAWeight :
    CarrierWilsonActivityDatum

canonicalCarrierWilsonActivityData :
  List CarrierWilsonActivityDatum
canonicalCarrierWilsonActivityData =
  wilsonLoopPhase
  ∷ wilsonActionWeight
  ∷ polymerBoundaryTrace
  ∷ activityNormOrAbsoluteWeight
  ∷ betaCMinMinusAWeight
  ∷ []

data SamePrimeP7KPDatum : Set where
  p7PrimeValue :
    SamePrimeP7KPDatum

  p7BTValencyEight :
    SamePrimeP7KPDatum

  p7BranchingFactorSeven :
    SamePrimeP7KPDatum

  samePrimeOverlapByPathIntersection :
    SamePrimeP7KPDatum

  incompatibilityNeighborhoodForP7Polymers :
    SamePrimeP7KPDatum

  localKPSumOverSamePrimeIncompatiblePolymers :
    SamePrimeP7KPDatum

canonicalSamePrimeP7KPData :
  List SamePrimeP7KPDatum
canonicalSamePrimeP7KPData =
  p7PrimeValue
  ∷ p7BTValencyEight
  ∷ p7BranchingFactorSeven
  ∷ samePrimeOverlapByPathIntersection
  ∷ incompatibilityNeighborhoodForP7Polymers
  ∷ localKPSumOverSamePrimeIncompatiblePolymers
  ∷ []

data ActualPolymerActivityOpenObligation : Set where
  defineWilsonActivityForEveryRetainedP7Polymer :
    ActualPolymerActivityOpenObligation

  proveActivityDependsOnWilsonDataNotToyRho :
    ActualPolymerActivityOpenObligation

  proveSamePrimeP7LocalKPSumBelowOne :
    ActualPolymerActivityOpenObligation

  proveUniformVolumeAndDepthStability :
    ActualPolymerActivityOpenObligation

  supplyBalabanRGTransferForActualWilsonActivity :
    ActualPolymerActivityOpenObligation

  connectCarrierActivityToContinuumOnlyAfterGate3 :
    ActualPolymerActivityOpenObligation

canonicalActualPolymerActivityOpenObligations :
  List ActualPolymerActivityOpenObligation
canonicalActualPolymerActivityOpenObligations =
  defineWilsonActivityForEveryRetainedP7Polymer
  ∷ proveActivityDependsOnWilsonDataNotToyRho
  ∷ proveSamePrimeP7LocalKPSumBelowOne
  ∷ proveUniformVolumeAndDepthStability
  ∷ supplyBalabanRGTransferForActualWilsonActivity
  ∷ connectCarrierActivityToContinuumOnlyAfterGate3
  ∷ []

data ActualPolymerActivityNonClaim : Set where
  noToyRhoPromotion :
    ActualPolymerActivityNonClaim

  noAnalyticKPProof :
    ActualPolymerActivityNonClaim

  noBalabanRGProof :
    ActualPolymerActivityNonClaim

  noContinuumYangMillsConstruction :
    ActualPolymerActivityNonClaim

  noYangMillsMassGapClaim :
    ActualPolymerActivityNonClaim

  noClayPromotion :
    ActualPolymerActivityNonClaim

canonicalActualPolymerActivityNonClaims :
  List ActualPolymerActivityNonClaim
canonicalActualPolymerActivityNonClaims =
  noToyRhoPromotion
  ∷ noAnalyticKPProof
  ∷ noBalabanRGProof
  ∷ noContinuumYangMillsConstruction
  ∷ noYangMillsMassGapClaim
  ∷ noClayPromotion
  ∷ []

data ActualPolymerActivityPromotion : Set where

actualPolymerActivityPromotionImpossibleHere :
  ActualPolymerActivityPromotion →
  ⊥
actualPolymerActivityPromotionImpossibleHere ()

p7Prime :
  Nat
p7Prime =
  7

p7BTValency :
  Nat
p7BTValency =
  8

p7BranchingFactor :
  Nat
p7BranchingFactor =
  7

p7StrictKPMarginBetaNumerator :
  Nat
p7StrictKPMarginBetaNumerator =
  1364

p7StrictKPMarginBetaDenominator :
  Nat
p7StrictKPMarginBetaDenominator =
  100

toyVsActualStatement :
  String
toyVsActualStatement =
  "Toy rho(k) is diagnostic only; actual KP promotion requires carrier Wilson activity for each retained same-prime p=7 polymer."

wilsonActivityInterfaceStatement :
  String
wilsonActivityInterfaceStatement =
  "Actual activity(P) is a carrier Wilson-action weight using polymer support, plaquette Wilson-loop phase, boundary trace, norm/absolute weight, and beta*cMin-a weighting."

p7SamePrimeDataStatement :
  String
p7SamePrimeDataStatement =
  "Same-prime p=7 data required: p=7, BT valency 8, branching factor 7, path/subtree support, path-intersection overlap, incompatibility neighborhood, and local KP sum."

promotionBoundaryStatement :
  String
promotionBoundaryStatement =
  "This receipt defines the actual-vs-toy boundary and required Wilson activity data only; analytic KP, Balaban/RG transfer, continuum Yang-Mills, mass gap, and Clay promotion remain unproved."

record CarrierWilsonActivityInterface : Set where
  field
    activityKind :
      PolymerActivityKind

    activityKindIsActual :
      activityKind ≡ actualCarrierWilsonActivity

    prime :
      Nat

    primeIsSeven :
      prime ≡ p7Prime

    btValency :
      Nat

    btValencyIsEight :
      btValency ≡ p7BTValency

    branchingFactor :
      Nat

    branchingFactorIsSeven :
      branchingFactor ≡ p7BranchingFactor

    polymerSupportData :
      List P7PolymerSupportDatum

    polymerSupportDataAreCanonical :
      polymerSupportData ≡ canonicalP7PolymerSupportData

    wilsonActivityData :
      List CarrierWilsonActivityDatum

    wilsonActivityDataAreCanonical :
      wilsonActivityData ≡ canonicalCarrierWilsonActivityData

    samePrimeKPData :
      List SamePrimeP7KPDatum

    samePrimeKPDataAreCanonical :
      samePrimeKPData ≡ canonicalSamePrimeP7KPData

    toyRhoUsedAsActivity :
      Bool

    toyRhoUsedAsActivityIsFalse :
      toyRhoUsedAsActivity ≡ false

    wilsonWeightUsedAsActivity :
      Bool

    wilsonWeightUsedAsActivityIsTrue :
      wilsonWeightUsedAsActivity ≡ true

    localKPSumTargetRecorded :
      Bool

    localKPSumTargetRecordedIsTrue :
      localKPSumTargetRecorded ≡ true

    localKPSumBelowOneProved :
      Bool

    localKPSumBelowOneProvedIsFalse :
      localKPSumBelowOneProved ≡ false

    strictP7MarginBetaNumerator :
      Nat

    strictP7MarginBetaNumeratorIsCanonical :
      strictP7MarginBetaNumerator
      ≡
      p7StrictKPMarginBetaNumerator

    strictP7MarginBetaDenominator :
      Nat

    strictP7MarginBetaDenominatorIsCanonical :
      strictP7MarginBetaDenominator
      ≡
      p7StrictKPMarginBetaDenominator

open CarrierWilsonActivityInterface public

canonicalCarrierWilsonActivityInterface :
  CarrierWilsonActivityInterface
canonicalCarrierWilsonActivityInterface =
  record
    { activityKind =
        actualCarrierWilsonActivity
    ; activityKindIsActual =
        refl
    ; prime =
        p7Prime
    ; primeIsSeven =
        refl
    ; btValency =
        p7BTValency
    ; btValencyIsEight =
        refl
    ; branchingFactor =
        p7BranchingFactor
    ; branchingFactorIsSeven =
        refl
    ; polymerSupportData =
        canonicalP7PolymerSupportData
    ; polymerSupportDataAreCanonical =
        refl
    ; wilsonActivityData =
        canonicalCarrierWilsonActivityData
    ; wilsonActivityDataAreCanonical =
        refl
    ; samePrimeKPData =
        canonicalSamePrimeP7KPData
    ; samePrimeKPDataAreCanonical =
        refl
    ; toyRhoUsedAsActivity =
        false
    ; toyRhoUsedAsActivityIsFalse =
        refl
    ; wilsonWeightUsedAsActivity =
        true
    ; wilsonWeightUsedAsActivityIsTrue =
        refl
    ; localKPSumTargetRecorded =
        true
    ; localKPSumTargetRecordedIsTrue =
        refl
    ; localKPSumBelowOneProved =
        false
    ; localKPSumBelowOneProvedIsFalse =
        refl
    ; strictP7MarginBetaNumerator =
        p7StrictKPMarginBetaNumerator
    ; strictP7MarginBetaNumeratorIsCanonical =
        refl
    ; strictP7MarginBetaDenominator =
        p7StrictKPMarginBetaDenominator
    ; strictP7MarginBetaDenominatorIsCanonical =
        refl
    }

record ActualPolymerActivityDefinitionReceipt : Setω where
  field
    status :
      ActualPolymerActivityStatus

    statusIsFrontierRecorded :
      status ≡ actualCarrierWilsonActivityFrontierRecorded

    toyRhoMarginReceipt :
      ToyRho.YMKPActivityRatioMarginReceipt

    toyRhoReceiptMarksToyDiagnostic :
      ToyRho.rhoProfileToyDiagnostic toyRhoMarginReceipt ≡ true

    toyRhoReceiptKeepsActualMarginOpen :
      ToyRho.actualRhoBelowOneMarginOpen toyRhoMarginReceipt ≡ true

    toyRhoReceiptDoesNotPromoteToyRho :
      ToyRho.toyRhoProfilePromotedAsProof toyRhoMarginReceipt ≡ false

    toyRhoReceiptClayFalse :
      ToyRho.clayYangMillsPromoted toyRhoMarginReceipt ≡ false

    actualActivityInterface :
      CarrierWilsonActivityInterface

    actualActivityInterfaceIsCanonical :
      actualActivityInterface ≡ canonicalCarrierWilsonActivityInterface

    activityKind :
      PolymerActivityKind

    activityKindIsActual :
      activityKind ≡ actualCarrierWilsonActivity

    toyKind :
      PolymerActivityKind

    toyKindIsDiagnostic :
      toyKind ≡ toyDepthRhoDiagnostic

    toyAndActualSeparated :
      Bool

    toyAndActualSeparatedIsTrue :
      toyAndActualSeparated ≡ true

    toyRhoGuarded :
      Bool

    toyRhoGuardedIsTrue :
      toyRhoGuarded ≡ true

    actualWilsonActivityRequiredForPromotion :
      Bool

    actualWilsonActivityRequiredForPromotionIsTrue :
      actualWilsonActivityRequiredForPromotion ≡ true

    p7SamePrimePolymerDataRecorded :
      Bool

    p7SamePrimePolymerDataRecordedIsTrue :
      p7SamePrimePolymerDataRecorded ≡ true

    supportData :
      List P7PolymerSupportDatum

    supportDataAreCanonical :
      supportData ≡ canonicalP7PolymerSupportData

    wilsonActivityData :
      List CarrierWilsonActivityDatum

    wilsonActivityDataAreCanonical :
      wilsonActivityData ≡ canonicalCarrierWilsonActivityData

    samePrimeKPData :
      List SamePrimeP7KPDatum

    samePrimeKPDataAreCanonical :
      samePrimeKPData ≡ canonicalSamePrimeP7KPData

    actualLocalKPSumBoundProved :
      Bool

    actualLocalKPSumBoundProvedIsFalse :
      actualLocalKPSumBoundProved ≡ false

    analyticKPProved :
      Bool

    analyticKPProvedIsFalse :
      analyticKPProved ≡ false

    balabanRGTransferProved :
      Bool

    balabanRGTransferProvedIsFalse :
      balabanRGTransferProved ≡ false

    continuumYangMillsPromoted :
      Bool

    continuumYangMillsPromotedIsFalse :
      continuumYangMillsPromoted ≡ false

    massGapPromoted :
      Bool

    massGapPromotedIsFalse :
      massGapPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    openObligations :
      List ActualPolymerActivityOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalActualPolymerActivityOpenObligations

    nonClaims :
      List ActualPolymerActivityNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalActualPolymerActivityNonClaims

    promotionFlags :
      List ActualPolymerActivityPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    noPromotion :
      ActualPolymerActivityPromotion →
      ⊥

    toyVsActualReading :
      String

    toyVsActualReadingIsCanonical :
      toyVsActualReading ≡ toyVsActualStatement

    wilsonActivityInterfaceReading :
      String

    wilsonActivityInterfaceReadingIsCanonical :
      wilsonActivityInterfaceReading ≡ wilsonActivityInterfaceStatement

    p7SamePrimeDataReading :
      String

    p7SamePrimeDataReadingIsCanonical :
      p7SamePrimeDataReading ≡ p7SamePrimeDataStatement

    promotionBoundaryReading :
      String

    promotionBoundaryReadingIsCanonical :
      promotionBoundaryReading ≡ promotionBoundaryStatement

    receiptBoundary :
      List String

open ActualPolymerActivityDefinitionReceipt public

canonicalActualPolymerActivityDefinitionReceipt :
  ActualPolymerActivityDefinitionReceipt
canonicalActualPolymerActivityDefinitionReceipt =
  record
    { status =
        actualCarrierWilsonActivityFrontierRecorded
    ; statusIsFrontierRecorded =
        refl
    ; toyRhoMarginReceipt =
        ToyRho.canonicalYMKPActivityRatioMarginReceipt
    ; toyRhoReceiptMarksToyDiagnostic =
        refl
    ; toyRhoReceiptKeepsActualMarginOpen =
        refl
    ; toyRhoReceiptDoesNotPromoteToyRho =
        refl
    ; toyRhoReceiptClayFalse =
        refl
    ; actualActivityInterface =
        canonicalCarrierWilsonActivityInterface
    ; actualActivityInterfaceIsCanonical =
        refl
    ; activityKind =
        actualCarrierWilsonActivity
    ; activityKindIsActual =
        refl
    ; toyKind =
        toyDepthRhoDiagnostic
    ; toyKindIsDiagnostic =
        refl
    ; toyAndActualSeparated =
        true
    ; toyAndActualSeparatedIsTrue =
        refl
    ; toyRhoGuarded =
        true
    ; toyRhoGuardedIsTrue =
        refl
    ; actualWilsonActivityRequiredForPromotion =
        true
    ; actualWilsonActivityRequiredForPromotionIsTrue =
        refl
    ; p7SamePrimePolymerDataRecorded =
        true
    ; p7SamePrimePolymerDataRecordedIsTrue =
        refl
    ; supportData =
        canonicalP7PolymerSupportData
    ; supportDataAreCanonical =
        refl
    ; wilsonActivityData =
        canonicalCarrierWilsonActivityData
    ; wilsonActivityDataAreCanonical =
        refl
    ; samePrimeKPData =
        canonicalSamePrimeP7KPData
    ; samePrimeKPDataAreCanonical =
        refl
    ; actualLocalKPSumBoundProved =
        false
    ; actualLocalKPSumBoundProvedIsFalse =
        refl
    ; analyticKPProved =
        false
    ; analyticKPProvedIsFalse =
        refl
    ; balabanRGTransferProved =
        false
    ; balabanRGTransferProvedIsFalse =
        refl
    ; continuumYangMillsPromoted =
        false
    ; continuumYangMillsPromotedIsFalse =
        refl
    ; massGapPromoted =
        false
    ; massGapPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; openObligations =
        canonicalActualPolymerActivityOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; nonClaims =
        canonicalActualPolymerActivityNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; noPromotion =
        actualPolymerActivityPromotionImpossibleHere
    ; toyVsActualReading =
        toyVsActualStatement
    ; toyVsActualReadingIsCanonical =
        refl
    ; wilsonActivityInterfaceReading =
        wilsonActivityInterfaceStatement
    ; wilsonActivityInterfaceReadingIsCanonical =
        refl
    ; p7SamePrimeDataReading =
        p7SamePrimeDataStatement
    ; p7SamePrimeDataReadingIsCanonical =
        refl
    ; promotionBoundaryReading =
        promotionBoundaryStatement
    ; promotionBoundaryReadingIsCanonical =
        refl
    ; receiptBoundary =
        "Guards toy rho(k) as diagnostic-only carrier bookkeeping"
        ∷ "Defines the actual carrier Wilson activity interface required before KP promotion"
        ∷ "Records same-prime p=7 polymer data: p=7, valency 8, branching factor 7, path/subtree support, overlap, incompatibility neighborhood, and local KP sum"
        ∷ "Requires Wilson-loop phase, Wilson-action weight, boundary trace, activity norm/absolute weight, and beta*cMin-a weighting"
        ∷ "Leaves actual local KP sum below one, uniform volume/depth stability, and Balaban/RG transfer open"
        ∷ "No analytic KP theorem, continuum Yang-Mills construction, mass gap, or Clay promotion follows"
        ∷ []
    }

canonicalActualPolymerActivityGuardsToyRho :
  toyRhoGuarded canonicalActualPolymerActivityDefinitionReceipt ≡ true
canonicalActualPolymerActivityGuardsToyRho =
  refl

canonicalActualPolymerActivityNoAnalyticKP :
  analyticKPProved canonicalActualPolymerActivityDefinitionReceipt ≡ false
canonicalActualPolymerActivityNoAnalyticKP =
  refl

canonicalActualPolymerActivityNoClay :
  clayYangMillsPromoted canonicalActualPolymerActivityDefinitionReceipt
  ≡
  false
canonicalActualPolymerActivityNoClay =
  refl
