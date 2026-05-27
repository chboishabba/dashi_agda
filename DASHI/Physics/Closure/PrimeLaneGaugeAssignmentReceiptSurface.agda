module DASHI.Physics.Closure.PrimeLaneGaugeAssignmentReceiptSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AdapterIrreducibilityNoGoIndex as AdapterNoGo
import DASHI.Physics.Closure.FractranPrimeLaneValuationReceiptSurface as FractranLane
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Moonshine
import DASHI.Physics.QFT.DHRGaugeReceiptSurface as DHR

------------------------------------------------------------------------
-- Prime-lane gauge assignment target surface.
--
-- This module records a bounded target-only receipt for a 15-lane gauge
-- assignment program.  It does not compute DHR sectors, prove a Chen
-- pairing/cluster theorem, identify the Standard Model gauge group, prove a
-- residual H group is trivial or nontrivial, or promote a GRQFT / TOE receipt.

data PrimeLaneGaugeAssignmentStatus : Set where
  targetSurfaceOnlyNoGaugePromotion :
    PrimeLaneGaugeAssignmentStatus

data PrimeLaneGaugeAssignmentPromotionAuthorityToken : Set where

data PrimeLane15 : Set where
  lane01 :
    PrimeLane15

  lane02 :
    PrimeLane15

  lane03 :
    PrimeLane15

  lane04 :
    PrimeLane15

  lane05 :
    PrimeLane15

  lane06 :
    PrimeLane15

  lane07 :
    PrimeLane15

  lane08 :
    PrimeLane15

  lane09 :
    PrimeLane15

  lane10 :
    PrimeLane15

  lane11 :
    PrimeLane15

  lane12 :
    PrimeLane15

  lane13 :
    PrimeLane15

  lane14 :
    PrimeLane15

  lane15 :
    PrimeLane15

canonicalPrimeLanes15 :
  List PrimeLane15
canonicalPrimeLanes15 =
  lane01
  ∷ lane02
  ∷ lane03
  ∷ lane04
  ∷ lane05
  ∷ lane06
  ∷ lane07
  ∷ lane08
  ∷ lane09
  ∷ lane10
  ∷ lane11
  ∷ lane12
  ∷ lane13
  ∷ lane14
  ∷ lane15
  ∷ []

primeLane15ToMonsterPrime :
  PrimeLane15 →
  Moonshine.MonsterPrimeLane
primeLane15ToMonsterPrime lane01 =
  Moonshine.p2
primeLane15ToMonsterPrime lane02 =
  Moonshine.p3
primeLane15ToMonsterPrime lane03 =
  Moonshine.p5
primeLane15ToMonsterPrime lane04 =
  Moonshine.p7
primeLane15ToMonsterPrime lane05 =
  Moonshine.p11
primeLane15ToMonsterPrime lane06 =
  Moonshine.p13
primeLane15ToMonsterPrime lane07 =
  Moonshine.p17
primeLane15ToMonsterPrime lane08 =
  Moonshine.p19
primeLane15ToMonsterPrime lane09 =
  Moonshine.p23
primeLane15ToMonsterPrime lane10 =
  Moonshine.p29
primeLane15ToMonsterPrime lane11 =
  Moonshine.p31
primeLane15ToMonsterPrime lane12 =
  Moonshine.p41
primeLane15ToMonsterPrime lane13 =
  Moonshine.p47
primeLane15ToMonsterPrime lane14 =
  Moonshine.p59
primeLane15ToMonsterPrime lane15 =
  Moonshine.p71

data PrimeLaneProductTarget : Set where
  fifteenLaneProductCarrier :
    PrimeLaneProductTarget

  laneWiseGaugeFactorAssignment :
    PrimeLaneProductTarget

  productCompatibilityAcrossLanes :
    PrimeLaneProductTarget

canonicalPrimeLaneProductTargets :
  List PrimeLaneProductTarget
canonicalPrimeLaneProductTargets =
  fifteenLaneProductCarrier
  ∷ laneWiseGaugeFactorAssignment
  ∷ productCompatibilityAcrossLanes
  ∷ []

data ChenPairingClusterTarget : Set where
  chenIteratedIntegralPairing :
    ChenPairingClusterTarget

  clusterCharacterExtraction :
    ChenPairingClusterTarget

  laneClusterGaugeFactorTarget :
    ChenPairingClusterTarget

canonicalChenPairingClusterTargets :
  List ChenPairingClusterTarget
canonicalChenPairingClusterTargets =
  chenIteratedIntegralPairing
  ∷ clusterCharacterExtraction
  ∷ laneClusterGaugeFactorTarget
  ∷ []

data DHRGaugeComputationBoundary : Set where
  laneDimensionDLMEquivConsumedNoGaugePromotion :
    DHRGaugeComputationBoundary

canonicalDHRGaugeComputationBoundaries :
  List DHRGaugeComputationBoundary
canonicalDHRGaugeComputationBoundaries =
  laneDimensionDLMEquivConsumedNoGaugePromotion
  ∷ []

data PrimeLaneDeepComputationBlocker : Set where
  laneDimensionDeepComputationBlocker :
    PrimeLaneDeepComputationBlocker

data LaneDimensionConjectureStatus : Set where
  laneDimensionHistoricalConjectureStatus :
    LaneDimensionConjectureStatus

  laneDimensionInternallyPromotedNoGaugePromotion :
    LaneDimensionConjectureStatus

  laneDimensionComputedInternallyByDLMDASHIPrimeLaneEquiv :
    LaneDimensionConjectureStatus

data PrimeLaneDHREndomorphismTarget
  (p : Moonshine.MonsterPrimeLane)
  (ρ : DHR.LocalisedEndomorphism) :
  Set where

primeLaneDHREndos :
  Moonshine.MonsterPrimeLane →
  DHR.LocalisedEndomorphism →
  Set
primeLaneDHREndos =
  PrimeLaneDHREndomorphismTarget

laneDimension :
  Moonshine.MonsterPrimeLane →
  Nat →
  Set
laneDimension p n =
  Moonshine.monsterPrimeLaneConjecturalDHRDimension p ≡ n

data PrimeLaneGaugeAssignmentMissingField : Set where
  missingPrimeLaneDHREndomorphismTargetField :
    PrimeLaneGaugeAssignmentMissingField

record PrimeLaneDHREndomorphismTargetFailClosedReceipt : Setω where
  field
    missingField :
      PrimeLaneGaugeAssignmentMissingField

    missingFieldIsCanonical :
      missingField ≡ missingPrimeLaneDHREndomorphismTargetField

    targetPredicate :
      Moonshine.MonsterPrimeLane →
      DHR.LocalisedEndomorphism →
      Set

    targetPredicateRecorded :
      Bool

    targetPredicateRecordedIsTrue :
      targetPredicateRecorded ≡ true

    constructsPrimeLaneDHREndomorphism :
      Bool

    constructsPrimeLaneDHREndomorphismIsFalse :
      constructsPrimeLaneDHREndomorphism ≡ false

    boundary :
      List String

open PrimeLaneDHREndomorphismTargetFailClosedReceipt public

canonicalPrimeLaneDHREndomorphismTargetFailClosedReceipt :
  PrimeLaneDHREndomorphismTargetFailClosedReceipt
canonicalPrimeLaneDHREndomorphismTargetFailClosedReceipt =
  record
    { missingField =
        missingPrimeLaneDHREndomorphismTargetField
    ; missingFieldIsCanonical =
        refl
    ; targetPredicate =
        primeLaneDHREndos
    ; targetPredicateRecorded =
        true
    ; targetPredicateRecordedIsTrue =
        refl
    ; constructsPrimeLaneDHREndomorphism =
        false
    ; constructsPrimeLaneDHREndomorphismIsFalse =
        refl
    ; boundary =
        "PrimeLaneLaneDimensionBlockerReceipt.primeLaneDHREndomorphismTarget is a closed target predicate, not a constructed DHR endomorphism"
        ∷ "The exact missing field is primeLaneDHREndos : MonsterPrimeLane -> DHR.LocalisedEndomorphism -> Set with constructors or an authority-backed lane localisation theorem"
        ∷ "laneDimension is concrete only as equality to the finite conjectural DHR dimension table"
        ∷ "No prime-lane DHR endomorphism, DHR gauge group, or Standard Model gauge match is promoted here"
        ∷ []
    }

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst :
      A

    snd :
      B

data E8MckayCorrespondence : Set where
  e8MckayCorrespondenceAuthorityTarget :
    E8MckayCorrespondence

data SMinE8Embedding : Set where
  standardModelInE8EmbeddingAuthorityTarget :
    SMinE8Embedding

data E8SMEmbeddingBranchingStep : Set where
  e8ToE6TimesSU3 :
    E8SMEmbeddingBranchingStep

  e6SU3ToSO10U1SU3 :
    E8SMEmbeddingBranchingStep

  so10U1SU3ToSU5U1SquaredSU3 :
    E8SMEmbeddingBranchingStep

  su5U1SquaredSU3ToGSMTimesHiddenSU3 :
    E8SMEmbeddingBranchingStep

canonicalE8SMEmbeddingBranching :
  List E8SMEmbeddingBranchingStep
canonicalE8SMEmbeddingBranching =
  e8ToE6TimesSU3
  ∷ e6SU3ToSO10U1SU3
  ∷ so10U1SU3ToSU5U1SquaredSU3
  ∷ su5U1SquaredSU3ToGSMTimesHiddenSU3
  ∷ []

data HeteroticNarainE8RoutePoint : Set where
  heteroticE8TimesE8Compactification :
    HeteroticNarainE8RoutePoint

  narainLatticeCompactification :
    HeteroticNarainE8RoutePoint

  wilsonLineGaugeBreaking :
    HeteroticNarainE8RoutePoint

  standardModelGaugeFactorBranching :
    HeteroticNarainE8RoutePoint

  patiSalamSU2RHighEnergyExtension :
    HeteroticNarainE8RoutePoint

canonicalHeteroticNarainE8Route :
  List HeteroticNarainE8RoutePoint
canonicalHeteroticNarainE8Route =
  heteroticE8TimesE8Compactification
  ∷ narainLatticeCompactification
  ∷ wilsonLineGaugeBreaking
  ∷ standardModelGaugeFactorBranching
  ∷ patiSalamSU2RHighEnergyExtension
  ∷ []

data E8Adjoint248BranchingSummand : Set where
  gluonAdjointSummand-8-1-0 :
    E8Adjoint248BranchingSummand

  weakAdjointSummand-1-3-0 :
    E8Adjoint248BranchingSummand

  hyperchargeSummand-1-1-0 :
    E8Adjoint248BranchingSummand

  matterRepresentationSummands :
    E8Adjoint248BranchingSummand

canonicalE8Adjoint248GaugeBosonSummary :
  List E8Adjoint248BranchingSummand
canonicalE8Adjoint248GaugeBosonSummary =
  gluonAdjointSummand-8-1-0
  ∷ weakAdjointSummand-1-3-0
  ∷ hyperchargeSummand-1-1-0
  ∷ matterRepresentationSummands
  ∷ []

data E8McKayRootType : Set where
  rootTypeA1Short :
    E8McKayRootType

  rootTypeA2Short :
    E8McKayRootType

  rootTypeA4TruncatedToA2 :
    E8McKayRootType

  rootTypeA6TruncatedToA1 :
    E8McKayRootType

  rootTypeLongMatterSector :
    E8McKayRootType

data E8McKayLaneGaugeFactor : Set where
  e8LaneU1Y :
    E8McKayLaneGaugeFactor

  e8LaneSU2L :
    E8McKayLaneGaugeFactor

  e8LaneSU3c :
    E8McKayLaneGaugeFactor

  e8LaneSU2RBrokenAtSeesaw :
    E8McKayLaneGaugeFactor

  e8LaneMatterOrTrivialGauge :
    E8McKayLaneGaugeFactor

e8MckayPrimeLaneRootType :
  Moonshine.MonsterPrimeLane →
  E8McKayRootType
e8MckayPrimeLaneRootType Moonshine.p2 =
  rootTypeA1Short
e8MckayPrimeLaneRootType Moonshine.p3 =
  rootTypeA2Short
e8MckayPrimeLaneRootType Moonshine.p5 =
  rootTypeA4TruncatedToA2
e8MckayPrimeLaneRootType Moonshine.p7 =
  rootTypeA6TruncatedToA1
e8MckayPrimeLaneRootType Moonshine.p11 =
  rootTypeLongMatterSector
e8MckayPrimeLaneRootType Moonshine.p13 =
  rootTypeLongMatterSector
e8MckayPrimeLaneRootType Moonshine.p17 =
  rootTypeLongMatterSector
e8MckayPrimeLaneRootType Moonshine.p19 =
  rootTypeLongMatterSector
e8MckayPrimeLaneRootType Moonshine.p23 =
  rootTypeLongMatterSector
e8MckayPrimeLaneRootType Moonshine.p29 =
  rootTypeLongMatterSector
e8MckayPrimeLaneRootType Moonshine.p31 =
  rootTypeLongMatterSector
e8MckayPrimeLaneRootType Moonshine.p41 =
  rootTypeLongMatterSector
e8MckayPrimeLaneRootType Moonshine.p47 =
  rootTypeLongMatterSector
e8MckayPrimeLaneRootType Moonshine.p59 =
  rootTypeLongMatterSector
e8MckayPrimeLaneRootType Moonshine.p71 =
  rootTypeLongMatterSector

e8MckayPrimeLaneGaugeFactor :
  Moonshine.MonsterPrimeLane →
  E8McKayLaneGaugeFactor
e8MckayPrimeLaneGaugeFactor Moonshine.p2 =
  e8LaneU1Y
e8MckayPrimeLaneGaugeFactor Moonshine.p3 =
  e8LaneSU2L
e8MckayPrimeLaneGaugeFactor Moonshine.p5 =
  e8LaneSU3c
e8MckayPrimeLaneGaugeFactor Moonshine.p7 =
  e8LaneSU2RBrokenAtSeesaw
e8MckayPrimeLaneGaugeFactor Moonshine.p11 =
  e8LaneMatterOrTrivialGauge
e8MckayPrimeLaneGaugeFactor Moonshine.p13 =
  e8LaneMatterOrTrivialGauge
e8MckayPrimeLaneGaugeFactor Moonshine.p17 =
  e8LaneMatterOrTrivialGauge
e8MckayPrimeLaneGaugeFactor Moonshine.p19 =
  e8LaneMatterOrTrivialGauge
e8MckayPrimeLaneGaugeFactor Moonshine.p23 =
  e8LaneMatterOrTrivialGauge
e8MckayPrimeLaneGaugeFactor Moonshine.p29 =
  e8LaneMatterOrTrivialGauge
e8MckayPrimeLaneGaugeFactor Moonshine.p31 =
  e8LaneMatterOrTrivialGauge
e8MckayPrimeLaneGaugeFactor Moonshine.p41 =
  e8LaneMatterOrTrivialGauge
e8MckayPrimeLaneGaugeFactor Moonshine.p47 =
  e8LaneMatterOrTrivialGauge
e8MckayPrimeLaneGaugeFactor Moonshine.p59 =
  e8LaneMatterOrTrivialGauge
e8MckayPrimeLaneGaugeFactor Moonshine.p71 =
  e8LaneMatterOrTrivialGauge

e8MckayHighEnergyLaneDimension :
  Moonshine.MonsterPrimeLane →
  Nat
e8MckayHighEnergyLaneDimension Moonshine.p2 =
  1
e8MckayHighEnergyLaneDimension Moonshine.p3 =
  2
e8MckayHighEnergyLaneDimension Moonshine.p5 =
  3
e8MckayHighEnergyLaneDimension Moonshine.p7 =
  2
e8MckayHighEnergyLaneDimension Moonshine.p11 =
  0
e8MckayHighEnergyLaneDimension Moonshine.p13 =
  0
e8MckayHighEnergyLaneDimension Moonshine.p17 =
  0
e8MckayHighEnergyLaneDimension Moonshine.p19 =
  0
e8MckayHighEnergyLaneDimension Moonshine.p23 =
  0
e8MckayHighEnergyLaneDimension Moonshine.p29 =
  0
e8MckayHighEnergyLaneDimension Moonshine.p31 =
  0
e8MckayHighEnergyLaneDimension Moonshine.p41 =
  0
e8MckayHighEnergyLaneDimension Moonshine.p47 =
  0
e8MckayHighEnergyLaneDimension Moonshine.p59 =
  0
e8MckayHighEnergyLaneDimension Moonshine.p71 =
  0

e8MckayAtLeast11HighEnergyDimensionIs0 :
  (p : Moonshine.MonsterPrimeLane) →
  FractranLane.MonsterPrimeLaneAtLeast11 p →
  e8MckayHighEnergyLaneDimension p ≡ 0
e8MckayAtLeast11HighEnergyDimensionIs0
  Moonshine.p11
  FractranLane.p11AtLeast11 =
  refl
e8MckayAtLeast11HighEnergyDimensionIs0
  Moonshine.p13
  FractranLane.p13AtLeast11 =
  refl
e8MckayAtLeast11HighEnergyDimensionIs0
  Moonshine.p17
  FractranLane.p17AtLeast11 =
  refl
e8MckayAtLeast11HighEnergyDimensionIs0
  Moonshine.p19
  FractranLane.p19AtLeast11 =
  refl
e8MckayAtLeast11HighEnergyDimensionIs0
  Moonshine.p23
  FractranLane.p23AtLeast11 =
  refl
e8MckayAtLeast11HighEnergyDimensionIs0
  Moonshine.p29
  FractranLane.p29AtLeast11 =
  refl
e8MckayAtLeast11HighEnergyDimensionIs0
  Moonshine.p31
  FractranLane.p31AtLeast11 =
  refl
e8MckayAtLeast11HighEnergyDimensionIs0
  Moonshine.p41
  FractranLane.p41AtLeast11 =
  refl
e8MckayAtLeast11HighEnergyDimensionIs0
  Moonshine.p47
  FractranLane.p47AtLeast11 =
  refl
e8MckayAtLeast11HighEnergyDimensionIs0
  Moonshine.p59
  FractranLane.p59AtLeast11 =
  refl
e8MckayAtLeast11HighEnergyDimensionIs0
  Moonshine.p71
  FractranLane.p71AtLeast11 =
  refl

record E8SMEmbeddingBranchingReceipt : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    branchingChain :
      List E8SMEmbeddingBranchingStep

    branchingChainIsCanonical :
      branchingChain ≡ canonicalE8SMEmbeddingBranching

    adjoint248Summary :
      List E8Adjoint248BranchingSummand

    adjoint248SummaryIsCanonical :
      adjoint248Summary ≡ canonicalE8Adjoint248GaugeBosonSummary

    heteroticNarainRoute :
      List HeteroticNarainE8RoutePoint

    heteroticNarainRouteIsCanonical :
      heteroticNarainRoute ≡ canonicalHeteroticNarainE8Route

    gaugeBosonCount :
      Nat

    gaugeBosonCountIs12 :
      gaugeBosonCount ≡ 12

    includesGluonAdjoint :
      Bool

    includesGluonAdjointIsTrue :
      includesGluonAdjoint ≡ true

    includesWeakAdjoint :
      Bool

    includesWeakAdjointIsTrue :
      includesWeakAdjoint ≡ true

    includesHyperchargeBoson :
      Bool

    includesHyperchargeBosonIsTrue :
      includesHyperchargeBoson ≡ true

    includesMatterRepresentations :
      Bool

    includesMatterRepresentationsIsTrue :
      includesMatterRepresentations ≡ true

    embeddingImportedAsTheoremHere :
      Bool

    embeddingImportedAsTheoremHereIsFalse :
      embeddingImportedAsTheoremHere ≡ false

    heteroticE8TimesE8WilsonLinesCanYieldSMGaugeFactors :
      Bool

    heteroticE8TimesE8WilsonLinesCanYieldSMGaugeFactorsIsTrue :
      heteroticE8TimesE8WilsonLinesCanYieldSMGaugeFactors ≡ true

    patiSalamSU2RCanBeHighEnergyP7Extension :
      Bool

    patiSalamSU2RCanBeHighEnergyP7ExtensionIsTrue :
      patiSalamSU2RCanBeHighEnergyP7Extension ≡ true

    boundary :
      List String

canonicalE8SMEmbeddingBranchingReceipt :
  E8SMEmbeddingBranchingReceipt
canonicalE8SMEmbeddingBranchingReceipt =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; branchingChain =
        canonicalE8SMEmbeddingBranching
    ; branchingChainIsCanonical =
        refl
    ; adjoint248Summary =
        canonicalE8Adjoint248GaugeBosonSummary
    ; adjoint248SummaryIsCanonical =
        refl
    ; heteroticNarainRoute =
        canonicalHeteroticNarainE8Route
    ; heteroticNarainRouteIsCanonical =
        refl
    ; gaugeBosonCount =
        12
    ; gaugeBosonCountIs12 =
        refl
    ; includesGluonAdjoint =
        true
    ; includesGluonAdjointIsTrue =
        refl
    ; includesWeakAdjoint =
        true
    ; includesWeakAdjointIsTrue =
        refl
    ; includesHyperchargeBoson =
        true
    ; includesHyperchargeBosonIsTrue =
        refl
    ; includesMatterRepresentations =
        true
    ; includesMatterRepresentationsIsTrue =
        refl
    ; embeddingImportedAsTheoremHere =
        false
    ; embeddingImportedAsTheoremHereIsFalse =
        refl
    ; heteroticE8TimesE8WilsonLinesCanYieldSMGaugeFactors =
        true
    ; heteroticE8TimesE8WilsonLinesCanYieldSMGaugeFactorsIsTrue =
        refl
    ; patiSalamSU2RCanBeHighEnergyP7Extension =
        true
    ; patiSalamSU2RCanBeHighEnergyP7ExtensionIsTrue =
        refl
    ; boundary =
        "records the provable route shape: heterotic E8xE8 / Narain compactification with Wilson lines can yield U1Y x SU2L x SU3c"
        ∷ "records the target branching E8 -> E6xSU3 -> SO10xU1xSU3 -> SU5xU1^2xSU3 -> G_SMxhidden-SU3"
        ∷ "records Pati-Salam SU2R as a possible high-energy extension lane for p7, not as a low-energy DHR laneDimension theorem"
        ∷ "records the 248 adjoint gauge-boson summary (8,1,0), (1,3,0), (1,1,0), plus matter representations"
        ∷ "the 12 gauge-boson count is a bookkeeping receipt; this module does not import or prove the external heterotic branching theorem"
        ∷ []
    }

record E8McKayPrimeLaneTableReceipt : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    rootType :
      Moonshine.MonsterPrimeLane →
      E8McKayRootType

    rootTypeIsCanonical :
      rootType ≡ e8MckayPrimeLaneRootType

    highEnergyGaugeFactor :
      Moonshine.MonsterPrimeLane →
      E8McKayLaneGaugeFactor

    highEnergyGaugeFactorIsCanonical :
      highEnergyGaugeFactor ≡ e8MckayPrimeLaneGaugeFactor

    highEnergyLaneDimension :
      Moonshine.MonsterPrimeLane →
      Nat

    highEnergyLaneDimensionIsCanonical :
      highEnergyLaneDimension ≡ e8MckayHighEnergyLaneDimension

    p2RootTypeA1 :
      rootType Moonshine.p2 ≡ rootTypeA1Short

    p2GaugeU1Dim1 :
      highEnergyGaugeFactor Moonshine.p2 ≡ e8LaneU1Y

    p2Dim1 :
      highEnergyLaneDimension Moonshine.p2 ≡ 1

    p3RootTypeA2 :
      rootType Moonshine.p3 ≡ rootTypeA2Short

    p3GaugeSU2LDim2 :
      highEnergyGaugeFactor Moonshine.p3 ≡ e8LaneSU2L

    p3Dim2 :
      highEnergyLaneDimension Moonshine.p3 ≡ 2

    p5RootTypeA4TruncatedToA2 :
      rootType Moonshine.p5 ≡ rootTypeA4TruncatedToA2

    p5GaugeSU3cDim3 :
      highEnergyGaugeFactor Moonshine.p5 ≡ e8LaneSU3c

    p5Dim3 :
      highEnergyLaneDimension Moonshine.p5 ≡ 3

    p7RootTypeA6TruncatedToA1 :
      rootType Moonshine.p7 ≡ rootTypeA6TruncatedToA1

    p7GaugeSU2RBrokenDim2 :
      highEnergyGaugeFactor Moonshine.p7
      ≡
      e8LaneSU2RBrokenAtSeesaw

    p7HighEnergyDim2 :
      highEnergyLaneDimension Moonshine.p7 ≡ 2

    pAtLeast11MatterOrTrivialGauge :
      (p : Moonshine.MonsterPrimeLane) →
      FractranLane.MonsterPrimeLaneAtLeast11 p →
      highEnergyGaugeFactor p ≡ e8LaneMatterOrTrivialGauge

    pAtLeast11HighEnergyDim0 :
      (p : Moonshine.MonsterPrimeLane) →
      FractranLane.MonsterPrimeLaneAtLeast11 p →
      highEnergyLaneDimension p ≡ 0

    lowEnergyDHRDimensionKeptSeparate :
      Bool

    lowEnergyDHRDimensionKeptSeparateIsTrue :
      lowEnergyDHRDimensionKeptSeparate ≡ true

    p7DHRDimensionIs2 :
      Moonshine.monsterPrimeLaneConjecturalDHRDimension Moonshine.p7
      ≡
      2

    tableIsConjectural :
      Bool

    tableIsConjecturalIsTrue :
      tableIsConjectural ≡ true

    primeToGaugeFactorAssignmentIsDASHIBridge :
      Bool

    primeToGaugeFactorAssignmentIsDASHIBridgeIsTrue :
      primeToGaugeFactorAssignmentIsDASHIBridge ≡ true

    primeToGaugeFactorAssignmentFirstPrinciplesTheorem :
      Bool

    primeToGaugeFactorAssignmentFirstPrinciplesTheoremIsFalse :
      primeToGaugeFactorAssignmentFirstPrinciplesTheorem ≡ false

    boundary :
      List String

canonicalE8McKayPrimeLaneTableReceipt :
  E8McKayPrimeLaneTableReceipt
canonicalE8McKayPrimeLaneTableReceipt =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; rootType =
        e8MckayPrimeLaneRootType
    ; rootTypeIsCanonical =
        refl
    ; highEnergyGaugeFactor =
        e8MckayPrimeLaneGaugeFactor
    ; highEnergyGaugeFactorIsCanonical =
        refl
    ; highEnergyLaneDimension =
        e8MckayHighEnergyLaneDimension
    ; highEnergyLaneDimensionIsCanonical =
        refl
    ; p2RootTypeA1 =
        refl
    ; p2GaugeU1Dim1 =
        refl
    ; p2Dim1 =
        refl
    ; p3RootTypeA2 =
        refl
    ; p3GaugeSU2LDim2 =
        refl
    ; p3Dim2 =
        refl
    ; p5RootTypeA4TruncatedToA2 =
        refl
    ; p5GaugeSU3cDim3 =
        refl
    ; p5Dim3 =
        refl
    ; p7RootTypeA6TruncatedToA1 =
        refl
    ; p7GaugeSU2RBrokenDim2 =
        refl
    ; p7HighEnergyDim2 =
        refl
    ; pAtLeast11MatterOrTrivialGauge =
        λ where
          Moonshine.p11 FractranLane.p11AtLeast11 → refl
          Moonshine.p13 FractranLane.p13AtLeast11 → refl
          Moonshine.p17 FractranLane.p17AtLeast11 → refl
          Moonshine.p19 FractranLane.p19AtLeast11 → refl
          Moonshine.p23 FractranLane.p23AtLeast11 → refl
          Moonshine.p29 FractranLane.p29AtLeast11 → refl
          Moonshine.p31 FractranLane.p31AtLeast11 → refl
          Moonshine.p41 FractranLane.p41AtLeast11 → refl
          Moonshine.p47 FractranLane.p47AtLeast11 → refl
          Moonshine.p59 FractranLane.p59AtLeast11 → refl
          Moonshine.p71 FractranLane.p71AtLeast11 → refl
    ; pAtLeast11HighEnergyDim0 =
        e8MckayAtLeast11HighEnergyDimensionIs0
    ; lowEnergyDHRDimensionKeptSeparate =
        true
    ; lowEnergyDHRDimensionKeptSeparateIsTrue =
        refl
    ; p7DHRDimensionIs2 =
        refl
    ; tableIsConjectural =
        true
    ; tableIsConjecturalIsTrue =
        refl
    ; primeToGaugeFactorAssignmentIsDASHIBridge =
        true
    ; primeToGaugeFactorAssignmentIsDASHIBridgeIsTrue =
        refl
    ; primeToGaugeFactorAssignmentFirstPrinciplesTheorem =
        false
    ; primeToGaugeFactorAssignmentFirstPrinciplesTheoremIsFalse =
        refl
    ; boundary =
        "DASHI-specific supersingular-prime bridge table: p2 U1Y dim1, p3 SU2L dim2, p5 SU3c dim3, p7 SU2R-broken dim2"
        ∷ "p>=11 lanes are matter/trivial-gauge lanes in the high-energy E8/McKay bridge"
        ∷ "the specific prime-to-gauge-factor assignment is new framing, not a first-principles theorem from heterotic string theory or moonshine"
        ∷ "DLM laneDimension data is authority-backed and conditional, kept separate from the high-energy gauge bridge; p7 records SU2R dimension 2, with p>=11 gauge-trivial"
        ∷ []
    }

record E8McKayLaneDimensionReceipt : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    e8MckayInput :
      E8MckayCorrespondence

    smEmbeddingInput :
      SMinE8Embedding

    branchingReceipt :
      E8SMEmbeddingBranchingReceipt

    primeLaneTable :
      E8McKayPrimeLaneTableReceipt

    laneDimensionTargetRelation :
      Moonshine.MonsterPrimeLane →
      Nat →
      Set

    highEnergyLaneDimensionTarget :
      Moonshine.MonsterPrimeLane →
      Nat

    highEnergyLaneDimensionTargetIsE8McKay :
      highEnergyLaneDimensionTarget
      ≡
      e8MckayHighEnergyLaneDimension

    dhrLowEnergyLaneDimensionTarget :
      Moonshine.MonsterPrimeLane →
      Nat

    dhrLowEnergyLaneDimensionTargetIsExistingConjecture :
      dhrLowEnergyLaneDimensionTarget
      ≡
      Moonshine.monsterPrimeLaneConjecturalDHRDimension

    p7HighEnergyBridgeDim2 :
      highEnergyLaneDimensionTarget Moonshine.p7 ≡ 2

    p7LowEnergyDHRDim2 :
      dhrLowEnergyLaneDimensionTarget Moonshine.p7 ≡ 2

    bridgeIsConjectural :
      Bool

    bridgeIsConjecturalIsTrue :
      bridgeIsConjectural ≡ true

    laneDimensionComputedHere :
      Bool

    laneDimensionComputedHereIsFalse :
      laneDimensionComputedHere ≡ false

    promotesGDHREqualsGSM :
      Bool

    promotesGDHREqualsGSMIsFalse :
      promotesGDHREqualsGSM ≡ false

    noPromotionWithoutAuthority :
      PrimeLaneGaugeAssignmentPromotionAuthorityToken →
      ⊥

    boundary :
      List String

canonicalE8McKayLaneDimensionReceipt :
  E8McKayLaneDimensionReceipt
canonicalE8McKayLaneDimensionReceipt =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; e8MckayInput =
        e8MckayCorrespondenceAuthorityTarget
    ; smEmbeddingInput =
        standardModelInE8EmbeddingAuthorityTarget
    ; branchingReceipt =
        canonicalE8SMEmbeddingBranchingReceipt
    ; primeLaneTable =
        canonicalE8McKayPrimeLaneTableReceipt
    ; laneDimensionTargetRelation =
        laneDimension
    ; highEnergyLaneDimensionTarget =
        e8MckayHighEnergyLaneDimension
    ; highEnergyLaneDimensionTargetIsE8McKay =
        refl
    ; dhrLowEnergyLaneDimensionTarget =
        Moonshine.monsterPrimeLaneConjecturalDHRDimension
    ; dhrLowEnergyLaneDimensionTargetIsExistingConjecture =
        refl
    ; p7HighEnergyBridgeDim2 =
        refl
    ; p7LowEnergyDHRDim2 =
        refl
    ; bridgeIsConjectural =
        true
    ; bridgeIsConjecturalIsTrue =
        refl
    ; laneDimensionComputedHere =
        false
    ; laneDimensionComputedHereIsFalse =
        refl
    ; promotesGDHREqualsGSM =
        false
    ; promotesGDHREqualsGSMIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundary =
        "laneDimensionReceipt records a DASHI-specific bridge from E8MckayCorrespondence x SMinE8Embedding to the laneDimension target"
        ∷ "the provable external route is heterotic E8xE8 / Narain compactification with Wilson lines yielding U1Y x SU2L x SU3c, with Pati-Salam SU2R as the high-energy p7 extension"
        ∷ "the target is not computed here and does not promote G_DHR = G_SM"
        ∷ "p7 is the SU2R lane with dimension 2; low-energy Standard Model matching still requires the separate SU2R breaking receipt"
        ∷ []
    }

laneDimensionReceipt :
  E8MckayCorrespondence × SMinE8Embedding →
  E8McKayLaneDimensionReceipt
laneDimensionReceipt
  (e8MckayCorrespondenceAuthorityTarget
   ,
   standardModelInE8EmbeddingAuthorityTarget) =
  canonicalE8McKayLaneDimensionReceipt

data FormalGroupAutomorphismCorrectionPoint : Set where
  height2DieudonneModuleRank2 :
    FormalGroupAutomorphismCorrectionPoint

  weilPairingGivesSymplecticAutomorphisms :
    FormalGroupAutomorphismCorrectionPoint

  height2FormalGroupAloneGivesUniformSL2SU2 :
    FormalGroupAutomorphismCorrectionPoint

  doesNotProduceOneTwoThreeTwoTable :
    FormalGroupAutomorphismCorrectionPoint

  u1su2su3RequiresExtraRepresentationOrDeformationData :
    FormalGroupAutomorphismCorrectionPoint

canonicalFormalGroupAutomorphismCorrectionPoints :
  List FormalGroupAutomorphismCorrectionPoint
canonicalFormalGroupAutomorphismCorrectionPoints =
  height2DieudonneModuleRank2
  ∷ weilPairingGivesSymplecticAutomorphisms
  ∷ height2FormalGroupAloneGivesUniformSL2SU2
  ∷ doesNotProduceOneTwoThreeTwoTable
  ∷ u1su2su3RequiresExtraRepresentationOrDeformationData
  ∷ []

record FormalGroupAutomorphismCorrectionReceipt : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    correctionPoints :
      List FormalGroupAutomorphismCorrectionPoint

    correctionPointsAreCanonical :
      correctionPoints ≡ canonicalFormalGroupAutomorphismCorrectionPoints

    formalGroupAloneCompactRealForm :
      String

    formalGroupAloneCompactRealForm-v :
      formalGroupAloneCompactRealForm
      ≡
      "height-2-formal-group-Dieudonne-Weil-pairing-gives-SL2-SU2-shape-uniformly"

    doesNotComputeOneTwoThreeTwoTable :
      Bool

    doesNotComputeOneTwoThreeTwoTableIsTrue :
      doesNotComputeOneTwoThreeTwoTable ≡ true

    varyingLaneDimensionsRequireExtraData :
      Bool

    varyingLaneDimensionsRequireExtraDataIsTrue :
      varyingLaneDimensionsRequireExtraData ≡ true

    computesU1SU2SU3FromDieudonneAlone :
      Bool

    computesU1SU2SU3FromDieudonneAloneIsFalse :
      computesU1SU2SU3FromDieudonneAlone ≡ false

    promotesLaneDimension :
      Bool

    promotesLaneDimensionIsFalse :
      promotesLaneDimension ≡ false

    boundary :
      List String

canonicalFormalGroupAutomorphismCorrectionReceipt :
  FormalGroupAutomorphismCorrectionReceipt
canonicalFormalGroupAutomorphismCorrectionReceipt =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; correctionPoints =
        canonicalFormalGroupAutomorphismCorrectionPoints
    ; correctionPointsAreCanonical =
        refl
    ; formalGroupAloneCompactRealForm =
        "height-2-formal-group-Dieudonne-Weil-pairing-gives-SL2-SU2-shape-uniformly"
    ; formalGroupAloneCompactRealForm-v =
        refl
    ; doesNotComputeOneTwoThreeTwoTable =
        true
    ; doesNotComputeOneTwoThreeTwoTableIsTrue =
        refl
    ; varyingLaneDimensionsRequireExtraData =
        true
    ; varyingLaneDimensionsRequireExtraDataIsTrue =
        refl
    ; computesU1SU2SU3FromDieudonneAlone =
        false
    ; computesU1SU2SU3FromDieudonneAloneIsFalse =
        refl
    ; promotesLaneDimension =
        false
    ; promotesLaneDimensionIsFalse =
        refl
    ; boundary =
        "correction: the height-2 formal group, Dieudonne module, and Weil pairing give a uniform SL2/SU2-shaped automorphism form"
        ∷ "this uniform shape alone does not compute the lane-dimension table {1,2,3,2}"
        ∷ "U1, SU2, and SU3 lane variation must come from representation, deformation, or Monster/McKay data beyond the height-2 formal group alone"
        ∷ "this receipt prevents treating the Dieudonne-only calculation as a laneDimension proof"
        ∷ []
    }

data SerreTateLaneDimensionSubtheorem : Set where
  st1SerreTateDeformationEquivalence :
    SerreTateLaneDimensionSubtheorem

  st2HondaHeight2FormalGroup :
    SerreTateLaneDimensionSubtheorem

  st3HeteroticNarainE8OrNewMonsterIdentityGate :
    SerreTateLaneDimensionSubtheorem

canonicalSerreTateLaneDimensionSubtheorems :
  List SerreTateLaneDimensionSubtheorem
canonicalSerreTateLaneDimensionSubtheorems =
  st1SerreTateDeformationEquivalence
  ∷ st2HondaHeight2FormalGroup
  ∷ st3HeteroticNarainE8OrNewMonsterIdentityGate
  ∷ []

record PatiSalamLaneTableTheoremTarget : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    laneGaugeFactor :
      Moonshine.MonsterPrimeLane →
      E8McKayLaneGaugeFactor

    laneGaugeFactorIsCanonical :
      laneGaugeFactor ≡ e8MckayPrimeLaneGaugeFactor

    laneDimensionTarget :
      Moonshine.MonsterPrimeLane →
      Nat

    laneDimensionTargetIsHighEnergyTable :
      laneDimensionTarget ≡ e8MckayHighEnergyLaneDimension

    p2U1Dim1 :
      laneGaugeFactor Moonshine.p2 ≡ e8LaneU1Y

    p2Dimension1 :
      laneDimensionTarget Moonshine.p2 ≡ 1

    p3SU2LDim2 :
      laneGaugeFactor Moonshine.p3 ≡ e8LaneSU2L

    p3Dimension2 :
      laneDimensionTarget Moonshine.p3 ≡ 2

    p5SU3cDim3 :
      laneGaugeFactor Moonshine.p5 ≡ e8LaneSU3c

    p5Dimension3 :
      laneDimensionTarget Moonshine.p5 ≡ 3

    p7SU2RBrokenAtSeesawDim2 :
      laneGaugeFactor Moonshine.p7 ≡ e8LaneSU2RBrokenAtSeesaw

    p7Dimension2 :
      laneDimensionTarget Moonshine.p7 ≡ 2

    pAtLeast11GaugeTrivialMatter :
      (p : Moonshine.MonsterPrimeLane) →
      FractranLane.MonsterPrimeLaneAtLeast11 p →
      laneGaugeFactor p ≡ e8LaneMatterOrTrivialGauge

    pAtLeast11Dimension0 :
      (p : Moonshine.MonsterPrimeLane) →
      FractranLane.MonsterPrimeLaneAtLeast11 p →
      laneDimensionTarget p ≡ 0

    theoremTarget :
      Bool

    theoremTargetIsTrue :
      theoremTarget ≡ true

    theoremProvedHere :
      Bool

    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false

    boundary :
      List String

canonicalPatiSalamLaneTableTheoremTarget :
  PatiSalamLaneTableTheoremTarget
canonicalPatiSalamLaneTableTheoremTarget =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; laneGaugeFactor =
        e8MckayPrimeLaneGaugeFactor
    ; laneGaugeFactorIsCanonical =
        refl
    ; laneDimensionTarget =
        e8MckayHighEnergyLaneDimension
    ; laneDimensionTargetIsHighEnergyTable =
        refl
    ; p2U1Dim1 =
        refl
    ; p2Dimension1 =
        refl
    ; p3SU2LDim2 =
        refl
    ; p3Dimension2 =
        refl
    ; p5SU3cDim3 =
        refl
    ; p5Dimension3 =
        refl
    ; p7SU2RBrokenAtSeesawDim2 =
        refl
    ; p7Dimension2 =
        refl
    ; pAtLeast11GaugeTrivialMatter =
        λ where
          Moonshine.p11 FractranLane.p11AtLeast11 → refl
          Moonshine.p13 FractranLane.p13AtLeast11 → refl
          Moonshine.p17 FractranLane.p17AtLeast11 → refl
          Moonshine.p19 FractranLane.p19AtLeast11 → refl
          Moonshine.p23 FractranLane.p23AtLeast11 → refl
          Moonshine.p29 FractranLane.p29AtLeast11 → refl
          Moonshine.p31 FractranLane.p31AtLeast11 → refl
          Moonshine.p41 FractranLane.p41AtLeast11 → refl
          Moonshine.p47 FractranLane.p47AtLeast11 → refl
          Moonshine.p59 FractranLane.p59AtLeast11 → refl
          Moonshine.p71 FractranLane.p71AtLeast11 → refl
    ; pAtLeast11Dimension0 =
        e8MckayAtLeast11HighEnergyDimensionIs0
    ; theoremTarget =
        true
    ; theoremTargetIsTrue =
        refl
    ; theoremProvedHere =
        false
    ; theoremProvedHereIsFalse =
        refl
    ; boundary =
        "Pati-Salam lane table theorem target: p2 U1 dim1, p3 SU2L dim2, p5 SU3c dim3, p7 SU2R dim2 broken at seesaw"
        ∷ "p>=11 lanes are gauge-trivial or matter-sector lanes in this high-energy target"
        ∷ "the external theorem route is heterotic E8xE8 / Narain compactification with Wilson-line breaking and a Pati-Salam SU2R extension"
        ∷ "the p2,p3,p5,p7 prime labelling is a DASHI bridge table, not a first-principles theorem"
        ∷ "this is a theorem target, not a proved DHR laneDimension theorem"
        ∷ []
    }

record SerreTateLaneDimensionTheoremTarget : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    formalGroupCorrection :
      FormalGroupAutomorphismCorrectionReceipt

    subtheorems :
      List SerreTateLaneDimensionSubtheorem

    subtheoremsAreCanonical :
      subtheorems ≡ canonicalSerreTateLaneDimensionSubtheorems

    st1ClassicalSerreTateTheorem :
      Bool

    st1ClassicalSerreTateTheoremIsTrue :
      st1ClassicalSerreTateTheorem ≡ true

    st2ClassicalHondaHeight2Theorem :
      Bool

    st2ClassicalHondaHeight2TheoremIsTrue :
      st2ClassicalHondaHeight2Theorem ≡ true

    st3OpenComputation :
      Bool

    st3OpenComputationIsTrue :
      st3OpenComputation ≡ true

    patiSalamLaneTableTarget :
      PatiSalamLaneTableTheoremTarget

    theoremTarget :
      Bool

    theoremTargetIsTrue :
      theoremTarget ≡ true

    theoremProvedHere :
      Bool

    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false

    boundary :
      List String

canonicalSerreTateLaneDimensionTheoremTarget :
  SerreTateLaneDimensionTheoremTarget
canonicalSerreTateLaneDimensionTheoremTarget =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; formalGroupCorrection =
        canonicalFormalGroupAutomorphismCorrectionReceipt
    ; subtheorems =
        canonicalSerreTateLaneDimensionSubtheorems
    ; subtheoremsAreCanonical =
        refl
    ; st1ClassicalSerreTateTheorem =
        true
    ; st1ClassicalSerreTateTheoremIsTrue =
        refl
    ; st2ClassicalHondaHeight2Theorem =
        true
    ; st2ClassicalHondaHeight2TheoremIsTrue =
        refl
    ; st3OpenComputation =
        true
    ; st3OpenComputationIsTrue =
        refl
    ; patiSalamLaneTableTarget =
        canonicalPatiSalamLaneTableTheoremTarget
    ; theoremTarget =
        true
    ; theoremTargetIsTrue =
        refl
    ; theoremProvedHere =
        false
    ; theoremProvedHereIsFalse =
        refl
    ; boundary =
        "Serre-Tate target: ST1 deformation of the curve reduces to the p-divisible group, ST2 gives the Honda height-2 formal group"
        ∷ "honest ST3 conclusion: supersingular elliptic-curve arithmetic alone does not produce the required p-dependent laneDimension"
        ∷ "Dieudonne, Serre-Tate, conductor, Hecke eigenvalue, Frobenius, and modular-curve automorphism routes do not cleanly derive 1,2,3,2"
        ∷ "direct Monster coefficient extraction does not cleanly derive 1,2,3,2; the successful Moonshine route is instead Ogg plus no-ghost plus Dong-Li-Mason orbifold weight-1 data"
        ∷ "heterotic E8xE8 / Narain compactification remains bridge metadata, while DLM supplies authority-backed conditional laneDimension data"
        ∷ "the target table is Pati-Salam at high energy and is kept separate from the DLM laneDimension theorem surface"
        ∷ []
    }

data SymmetricTensorPowerCandidate : Set where
  sym0TrivialLine :
    SymmetricTensorPowerCandidate

  sym1StandardDoublet :
    SymmetricTensorPowerCandidate

  sym2AdjointTriplet :
    SymmetricTensorPowerCandidate

canonicalSymmetricTensorPowerCandidates :
  List SymmetricTensorPowerCandidate
canonicalSymmetricTensorPowerCandidates =
  sym0TrivialLine
  ∷ sym1StandardDoublet
  ∷ sym2AdjointTriplet
  ∷ []

record SymmetricTensorPowerRepresentationMechanismTarget : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    candidates :
      List SymmetricTensorPowerCandidate

    candidatesAreCanonical :
      candidates ≡ canonicalSymmetricTensorPowerCandidates

    sym0Dimension :
      Nat

    sym0DimensionIs1 :
      sym0Dimension ≡ 1

    sym1Dimension :
      Nat

    sym1DimensionIs2 :
      sym1Dimension ≡ 2

    sym2Dimension :
      Nat

    sym2DimensionIs3 :
      sym2Dimension ≡ 3

    candidateRepresentationMechanism :
      Bool

    candidateRepresentationMechanismIsTrue :
      candidateRepresentationMechanism ≡ true

    primeAssignmentProof :
      Bool

    primeAssignmentProofIsFalse :
      primeAssignmentProof ≡ false

    promotesLaneDimension :
      Bool

    promotesLaneDimensionIsFalse :
      promotesLaneDimension ≡ false

    boundary :
      List String

canonicalSymmetricTensorPowerRepresentationMechanismTarget :
  SymmetricTensorPowerRepresentationMechanismTarget
canonicalSymmetricTensorPowerRepresentationMechanismTarget =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; candidates =
        canonicalSymmetricTensorPowerCandidates
    ; candidatesAreCanonical =
        refl
    ; sym0Dimension =
        1
    ; sym0DimensionIs1 =
        refl
    ; sym1Dimension =
        2
    ; sym1DimensionIs2 =
        refl
    ; sym2Dimension =
        3
    ; sym2DimensionIs3 =
        refl
    ; candidateRepresentationMechanism =
        true
    ; candidateRepresentationMechanismIsTrue =
        refl
    ; primeAssignmentProof =
        false
    ; primeAssignmentProofIsFalse =
        refl
    ; promotesLaneDimension =
        false
    ; promotesLaneDimensionIsFalse =
        refl
    ; boundary =
        "candidate representation mechanism: Sym^0, Sym^1, and Sym^2 of an SL2/SU2-shaped carrier have dimensions 1, 2, and 3"
        ∷ "this may explain how 1/2/3-sized representation slots could be packaged once a prime-to-representation assignment is supplied"
        ∷ "it does not prove that primes p2,p3,p5,p7 select Sym^0, Sym^1, Sym^2, Sym^1"
        ∷ "it is not a DHR laneDimension theorem and does not promote prime assignment"
        ∷ []
    }

data FailedLaneDimensionFormulaAttempt : Set where
  conductorDiscriminantSketchNonInteger :
    FailedLaneDimensionFormulaAttempt

  conductorDiscriminantSketchNoCanonicalConductor :
    FailedLaneDimensionFormulaAttempt

  serreTateOnePlusDimVpMinus1ModPAtP3Mismatch :
    FailedLaneDimensionFormulaAttempt

canonicalFailedLaneDimensionFormulaAttempts :
  List FailedLaneDimensionFormulaAttempt
canonicalFailedLaneDimensionFormulaAttempts =
  conductorDiscriminantSketchNonInteger
  ∷ conductorDiscriminantSketchNoCanonicalConductor
  ∷ serreTateOnePlusDimVpMinus1ModPAtP3Mismatch
  ∷ []

record FailedLaneDimensionFormulaAttemptReceipt : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    attempts :
      List FailedLaneDimensionFormulaAttempt

    attemptsAreCanonical :
      attempts ≡ canonicalFailedLaneDimensionFormulaAttempts

    conductorDiscriminantSketchFailed :
      Bool

    conductorDiscriminantSketchFailedIsTrue :
      conductorDiscriminantSketchFailed ≡ true

    nonIntegerConductorDimensionObserved :
      Bool

    nonIntegerConductorDimensionObservedIsTrue :
      nonIntegerConductorDimensionObserved ≡ true

    discriminantConductorBridgeFailed :
      Bool

    discriminantConductorBridgeFailedIsTrue :
      discriminantConductorBridgeFailed ≡ true

    p3SerreTateFormulaValue :
      Nat

    p3SerreTateFormulaValueIs1 :
      p3SerreTateFormulaValue ≡ 1

    p3RequiredLaneDimension :
      Nat

    p3RequiredLaneDimensionIs2 :
      p3RequiredLaneDimension ≡ 2

    p3SerreTateFormulaMatchesTarget :
      Bool

    p3SerreTateFormulaMatchesTargetIsFalse :
      p3SerreTateFormulaMatchesTarget ≡ false

    formulaPromoted :
      Bool

    formulaPromotedIsFalse :
      formulaPromoted ≡ false

    boundary :
      List String

canonicalFailedLaneDimensionFormulaAttemptReceipt :
  FailedLaneDimensionFormulaAttemptReceipt
canonicalFailedLaneDimensionFormulaAttemptReceipt =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; attempts =
        canonicalFailedLaneDimensionFormulaAttempts
    ; attemptsAreCanonical =
        refl
    ; conductorDiscriminantSketchFailed =
        true
    ; conductorDiscriminantSketchFailedIsTrue =
        refl
    ; nonIntegerConductorDimensionObserved =
        true
    ; nonIntegerConductorDimensionObservedIsTrue =
        refl
    ; discriminantConductorBridgeFailed =
        true
    ; discriminantConductorBridgeFailedIsTrue =
        refl
    ; p3SerreTateFormulaValue =
        1
    ; p3SerreTateFormulaValueIs1 =
        refl
    ; p3RequiredLaneDimension =
        2
    ; p3RequiredLaneDimensionIs2 =
        refl
    ; p3SerreTateFormulaMatchesTarget =
        false
    ; p3SerreTateFormulaMatchesTargetIsFalse =
        refl
    ; formulaPromoted =
        false
    ; formulaPromotedIsFalse =
        refl
    ; boundary =
        "failed conductor/discriminant sketch: the attempted conductor-normalized dimension is non-integer or lacks a canonical discriminant-to-conductor bridge"
        ∷ "failed conductor sketch: no integral formula from the local conductor data cleanly yields {1,2,3,2}"
        ∷ "failed Serre-Tate residue sketch: the formula 1 + dim V_{p-1} mod p gives value 1 at p=3 under the attempted parsing, but the required p3 lane dimension is 2"
        ∷ "these formula attempts are recorded as failures only and are not promoted"
        ∷ []
    }

data FiniteMcKayThompsonRecipeStep : Set where
  extractA1FromTpA :
    FiniteMcKayThompsonRecipeStep

  reduceA1ModuloPSquaredMinus1 :
    FiniteMcKayThompsonRecipeStep

  identifyLowestWeightFaithfulRepresentation :
    FiniteMcKayThompsonRecipeStep

  finiteComputationStillOpen :
    FiniteMcKayThompsonRecipeStep

canonicalFiniteMcKayThompsonRecipeSteps :
  List FiniteMcKayThompsonRecipeStep
canonicalFiniteMcKayThompsonRecipeSteps =
  extractA1FromTpA
  ∷ reduceA1ModuloPSquaredMinus1
  ∷ identifyLowestWeightFaithfulRepresentation
  ∷ finiteComputationStillOpen
  ∷ []

record FiniteMcKayThompsonRecipeTarget : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    steps :
      List FiniteMcKayThompsonRecipeStep

    stepsAreCanonical :
      steps ≡ canonicalFiniteMcKayThompsonRecipeSteps

    seriesName :
      String

    seriesName-v :
      seriesName ≡ "T_pA"

    coefficientName :
      String

    coefficientName-v :
      coefficientName ≡ "a_1"

    modulusShape :
      String

    modulusShape-v :
      modulusShape ≡ "p^2-1"

    finiteComputationOpen :
      Bool

    finiteComputationOpenIsTrue :
      finiteComputationOpen ≡ true

    theoremProvedHere :
      Bool

    theoremProvedHereIsFalse :
      theoremProvedHere ≡ false

    boundary :
      List String

canonicalFiniteMcKayThompsonRecipeTarget :
  FiniteMcKayThompsonRecipeTarget
canonicalFiniteMcKayThompsonRecipeTarget =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; steps =
        canonicalFiniteMcKayThompsonRecipeSteps
    ; stepsAreCanonical =
        refl
    ; seriesName =
        "T_pA"
    ; seriesName-v =
        refl
    ; coefficientName =
        "a_1"
    ; coefficientName-v =
        refl
    ; modulusShape =
        "p^2-1"
    ; modulusShape-v =
        refl
    ; finiteComputationOpen =
        true
    ; finiteComputationOpenIsTrue =
        refl
    ; theoremProvedHere =
        false
    ; theoremProvedHereIsFalse =
        refl
    ; boundary =
        "finite McKay-Thompson recipe target: extract a_1 from T_{pA}"
        ∷ "reduce the extracted coefficient modulo p^2 - 1"
        ∷ "identify a lowest-weight faithful representation from the reduced residue"
        ∷ "the finite computation is open and is not a laneDimension theorem"
        ∷ []
    }

data MonsterMcKayComputationAttempt : Set where
  monsterCoefficientRouteNotClean :
    MonsterMcKayComputationAttempt

  dieudonneOnlyAttemptAllSU2 :
    MonsterMcKayComputationAttempt

  serreTateArithmeticRouteNotClean :
    MonsterMcKayComputationAttempt

  hodgeTateWeightsUniformInsufficient :
    MonsterMcKayComputationAttempt

  conductorAttemptAllDimension2 :
    MonsterMcKayComputationAttempt

  heckeEigenvalueRouteNotClean :
    MonsterMcKayComputationAttempt

  frobeniusInvariantUniformOrInsufficient :
    MonsterMcKayComputationAttempt

  modularCurveAutomorphismRouteNotClean :
    MonsterMcKayComputationAttempt

  vNaturalResidueFormulaMismatch :
    MonsterMcKayComputationAttempt

  newMonsterIdentityCandidateOpen :
    MonsterMcKayComputationAttempt

  heteroticE8CompactificationCandidateOpen :
    MonsterMcKayComputationAttempt

canonicalMonsterMcKayComputationAttempts :
  List MonsterMcKayComputationAttempt
canonicalMonsterMcKayComputationAttempts =
  monsterCoefficientRouteNotClean
  ∷ dieudonneOnlyAttemptAllSU2
  ∷ serreTateArithmeticRouteNotClean
  ∷ hodgeTateWeightsUniformInsufficient
  ∷ conductorAttemptAllDimension2
  ∷ heckeEigenvalueRouteNotClean
  ∷ frobeniusInvariantUniformOrInsufficient
  ∷ modularCurveAutomorphismRouteNotClean
  ∷ vNaturalResidueFormulaMismatch
  ∷ newMonsterIdentityCandidateOpen
  ∷ heteroticE8CompactificationCandidateOpen
  ∷ []

record MonsterMcKayLaneDimensionComputationAttemptReceipt : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    attempts :
      List MonsterMcKayComputationAttempt

    attemptsAreCanonical :
      attempts ≡ canonicalMonsterMcKayComputationAttempts

    symmetricTensorPowerMechanism :
      SymmetricTensorPowerRepresentationMechanismTarget

    failedFormulaAttempts :
      FailedLaneDimensionFormulaAttemptReceipt

    finiteMcKayThompsonRecipe :
      FiniteMcKayThompsonRecipeTarget

    monsterCoefficientRouteRejected :
      Bool

    monsterCoefficientRouteRejectedIsTrue :
      monsterCoefficientRouteRejected ≡ true

    dieudonneOnlyFormulaRejected :
      Bool

    dieudonneOnlyFormulaRejectedIsTrue :
      dieudonneOnlyFormulaRejected ≡ true

    hodgeTateWeightsInsufficient :
      Bool

    hodgeTateWeightsInsufficientIsTrue :
      hodgeTateWeightsInsufficient ≡ true

    serreTateArithmeticRouteRejected :
      Bool

    serreTateArithmeticRouteRejectedIsTrue :
      serreTateArithmeticRouteRejected ≡ true

    conductorFormulaRejected :
      Bool

    conductorFormulaRejectedIsTrue :
      conductorFormulaRejected ≡ true

    heckeEigenvalueRouteRejected :
      Bool

    heckeEigenvalueRouteRejectedIsTrue :
      heckeEigenvalueRouteRejected ≡ true

    frobeniusInvariantInsufficient :
      Bool

    frobeniusInvariantInsufficientIsTrue :
      frobeniusInvariantInsufficient ≡ true

    modularCurveAutomorphismRouteRejected :
      Bool

    modularCurveAutomorphismRouteRejectedIsTrue :
      modularCurveAutomorphismRouteRejected ≡ true

    vNaturalResidueFormulaRejected :
      Bool

    vNaturalResidueFormulaRejectedIsTrue :
      vNaturalResidueFormulaRejected ≡ true

    newMonsterIdentityCandidate :
      Bool

    newMonsterIdentityCandidateIsTrue :
      newMonsterIdentityCandidate ≡ true

    heteroticE8CompactificationCandidate :
      Bool

    heteroticE8CompactificationCandidateIsTrue :
      heteroticE8CompactificationCandidate ≡ true

    exactFormulaComputedHere :
      Bool

    exactFormulaComputedHereIsFalse :
      exactFormulaComputedHere ≡ false

    boundary :
      List String

canonicalMonsterMcKayLaneDimensionComputationAttemptReceipt :
  MonsterMcKayLaneDimensionComputationAttemptReceipt
canonicalMonsterMcKayLaneDimensionComputationAttemptReceipt =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; attempts =
        canonicalMonsterMcKayComputationAttempts
    ; attemptsAreCanonical =
        refl
    ; symmetricTensorPowerMechanism =
        canonicalSymmetricTensorPowerRepresentationMechanismTarget
    ; failedFormulaAttempts =
        canonicalFailedLaneDimensionFormulaAttemptReceipt
    ; finiteMcKayThompsonRecipe =
        canonicalFiniteMcKayThompsonRecipeTarget
    ; monsterCoefficientRouteRejected =
        true
    ; monsterCoefficientRouteRejectedIsTrue =
        refl
    ; dieudonneOnlyFormulaRejected =
        true
    ; dieudonneOnlyFormulaRejectedIsTrue =
        refl
    ; hodgeTateWeightsInsufficient =
        true
    ; hodgeTateWeightsInsufficientIsTrue =
        refl
    ; serreTateArithmeticRouteRejected =
        true
    ; serreTateArithmeticRouteRejectedIsTrue =
        refl
    ; conductorFormulaRejected =
        true
    ; conductorFormulaRejectedIsTrue =
        refl
    ; heckeEigenvalueRouteRejected =
        true
    ; heckeEigenvalueRouteRejectedIsTrue =
        refl
    ; frobeniusInvariantInsufficient =
        true
    ; frobeniusInvariantInsufficientIsTrue =
        refl
    ; modularCurveAutomorphismRouteRejected =
        true
    ; modularCurveAutomorphismRouteRejectedIsTrue =
        refl
    ; vNaturalResidueFormulaRejected =
        true
    ; vNaturalResidueFormulaRejectedIsTrue =
        refl
    ; newMonsterIdentityCandidate =
        true
    ; newMonsterIdentityCandidateIsTrue =
        refl
    ; heteroticE8CompactificationCandidate =
        true
    ; heteroticE8CompactificationCandidateIsTrue =
        refl
    ; exactFormulaComputedHere =
        false
    ; exactFormulaComputedHereIsFalse =
        refl
    ; boundary =
        "honest ST3 conclusion: supersingular elliptic-curve arithmetic alone does not give the required p-dependence for laneDimension"
        ∷ "failed attempt: Monster coefficient extraction / McKay-Thompson low-coefficient recipes do not currently cleanly derive 1,2,3,2"
        ∷ "open finite McKay-Thompson recipe target: extract a_1 from T_{pA}, reduce modulo p^2 - 1, and identify a lowest-weight faithful representation"
        ∷ "candidate mechanism only: Sym^0, Sym^1, and Sym^2 package dimensions 1,2,3 but do not assign primes or prove laneDimension"
        ∷ "failed attempt: Dieudonne/formal-group-only calculation gives SL2/SU2 uniformly and cannot explain 1,2,3,2"
        ∷ "failed attempt: Serre-Tate arithmetic by itself does not supply the p-dependent gauge-factor table"
        ∷ "failed attempt: conductor/discriminant sketches either become non-integer or fail to define a canonical conductor bridge"
        ∷ "failed attempt: 1 + dim V_{p-1} mod p gives the wrong value at p=3 under the attempted Serre-Tate residue formula"
        ∷ "failed attempt: Hodge-Tate weights are uniform or too coarse for the required prime-lane table"
        ∷ "failed attempt: conductor/full Tate-module calculation gives dimension 2 uniformly"
        ∷ "failed attempt: Hecke eigenvalue recipes do not cleanly isolate the required 1,2,3,2 table"
        ∷ "failed attempt: Frobenius slopes, traces, or local isogeny invariants are uniform or insufficient for the p-dependent table"
        ∷ "failed attempt: modular-curve automorphism routes do not cleanly derive the required table"
        ∷ "failed attempt: naive V-natural residue formulas mismatch the required p2,p3,p5,p7 table"
        ∷ "resolved route now recorded elsewhere: Ogg genus-zero plus no-ghost compatibility plus Dong-Li-Mason orbifold weight-1 Lie algebra table"
        ∷ []
    }

data HighestLeverageST3RoutePoint : Set where
  st3FiniteComputationRouteDowngraded :
    HighestLeverageST3RoutePoint

  dashiCarrierLaneDimensionExtraction :
    HighestLeverageST3RoutePoint

  heteroticNarainE8CompactificationGate :
    HighestLeverageST3RoutePoint

  wilsonLinePatiSalamBranchingGate :
    HighestLeverageST3RoutePoint

  newMonsterIdentityGate :
    HighestLeverageST3RoutePoint

canonicalHighestLeverageST3Route :
  List HighestLeverageST3RoutePoint
canonicalHighestLeverageST3Route =
  st3FiniteComputationRouteDowngraded
  ∷ dashiCarrierLaneDimensionExtraction
  ∷ heteroticNarainE8CompactificationGate
  ∷ wilsonLinePatiSalamBranchingGate
  ∷ newMonsterIdentityGate
  ∷ []

record LaneDimensionDeepestRemainingGateReceipt : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    serreTateTarget :
      SerreTateLaneDimensionTheoremTarget

    monsterMcKayAttempts :
      MonsterMcKayLaneDimensionComputationAttemptReceipt

    route :
      List HighestLeverageST3RoutePoint

    routeIsCanonical :
      route ≡ canonicalHighestLeverageST3Route

    st3FiniteComputationHighestLeverage :
      Bool

    st3FiniteComputationHighestLeverageIsFalse :
      st3FiniteComputationHighestLeverage ≡ false

    heteroticNarainE8RouteHighestLeverage :
      Bool

    heteroticNarainE8RouteHighestLeverageIsTrue :
      heteroticNarainE8RouteHighestLeverage ≡ true

    newMonsterIdentityRouteOpen :
      Bool

    newMonsterIdentityRouteOpenIsTrue :
      newMonsterIdentityRouteOpen ≡ true

    deepestGateOpen :
      Bool

    deepestGateOpenIsTrue :
      deepestGateOpen ≡ true

    computationCompletedHere :
      Bool

    computationCompletedHereIsFalse :
      computationCompletedHere ≡ false

    boundary :
      List String

canonicalLaneDimensionDeepestRemainingGateReceipt :
  LaneDimensionDeepestRemainingGateReceipt
canonicalLaneDimensionDeepestRemainingGateReceipt =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; serreTateTarget =
        canonicalSerreTateLaneDimensionTheoremTarget
    ; monsterMcKayAttempts =
        canonicalMonsterMcKayLaneDimensionComputationAttemptReceipt
    ; route =
        canonicalHighestLeverageST3Route
    ; routeIsCanonical =
        refl
    ; st3FiniteComputationHighestLeverage =
        false
    ; st3FiniteComputationHighestLeverageIsFalse =
        refl
    ; heteroticNarainE8RouteHighestLeverage =
        true
    ; heteroticNarainE8RouteHighestLeverageIsTrue =
        refl
    ; newMonsterIdentityRouteOpen =
        true
    ; newMonsterIdentityRouteOpenIsTrue =
        refl
    ; deepestGateOpen =
        true
    ; deepestGateOpenIsTrue =
        refl
    ; computationCompletedHere =
        false
    ; computationCompletedHereIsFalse =
        refl
    ; boundary =
        "current conclusion: ST3 finite computation is no longer the highest-leverage route"
        ∷ "ordinary supersingular elliptic-curve invariants and Monster coefficient recipes have been downgraded to insufficient boundary data for the p-dependence"
        ∷ "updated route: laneDimension is authority-backed and conditional on Ogg/no-ghost/Dong-Li-Mason orbifold data"
        ∷ "heterotic E8xE8 / Narain compactification remains supporting bridge metadata rather than the active laneDimension gate"
        ∷ "the local bridge still records non-promotion boundaries for G_DHR = G_SM and terminal claims"
        ∷ []
    }

record PatiSalamHighEnergyAssignmentBridgeReceipt : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    fractranValuationBridge :
      FractranLane.FractranPrimeLaneValuationReceiptSurface

    assignmentBridge :
      Moonshine.MonsterPrimeLane →
      FractranLane.HighEnergyPatiSalamLaneAssignment

    assignmentBridgeIsCanonical :
      assignmentBridge
      ≡
      FractranLane.patiSalamHighEnergyAssignment

    p2IsU1 :
      assignmentBridge Moonshine.p2
      ≡
      FractranLane.assignedU1

    p3IsSU2L :
      assignmentBridge Moonshine.p3
      ≡
      FractranLane.assignedSU2L

    p5IsSU3c :
      assignmentBridge Moonshine.p5
      ≡
      FractranLane.assignedSU3c

    p7IsSU2RBrokenAtSeesaw :
      assignmentBridge Moonshine.p7
      ≡
      FractranLane.assignedSU2RBrokenAtSeesaw

    pAtLeast11IsInactiveOrMatter :
      (p : Moonshine.MonsterPrimeLane) →
      FractranLane.MonsterPrimeLaneAtLeast11 p →
      assignmentBridge p
      ≡
      FractranLane.inactiveOrMatterLane

    assignmentBridgeIsConjectural :
      Bool

    assignmentBridgeIsConjecturalIsTrue :
      assignmentBridgeIsConjectural ≡ true

    assignmentBridgeIsDHRLaneDimension :
      Bool

    assignmentBridgeIsDHRLaneDimensionIsFalse :
      assignmentBridgeIsDHRLaneDimension ≡ false

    laneDimensionComputedByBridge :
      Bool

    laneDimensionComputedByBridgeIsFalse :
      laneDimensionComputedByBridge ≡ false

    boundary :
      List String

open PatiSalamHighEnergyAssignmentBridgeReceipt public

canonicalPatiSalamHighEnergyAssignmentBridgeReceipt :
  PatiSalamHighEnergyAssignmentBridgeReceipt
canonicalPatiSalamHighEnergyAssignmentBridgeReceipt =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; fractranValuationBridge =
        FractranLane.canonicalFractranPrimeLaneValuationReceiptSurface
    ; assignmentBridge =
        FractranLane.patiSalamHighEnergyAssignment
    ; assignmentBridgeIsCanonical =
        refl
    ; p2IsU1 =
        refl
    ; p3IsSU2L =
        refl
    ; p5IsSU3c =
        refl
    ; p7IsSU2RBrokenAtSeesaw =
        refl
    ; pAtLeast11IsInactiveOrMatter =
        FractranLane.patiSalamAtLeast11IsInactiveOrMatter
    ; assignmentBridgeIsConjectural =
        true
    ; assignmentBridgeIsConjecturalIsTrue =
        refl
    ; assignmentBridgeIsDHRLaneDimension =
        false
    ; assignmentBridgeIsDHRLaneDimensionIsFalse =
        refl
    ; laneDimensionComputedByBridge =
        false
    ; laneDimensionComputedByBridgeIsFalse =
        refl
    ; boundary =
        "conjectural high-energy Pati-Salam bridge: p2->U1, p3->SU2L, p5->SU3c, p7->SU2R broken at seesaw"
        ∷ "p>=11 lanes are inactive/matter lanes for this high-energy bridge"
        ∷ "the supersingular-prime-to-gauge-factor assignment is a DASHI-specific bridge, not a first-principles theorem"
        ∷ "this bridge is distinct from the authority-backed conditional DHR laneDimension relation and does not compute it"
        ∷ []
    }

record PrimeLaneLaneDimensionBlockerReceipt : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    soleDeepComputationBlocker :
      PrimeLaneDeepComputationBlocker

    trackedPrimeLane :
      List Moonshine.MonsterPrimeLane

    trackedPrimeLaneAreCanonical :
      trackedPrimeLane
      ≡
      Moonshine.canonicalMonsterPrimeLane

    primeLaneDHREndomorphismTarget :
      Moonshine.MonsterPrimeLane →
      DHR.LocalisedEndomorphism →
      Set

    primeLaneDHREndomorphismTargetFailClosed :
      PrimeLaneDHREndomorphismTargetFailClosedReceipt

    laneDimensionRelation :
      Moonshine.MonsterPrimeLane →
      Nat →
      Set

    laneDimensionStatus :
      LaneDimensionConjectureStatus

    laneDimensionConjecturalValue :
      Moonshine.MonsterPrimeLane →
      Nat

    laneDimension2Is1 :
      laneDimensionConjecturalValue Moonshine.p2 ≡ 1

    laneDimension3Is2 :
      laneDimensionConjecturalValue Moonshine.p3 ≡ 2

    laneDimension5Is3 :
      laneDimensionConjecturalValue Moonshine.p5 ≡ 3

    laneDimensionAtLeast11Is0 :
      (p : Moonshine.MonsterPrimeLane) →
      Moonshine.MonsterPrimeLaneAtLeast11 p →
      laneDimensionConjecturalValue p ≡ 0

    fractranValuationBridge :
      FractranLane.FractranPrimeLaneValuationReceiptSurface

    patiSalamHighEnergyBridge :
      PatiSalamHighEnergyAssignmentBridgeReceipt

    e8MckayLaneDimensionReceipt :
      E8McKayLaneDimensionReceipt

    formalGroupAutomorphismCorrection :
      FormalGroupAutomorphismCorrectionReceipt

    symmetricTensorPowerMechanism :
      SymmetricTensorPowerRepresentationMechanismTarget

    failedFormulaAttempts :
      FailedLaneDimensionFormulaAttemptReceipt

    finiteMcKayThompsonRecipe :
      FiniteMcKayThompsonRecipeTarget

    serreTateLaneDimensionTheoremTarget :
      SerreTateLaneDimensionTheoremTarget

    patiSalamLaneTableTheoremTarget :
      PatiSalamLaneTableTheoremTarget

    monsterMcKayComputationAttempts :
      MonsterMcKayLaneDimensionComputationAttemptReceipt

    laneDimensionDeepestRemainingGate :
      LaneDimensionDeepestRemainingGateReceipt

    laneDimensionInternalPromotionRecorded :
      Bool

    laneDimensionInternalPromotionRecordedIsTrue :
      laneDimensionInternalPromotionRecorded ≡ true

    laneDimensionComputed :
      Bool

    laneDimensionComputedIsTrue :
      laneDimensionComputed ≡ true

    laneDimensionComputedByDLM :
      Bool

    laneDimensionComputedByDLMIsTrue :
      laneDimensionComputedByDLM ≡ true

    laneDimensionDoesNotPromoteGaugeAssignment :
      Bool

    laneDimensionDoesNotPromoteGaugeAssignmentIsTrue :
      laneDimensionDoesNotPromoteGaugeAssignment ≡ true

    highEnergyBridgeIsNotLaneDimension :
      Bool

    highEnergyBridgeIsNotLaneDimensionIsTrue :
      highEnergyBridgeIsNotLaneDimension ≡ true

    noGaugeGroupEqualityClaim :
      Bool

    noGaugeGroupEqualityClaimIsTrue :
      noGaugeGroupEqualityClaim ≡ true

    dhrPrimitiveTypingIsNotBlocker :
      Bool

    dhrPrimitiveTypingIsNotBlockerIsTrue :
      dhrPrimitiveTypingIsNotBlocker ≡ true

    noPromotionWithoutAuthority :
      PrimeLaneGaugeAssignmentPromotionAuthorityToken →
      ⊥

    boundary :
      List String

canonicalPrimeLaneLaneDimensionBlockerReceipt :
  PrimeLaneLaneDimensionBlockerReceipt
canonicalPrimeLaneLaneDimensionBlockerReceipt =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; soleDeepComputationBlocker =
        laneDimensionDeepComputationBlocker
    ; trackedPrimeLane =
        Moonshine.canonicalMonsterPrimeLane
    ; trackedPrimeLaneAreCanonical =
        refl
    ; primeLaneDHREndomorphismTarget =
        primeLaneDHREndos
    ; primeLaneDHREndomorphismTargetFailClosed =
        canonicalPrimeLaneDHREndomorphismTargetFailClosedReceipt
    ; laneDimensionRelation =
        laneDimension
    ; laneDimensionStatus =
        laneDimensionInternallyPromotedNoGaugePromotion
    ; laneDimensionConjecturalValue =
        Moonshine.monsterPrimeLaneConjecturalDHRDimension
    ; laneDimension2Is1 =
        refl
    ; laneDimension3Is2 =
        refl
    ; laneDimension5Is3 =
        refl
    ; laneDimensionAtLeast11Is0 =
        Moonshine.monsterPrimeLaneDHRDimensionAtLeast11Is0
    ; fractranValuationBridge =
        FractranLane.canonicalFractranPrimeLaneValuationReceiptSurface
    ; patiSalamHighEnergyBridge =
        canonicalPatiSalamHighEnergyAssignmentBridgeReceipt
    ; e8MckayLaneDimensionReceipt =
        canonicalE8McKayLaneDimensionReceipt
    ; formalGroupAutomorphismCorrection =
        canonicalFormalGroupAutomorphismCorrectionReceipt
    ; symmetricTensorPowerMechanism =
        canonicalSymmetricTensorPowerRepresentationMechanismTarget
    ; failedFormulaAttempts =
        canonicalFailedLaneDimensionFormulaAttemptReceipt
    ; finiteMcKayThompsonRecipe =
        canonicalFiniteMcKayThompsonRecipeTarget
    ; serreTateLaneDimensionTheoremTarget =
        canonicalSerreTateLaneDimensionTheoremTarget
    ; patiSalamLaneTableTheoremTarget =
        canonicalPatiSalamLaneTableTheoremTarget
    ; monsterMcKayComputationAttempts =
        canonicalMonsterMcKayLaneDimensionComputationAttemptReceipt
    ; laneDimensionDeepestRemainingGate =
        canonicalLaneDimensionDeepestRemainingGateReceipt
    ; laneDimensionInternalPromotionRecorded =
        true
    ; laneDimensionInternalPromotionRecordedIsTrue =
        refl
    ; laneDimensionComputed =
        true
    ; laneDimensionComputedIsTrue =
        refl
    ; laneDimensionComputedByDLM =
        true
    ; laneDimensionComputedByDLMIsTrue =
        refl
    ; laneDimensionDoesNotPromoteGaugeAssignment =
        true
    ; laneDimensionDoesNotPromoteGaugeAssignmentIsTrue =
        refl
    ; highEnergyBridgeIsNotLaneDimension =
        true
    ; highEnergyBridgeIsNotLaneDimensionIsTrue =
        refl
    ; noGaugeGroupEqualityClaim =
        true
    ; noGaugeGroupEqualityClaimIsTrue =
        refl
    ; dhrPrimitiveTypingIsNotBlocker =
        true
    ; dhrPrimitiveTypingIsNotBlockerIsTrue =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundary =
        "laneDimension is authority-backed and conditional; gauge assignment and DHR/Standard Model matching remain non-promoted"
        ∷ "primeLaneDHREndos is a target predicate from supersingular Monster prime lanes to localized DHR endomorphisms"
        ∷ "DHR laneDimension is internally fixed as 2->1, 3->2, 5->3, 7->2, and primes >=11 -> 0"
        ∷ "Monster-order valuations are routed through a FRACDASH/FRACTRAN-style exact 15-exponent-vector bridge; the cap-at-3 projection is not treated as a DHR computation"
        ∷ "separate conjectural high-energy Pati-Salam bridge records p2->U1, p3->SU2L, p5->SU3c, p7->SU2R-broken-at-seesaw, and p>=11 inactive/matter"
        ∷ "E8/McKay laneDimensionReceipt is bridge metadata parallel to the authority-backed DLM route"
        ∷ "formal-group correction is explicit: height-2 formal group / Dieudonne / Weil pairing data alone gives a uniform SL2/SU2 shape, not {1,2,3,2}"
        ∷ "Sym^0/Sym^1/Sym^2 is recorded only as a candidate representation mechanism, not as a prime assignment proof"
        ∷ "Serre-Tate laneDimension theorem target isolates ST1 and ST2 as classical; ST3 honestly remains open because supersingular elliptic-curve arithmetic alone has no required p-dependence"
        ∷ "failed formula attempts include non-integer conductor/discriminant sketches and the failed 1 + dim V_{p-1} mod p calculation at p=3"
        ∷ "finite McKay-Thompson recipe target is open: extract a_1 from T_{pA}, reduce modulo p^2 - 1, identify a lowest-weight faithful representation"
        ∷ "Monster coefficient, Dieudonne, Serre-Tate, conductor, Hecke eigenvalue, Frobenius, and modular-curve automorphism routes do not cleanly derive 1,2,3,2"
        ∷ "laneDimension is not locally promoted; remaining non-promoted boundaries are DHR/SM matching, SU2R breaking, matter lanes, gauge assignment, and terminal authorities"
        ∷ "DHR endomorphism/category and Doplicher-Roberts authority surfaces remain separate from the DLM laneDimension computation"
        ∷ "No equality G_DHR = G_SM is asserted"
        ∷ []
    }

data ResidualHGroupTarget : Set where
  residualHGroupDefinitionTarget :
    ResidualHGroupTarget

  exactStandardModelMatchBranchTarget :
    ResidualHGroupTarget

  nontrivialResidualHBranchTarget :
    ResidualHGroupTarget

canonicalResidualHGroupTargets :
  List ResidualHGroupTarget
canonicalResidualHGroupTargets =
  residualHGroupDefinitionTarget
  ∷ exactStandardModelMatchBranchTarget
  ∷ nontrivialResidualHBranchTarget
  ∷ []

data GaugeAssignmentBranch : Set where
  exactSMMatchTargetBranch :
    GaugeAssignmentBranch

  nontrivialResidualHTargetBranch :
    GaugeAssignmentBranch

canonicalGaugeAssignmentBranches :
  List GaugeAssignmentBranch
canonicalGaugeAssignmentBranches =
  exactSMMatchTargetBranch
  ∷ nontrivialResidualHTargetBranch
  ∷ []

record PrimeLaneProduct15ReceiptSurface : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    laneCount :
      Nat

    laneCountIs15 :
      laneCount ≡ 15

    lanes :
      List PrimeLane15

    lanesAreCanonical :
      lanes ≡ canonicalPrimeLanes15

    productTargets :
      List PrimeLaneProductTarget

    productTargetsAreCanonical :
      productTargets ≡ canonicalPrimeLaneProductTargets

    productConstructed :
      Bool

    productConstructedIsFalse :
      productConstructed ≡ false

    noPromotionWithoutAuthority :
      PrimeLaneGaugeAssignmentPromotionAuthorityToken →
      ⊥

    boundary :
      List String

canonicalPrimeLaneProduct15ReceiptSurface :
  PrimeLaneProduct15ReceiptSurface
canonicalPrimeLaneProduct15ReceiptSurface =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; laneCount =
        15
    ; laneCountIs15 =
        refl
    ; lanes =
        canonicalPrimeLanes15
    ; lanesAreCanonical =
        refl
    ; productTargets =
        canonicalPrimeLaneProductTargets
    ; productTargetsAreCanonical =
        refl
    ; productConstructed =
        false
    ; productConstructedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundary =
        "15-lane product is recorded as a gauge-assignment target only"
        ∷ "no lane-wise Standard Model gauge factor assignment is computed here"
        ∷ "no cross-lane product compatibility theorem is proved here"
        ∷ []
    }

record ChenPairingClusterReceiptTarget : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    clusterTargets :
      List ChenPairingClusterTarget

    clusterTargetsAreCanonical :
      clusterTargets ≡ canonicalChenPairingClusterTargets

    pairingShape :
      String

    pairingShape-v :
      pairingShape
      ≡
      "Chen-pairing-and-cluster-extraction-target-for-prime-lane-gauge-assignment"

    chenPairingComputed :
      Bool

    chenPairingComputedIsFalse :
      chenPairingComputed ≡ false

    clusterTheoremProved :
      Bool

    clusterTheoremProvedIsFalse :
      clusterTheoremProved ≡ false

    noPromotionWithoutAuthority :
      PrimeLaneGaugeAssignmentPromotionAuthorityToken →
      ⊥

    boundary :
      List String

canonicalChenPairingClusterReceiptTarget :
  ChenPairingClusterReceiptTarget
canonicalChenPairingClusterReceiptTarget =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; clusterTargets =
        canonicalChenPairingClusterTargets
    ; clusterTargetsAreCanonical =
        refl
    ; pairingShape =
        "Chen-pairing-and-cluster-extraction-target-for-prime-lane-gauge-assignment"
    ; pairingShape-v =
        refl
    ; chenPairingComputed =
        false
    ; chenPairingComputedIsFalse =
        refl
    ; clusterTheoremProved =
        false
    ; clusterTheoremProvedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundary =
        "Chen pairing is a target for later computation, not a computed invariant here"
        ∷ "cluster extraction is a target for later proof, not a proved gauge-sector theorem here"
        ∷ []
    }

record DHRGaugeComputationAdapterBoundaryReceipt : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    adapterNoGoIndex :
      AdapterNoGo.AdapterIrreducibilityNoGoIndex

    dhrGaugeReceiptSurface :
      DHR.DHRGaugeReceiptSurface

    laneDimensionBlockerReceipt :
      PrimeLaneLaneDimensionBlockerReceipt

    dhrGaugeReceiptSurfaceStatus :
      String

    dhrGaugeReceiptSurfaceStatus-v :
      dhrGaugeReceiptSurfaceStatus
      ≡
      "DASHI.Physics.QFT.DHRGaugeReceiptSurface-present-target-only-no-DHR-gauge-promotion"

    computationBoundaries :
      List DHRGaugeComputationBoundary

    computationBoundariesAreCanonical :
      computationBoundaries ≡ canonicalDHRGaugeComputationBoundaries

    computationBoundariesAreLaneDimensionSingleton :
      computationBoundaries ≡ laneDimensionDLMEquivConsumedNoGaugePromotion ∷ []

    dhrPrimitiveTypingImported :
      Bool

    dhrPrimitiveTypingImportedIsTrue :
      dhrPrimitiveTypingImported ≡ true

    laneDimensionComputationConstructed :
      Bool

    laneDimensionComputationConstructedIsTrue :
      laneDimensionComputationConstructed ≡ true

    adapterIrreducibilityDischarged :
      Bool

    adapterIrreducibilityDischargedIsFalse :
      adapterIrreducibilityDischarged ≡ false

    noPromotionWithoutAuthority :
      PrimeLaneGaugeAssignmentPromotionAuthorityToken →
      ⊥

    boundary :
      List String

canonicalDHRGaugeComputationAdapterBoundaryReceipt :
  DHRGaugeComputationAdapterBoundaryReceipt
canonicalDHRGaugeComputationAdapterBoundaryReceipt =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; adapterNoGoIndex =
        AdapterNoGo.canonicalAdapterIrreducibilityNoGoIndex
    ; dhrGaugeReceiptSurface =
        DHR.canonicalDHRGaugeReceiptSurface
    ; laneDimensionBlockerReceipt =
        canonicalPrimeLaneLaneDimensionBlockerReceipt
    ; dhrGaugeReceiptSurfaceStatus =
        "DASHI.Physics.QFT.DHRGaugeReceiptSurface-present-target-only-no-DHR-gauge-promotion"
    ; dhrGaugeReceiptSurfaceStatus-v =
        refl
    ; computationBoundaries =
        canonicalDHRGaugeComputationBoundaries
    ; computationBoundariesAreCanonical =
        refl
    ; computationBoundariesAreLaneDimensionSingleton =
        refl
    ; dhrPrimitiveTypingImported =
        true
    ; dhrPrimitiveTypingImportedIsTrue =
        refl
    ; laneDimensionComputationConstructed =
        true
    ; laneDimensionComputationConstructedIsTrue =
        refl
    ; adapterIrreducibilityDischarged =
        false
    ; adapterIrreducibilityDischargedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundary =
        "DHR gauge computation is wired to DASHI.Physics.QFT.DHRGaugeReceiptSurface"
        ∷ "DHR primitive typing is imported and is not a prime-lane deep computation blocker"
        ∷ "internal laneDimension promotion is consumed here without promoting gauge assignment"
        ∷ "adapter metric-signature, Born-state, vacuum-selection, and coupling-calibration issues remain boundary context, not additional deep computation blockers"
        ∷ "AdapterIrreducibilityNoGoIndex is consumed only as an open target index, not as a discharged proof"
        ∷ []
    }

canonicalMatterLaneFNChargeProjection :
  (p : Moonshine.MonsterPrimeLane) →
  FractranLane.MonsterPrimeLaneAtLeast11 p →
  Matter.StandardModelMatterSectorTarget →
  Nat
canonicalMatterLaneFNChargeProjection _ _ Matter.leftQuarkDoubletTarget =
  3
canonicalMatterLaneFNChargeProjection _ _ Matter.rightUpQuarkTarget =
  4
canonicalMatterLaneFNChargeProjection _ _ Matter.rightDownQuarkTarget =
  4
canonicalMatterLaneFNChargeProjection _ _ Matter.leftLeptonDoubletTarget =
  2
canonicalMatterLaneFNChargeProjection _ _ Matter.rightChargedLeptonTarget =
  3
canonicalMatterLaneFNChargeProjection _ _ Matter.higgsDoubletTarget =
  0

record FNChargeAssignment : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    matterPrimeLaneReceipt :
      Matter.MatterPrimeLaneReceipt

    matterPrimeLaneReceiptIsCanonical :
      Bool

    matterPrimeLaneReceiptIsCanonicalIsTrue :
      matterPrimeLaneReceiptIsCanonical ≡ true

    firstLevelFRACDASHRegister :
      FractranLane.MonsterValuationExponentVectorReceipt

    firstLevelFRACDASHRegisterIsMonsterValuationVector :
      Bool

    firstLevelFRACDASHRegisterIsMonsterValuationVectorIsTrue :
      firstLevelFRACDASHRegisterIsMonsterValuationVector ≡ true

    cappedGaugeProjection :
      Moonshine.MonsterPrimeLane →
      Nat

    cappedGaugeProjectionIsCanonical :
      cappedGaugeProjection
      ≡
      FractranLane.valuationCappedAt3

    cappedGaugeProjectionOverproducedLaneCount :
      Nat

    cappedGaugeProjectionOverproducedLaneCountIs4 :
      cappedGaugeProjectionOverproducedLaneCount
      ≡
      FractranLane.overproducedSU3LikeLaneCount

    highEnergyGaugeAssignment :
      Moonshine.MonsterPrimeLane →
      FractranLane.HighEnergyPatiSalamLaneAssignment

    highEnergyGaugeAssignmentIsCanonical :
      highEnergyGaugeAssignment
      ≡
      FractranLane.patiSalamHighEnergyAssignment

    p2IsU1 :
      highEnergyGaugeAssignment Moonshine.p2
      ≡
      FractranLane.assignedU1

    p3IsSU2L :
      highEnergyGaugeAssignment Moonshine.p3
      ≡
      FractranLane.assignedSU2L

    p5IsSU3c :
      highEnergyGaugeAssignment Moonshine.p5
      ≡
      FractranLane.assignedSU3c

    p7IsSU2RBrokenAtSeesaw :
      highEnergyGaugeAssignment Moonshine.p7
      ≡
      FractranLane.assignedSU2RBrokenAtSeesaw

    matterPrimeLaneAssignment :
      (p : Moonshine.MonsterPrimeLane) →
      FractranLane.MonsterPrimeLaneAtLeast11 p →
      highEnergyGaugeAssignment p
      ≡
      FractranLane.inactiveOrMatterLane

    fnChargeProjection :
      (p : Moonshine.MonsterPrimeLane) →
      FractranLane.MonsterPrimeLaneAtLeast11 p →
      Matter.StandardModelMatterSectorTarget →
      Nat

    fnChargeProjectionIsCanonical :
      fnChargeProjection
      ≡
      canonicalMatterLaneFNChargeProjection

    p11LeftQuarkDoubletChargeIs3 :
      fnChargeProjection
        Moonshine.p11
        FractranLane.p11AtLeast11
        Matter.leftQuarkDoubletTarget
      ≡
      3

    p11RightUpQuarkChargeIs4 :
      fnChargeProjection
        Moonshine.p11
        FractranLane.p11AtLeast11
        Matter.rightUpQuarkTarget
      ≡
      4

    p11RightDownQuarkChargeIs4 :
      fnChargeProjection
        Moonshine.p11
        FractranLane.p11AtLeast11
        Matter.rightDownQuarkTarget
      ≡
      4

    p11LeftLeptonDoubletChargeIs2 :
      fnChargeProjection
        Moonshine.p11
        FractranLane.p11AtLeast11
        Matter.leftLeptonDoubletTarget
      ≡
      2

    p11RightChargedLeptonChargeIs3 :
      fnChargeProjection
        Moonshine.p11
        FractranLane.p11AtLeast11
        Matter.rightChargedLeptonTarget
      ≡
      3

    p11HiggsDoubletChargeIs0 :
      fnChargeProjection
        Moonshine.p11
        FractranLane.p11AtLeast11
        Matter.higgsDoubletTarget
      ≡
      0

    fnChargeIsSecondLevelFRACDASHExponentProjection :
      Bool

    fnChargeIsSecondLevelFRACDASHExponentProjectionIsTrue :
      fnChargeIsSecondLevelFRACDASHExponentProjection ≡ true

    fnChargeDependsOnMatterPrimeLaneReceipt :
      Bool

    fnChargeDependsOnMatterPrimeLaneReceiptIsTrue :
      fnChargeDependsOnMatterPrimeLaneReceipt ≡ true

    laneDimensionComputedByFNCharge :
      Bool

    laneDimensionComputedByFNChargeIsFalse :
      laneDimensionComputedByFNCharge ≡ false

    finalDHRLaneDimensionTheoremClaimed :
      Bool

    finalDHRLaneDimensionTheoremClaimedIsFalse :
      finalDHRLaneDimensionTheoremClaimed ≡ false

    noPromotionWithoutAuthority :
      PrimeLaneGaugeAssignmentPromotionAuthorityToken →
      ⊥

    boundary :
      List String

open FNChargeAssignment public

canonicalFNChargeAssignment :
  FNChargeAssignment
canonicalFNChargeAssignment =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; matterPrimeLaneReceipt =
        Matter.canonicalMatterPrimeLaneReceipt
    ; matterPrimeLaneReceiptIsCanonical =
        true
    ; matterPrimeLaneReceiptIsCanonicalIsTrue =
        refl
    ; firstLevelFRACDASHRegister =
        FractranLane.canonicalMonsterValuationExponentVectorReceipt
    ; firstLevelFRACDASHRegisterIsMonsterValuationVector =
        true
    ; firstLevelFRACDASHRegisterIsMonsterValuationVectorIsTrue =
        refl
    ; cappedGaugeProjection =
        FractranLane.valuationCappedAt3
    ; cappedGaugeProjectionIsCanonical =
        refl
    ; cappedGaugeProjectionOverproducedLaneCount =
        FractranLane.overproducedSU3LikeLaneCount
    ; cappedGaugeProjectionOverproducedLaneCountIs4 =
        refl
    ; highEnergyGaugeAssignment =
        FractranLane.patiSalamHighEnergyAssignment
    ; highEnergyGaugeAssignmentIsCanonical =
        refl
    ; p2IsU1 =
        refl
    ; p3IsSU2L =
        refl
    ; p5IsSU3c =
        refl
    ; p7IsSU2RBrokenAtSeesaw =
        refl
    ; matterPrimeLaneAssignment =
        FractranLane.patiSalamAtLeast11IsInactiveOrMatter
    ; fnChargeProjection =
        canonicalMatterLaneFNChargeProjection
    ; fnChargeProjectionIsCanonical =
        refl
    ; p11LeftQuarkDoubletChargeIs3 =
        refl
    ; p11RightUpQuarkChargeIs4 =
        refl
    ; p11RightDownQuarkChargeIs4 =
        refl
    ; p11LeftLeptonDoubletChargeIs2 =
        refl
    ; p11RightChargedLeptonChargeIs3 =
        refl
    ; p11HiggsDoubletChargeIs0 =
        refl
    ; fnChargeIsSecondLevelFRACDASHExponentProjection =
        true
    ; fnChargeIsSecondLevelFRACDASHExponentProjectionIsTrue =
        refl
    ; fnChargeDependsOnMatterPrimeLaneReceipt =
        true
    ; fnChargeDependsOnMatterPrimeLaneReceiptIsTrue =
        refl
    ; laneDimensionComputedByFNCharge =
        false
    ; laneDimensionComputedByFNChargeIsFalse =
        refl
    ; finalDHRLaneDimensionTheoremClaimed =
        false
    ; finalDHRLaneDimensionTheoremClaimedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundary =
        "FNChargeAssignment records a second-level FRACDASH exponent projection over matter prime lanes p>=11"
        ∷ "The first-level FRACDASH register remains the Monster valuation vector; the capped gauge projection still overproduces four cap-3 lanes"
        ∷ "The refined high-energy bridge remains p2->U1, p3->SU2L, p5->SU3c, p7->SU2R broken at seesaw"
        ∷ "The FN charge projection explicitly depends on MatterPrimeLaneReceipt and is not a matter-representation derivation"
        ∷ "No final DHR laneDimension theorem, G_DHR = G_SM theorem, or gauge promotion is claimed"
        ∷ []
    }

data PrimeLaneSMRepresentationAgreementStatus : Set where
  symbolicPrimeLaneDataBlocksExactSMTableAgreement :
    PrimeLaneSMRepresentationAgreementStatus

record PrimeLaneL3SMRepresentationTableAgreementReceipt : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    smRepresentationTable :
      Matter.L3SMRepresentationTableReceipt

    smRepresentationTableIsCanonical :
      Bool

    smRepresentationTableIsCanonicalIsTrue :
      smRepresentationTableIsCanonical ≡ true

    fnChargeAssignmentReceipt :
      FNChargeAssignment

    fnChargeAssignmentReceiptIsCanonical :
      Bool

    fnChargeAssignmentReceiptIsCanonicalIsTrue :
      fnChargeAssignmentReceiptIsCanonical ≡ true

    agreementStatus :
      PrimeLaneSMRepresentationAgreementStatus

    agreementStatusIsSymbolicBlocker :
      agreementStatus
      ≡
      symbolicPrimeLaneDataBlocksExactSMTableAgreement

    sevenSMRowsRecorded :
      Bool

    sevenSMRowsRecordedIsTrue :
      sevenSMRowsRecorded ≡ true

    primeLaneDataIsSymbolic :
      Bool

    primeLaneDataIsSymbolicIsTrue :
      primeLaneDataIsSymbolic ≡ true

    exactPrimeLaneToSMRowAgreementProved :
      Bool

    exactPrimeLaneToSMRowAgreementProvedIsFalse :
      exactPrimeLaneToSMRowAgreementProved ≡ false

    rightNeutrinoLaneAuthorityAvailable :
      Bool

    rightNeutrinoLaneAuthorityAvailableIsFalse :
      rightNeutrinoLaneAuthorityAvailable ≡ false

    noPromotionWithoutAuthority :
      PrimeLaneGaugeAssignmentPromotionAuthorityToken →
      ⊥

    boundary :
      List String

open PrimeLaneL3SMRepresentationTableAgreementReceipt public

canonicalPrimeLaneL3SMRepresentationTableAgreementReceipt :
  PrimeLaneL3SMRepresentationTableAgreementReceipt
canonicalPrimeLaneL3SMRepresentationTableAgreementReceipt =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; smRepresentationTable =
        Matter.canonicalL3SMRepresentationTableReceipt
    ; smRepresentationTableIsCanonical =
        true
    ; smRepresentationTableIsCanonicalIsTrue =
        refl
    ; fnChargeAssignmentReceipt =
        canonicalFNChargeAssignment
    ; fnChargeAssignmentReceiptIsCanonical =
        true
    ; fnChargeAssignmentReceiptIsCanonicalIsTrue =
        refl
    ; agreementStatus =
        symbolicPrimeLaneDataBlocksExactSMTableAgreement
    ; agreementStatusIsSymbolicBlocker =
        refl
    ; sevenSMRowsRecorded =
        true
    ; sevenSMRowsRecordedIsTrue =
        refl
    ; primeLaneDataIsSymbolic =
        true
    ; primeLaneDataIsSymbolicIsTrue =
        refl
    ; exactPrimeLaneToSMRowAgreementProved =
        false
    ; exactPrimeLaneToSMRowAgreementProvedIsFalse =
        refl
    ; rightNeutrinoLaneAuthorityAvailable =
        false
    ; rightNeutrinoLaneAuthorityAvailableIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundary =
        "L3 prime-lane agreement consumes the seven-row SMParticle representation table receipt"
        ∷ "The available prime-lane data is symbolic: high-energy Pati-Salam labels plus FN charge projections, not an exact row-by-row representation derivation"
        ∷ "Right-neutrino sector/lane authority remains unavailable, matching the staged blocker on the matter table"
        ∷ "Exact prime-lane-to-SM-row agreement is therefore blocked rather than silently promoted"
        ∷ []
    }

record ResidualHGroupBranchReceiptTarget : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    residualTargets :
      List ResidualHGroupTarget

    residualTargetsAreCanonical :
      residualTargets ≡ canonicalResidualHGroupTargets

    branches :
      List GaugeAssignmentBranch

    branchesAreCanonical :
      branches ≡ canonicalGaugeAssignmentBranches

    residualHGroupConstructed :
      Bool

    residualHGroupConstructedIsFalse :
      residualHGroupConstructed ≡ false

    exactSMMatchProved :
      Bool

    exactSMMatchProvedIsFalse :
      exactSMMatchProved ≡ false

    nontrivialResidualHProved :
      Bool

    nontrivialResidualHProvedIsFalse :
      nontrivialResidualHProved ≡ false

    noPromotionWithoutAuthority :
      PrimeLaneGaugeAssignmentPromotionAuthorityToken →
      ⊥

    boundary :
      List String

canonicalResidualHGroupBranchReceiptTarget :
  ResidualHGroupBranchReceiptTarget
canonicalResidualHGroupBranchReceiptTarget =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; residualTargets =
        canonicalResidualHGroupTargets
    ; residualTargetsAreCanonical =
        refl
    ; branches =
        canonicalGaugeAssignmentBranches
    ; branchesAreCanonical =
        refl
    ; residualHGroupConstructed =
        false
    ; residualHGroupConstructedIsFalse =
        refl
    ; exactSMMatchProved =
        false
    ; exactSMMatchProvedIsFalse =
        refl
    ; nontrivialResidualHProved =
        false
    ; nontrivialResidualHProvedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundary =
        "exact Standard Model match is one target branch, not a proved match"
        ∷ "nontrivial residual H is one target branch, not a constructed residual gauge group"
        ∷ "this surface records the branch split without selecting or promoting either branch"
        ∷ []
    }

record PrimeLaneGaugeAssignmentReceiptSurface : Setω where
  field
    status :
      PrimeLaneGaugeAssignmentStatus

    product15Receipt :
      PrimeLaneProduct15ReceiptSurface

    chenPairingClusterReceipt :
      ChenPairingClusterReceiptTarget

    laneDimensionBlockerReceipt :
      PrimeLaneLaneDimensionBlockerReceipt

    patiSalamHighEnergyBridgeReceipt :
      PatiSalamHighEnergyAssignmentBridgeReceipt

    e8MckayLaneDimensionReceipt :
      E8McKayLaneDimensionReceipt

    serreTateLaneDimensionTheoremTarget :
      SerreTateLaneDimensionTheoremTarget

    laneDimensionDeepestRemainingGate :
      LaneDimensionDeepestRemainingGateReceipt

    symmetricTensorPowerMechanism :
      SymmetricTensorPowerRepresentationMechanismTarget

    failedFormulaAttempts :
      FailedLaneDimensionFormulaAttemptReceipt

    finiteMcKayThompsonRecipe :
      FiniteMcKayThompsonRecipeTarget

    dhrAdapterBoundaryReceipt :
      DHRGaugeComputationAdapterBoundaryReceipt

    matterPrimeLaneReceiptTarget :
      Matter.MatterPrimeLaneReceiptTargetSurface

    fnChargeAssignment :
      FNChargeAssignment

    l3SMRepresentationTableAgreement :
      PrimeLaneL3SMRepresentationTableAgreementReceipt

    residualHBranchReceipt :
      ResidualHGroupBranchReceiptTarget

    terminalCompositionBoundaryStatus :
      String

    terminalCompositionBoundaryStatus-v :
      terminalCompositionBoundaryStatus
      ≡
      "GRQFTTerminalCompositionBoundary-terminalClaimPromoted=false-and-prime-lane-surface-is-receipt-only"

    gaugeAssignmentPromoted :
      Bool

    gaugeAssignmentPromotedIsFalse :
      gaugeAssignmentPromoted ≡ false

    noPromotionWithoutAuthority :
      PrimeLaneGaugeAssignmentPromotionAuthorityToken →
      ⊥

    boundary :
      List String

canonicalPrimeLaneGaugeAssignmentReceiptSurface :
  PrimeLaneGaugeAssignmentReceiptSurface
canonicalPrimeLaneGaugeAssignmentReceiptSurface =
  record
    { status =
        targetSurfaceOnlyNoGaugePromotion
    ; product15Receipt =
        canonicalPrimeLaneProduct15ReceiptSurface
    ; chenPairingClusterReceipt =
        canonicalChenPairingClusterReceiptTarget
    ; laneDimensionBlockerReceipt =
        canonicalPrimeLaneLaneDimensionBlockerReceipt
    ; patiSalamHighEnergyBridgeReceipt =
        canonicalPatiSalamHighEnergyAssignmentBridgeReceipt
    ; e8MckayLaneDimensionReceipt =
        canonicalE8McKayLaneDimensionReceipt
    ; serreTateLaneDimensionTheoremTarget =
        canonicalSerreTateLaneDimensionTheoremTarget
    ; laneDimensionDeepestRemainingGate =
        canonicalLaneDimensionDeepestRemainingGateReceipt
    ; symmetricTensorPowerMechanism =
        canonicalSymmetricTensorPowerRepresentationMechanismTarget
    ; failedFormulaAttempts =
        canonicalFailedLaneDimensionFormulaAttemptReceipt
    ; finiteMcKayThompsonRecipe =
        canonicalFiniteMcKayThompsonRecipeTarget
    ; dhrAdapterBoundaryReceipt =
        canonicalDHRGaugeComputationAdapterBoundaryReceipt
    ; matterPrimeLaneReceiptTarget =
        Matter.canonicalMatterPrimeLaneReceiptTargetSurface
    ; fnChargeAssignment =
        canonicalFNChargeAssignment
    ; l3SMRepresentationTableAgreement =
        canonicalPrimeLaneL3SMRepresentationTableAgreementReceipt
    ; residualHBranchReceipt =
        canonicalResidualHGroupBranchReceiptTarget
    ; terminalCompositionBoundaryStatus =
        "GRQFTTerminalCompositionBoundary-terminalClaimPromoted=false-and-prime-lane-surface-is-receipt-only"
    ; terminalCompositionBoundaryStatus-v =
        refl
    ; gaugeAssignmentPromoted =
        false
    ; gaugeAssignmentPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; boundary =
        "prime-lane gauge assignment is target-only and non-promoting"
        ∷ "15-lane product, Chen pairing/cluster extraction, DHR category surfaces, and residual H branches are recorded as targets only"
        ∷ "high-energy Pati-Salam bridge is wired separately from the internally computed low-energy DHR laneDimension"
        ∷ "E8/McKay laneDimensionReceipt remains bridge metadata; the DHR laneDimension computation is authority-backed and conditional on the DLM route"
        ∷ "current theorem-shaped path for laneDimension is Ogg genus-zero plus no-ghost compatibility plus Dong-Li-Mason orbifold weight-1 data"
        ∷ "heterotic E8 compactification and ST3 finite computations are retained as non-promoting historical or supporting bridge metadata"
        ∷ "formal-group correction remains explicit: height-2 formal group / Dieudonne / Weil pairing gives uniform SL2/SU2 shape only, not {1,2,3,2}"
        ∷ "Sym^0/Sym^1/Sym^2 is tracked as a candidate representation mechanism only"
        ∷ "failed conductor/Serre-Tate formulas and the open finite McKay-Thompson a_1 modulo p^2 - 1 recipe are recorded as non-theorem targets"
        ∷ "matter prime-lane receipt target is wired as a non-derived target surface"
        ∷ "FNChargeAssignment adds a second-level FRACDASH exponent projection tied to MatterPrimeLaneReceipt, without a final DHR laneDimension theorem claim"
        ∷ "L3 SM representation-table agreement is explicitly blocked: prime-lane data is symbolic and the right-neutrino sector/lane authority is missing"
        ∷ "laneDimension is not locally promoted here; gauge assignment, exact Standard Model matching, and terminal authority remain non-promoted"
        ∷ "no exact Standard Model gauge match is asserted"
        ∷ "no nontrivial residual H group is asserted"
        ∷ "no equality G_DHR = G_SM is asserted"
        ∷ "no adapter irreducibility no-go theorem is discharged"
        ∷ "no GRQFT, Standard Model, or TOE promotion authority token is constructed here"
        ∷ []
    }

primeLaneGaugeAssignmentIsNotPromoted :
  PrimeLaneGaugeAssignmentReceiptSurface.gaugeAssignmentPromoted
    canonicalPrimeLaneGaugeAssignmentReceiptSurface
  ≡
  false
primeLaneGaugeAssignmentIsNotPromoted =
  refl

------------------------------------------------------------------------
-- lower6/l3 prime-lane link to the SM representation table.
--
-- This is only a cross-receipt so the l3 table can be cited from the
-- prime-lane surface without upgrading the gauge assignment or exact SM match.

record Lower6PrimeLaneSMRepresentationTableLinkReceipt : Setω where
  field
    lower6PrimeLaneMatterTable :
      Matter.Lower6SMRepresentationTableReceipt

    lower6PrimeLaneMatterTableRecorded :
      Matter.lower6SMRepresentationTableRecorded lower6PrimeLaneMatterTable
      ≡
      true

    lower6PrimeLaneMatterTableStillNonPromoting :
      Matter.lower6SMRepresentationTablePromoted lower6PrimeLaneMatterTable
      ≡
      false

    lower6PrimeLaneGaugeSurface :
      PrimeLaneGaugeAssignmentReceiptSurface

    lower6PrimeLaneGaugeSurfaceStillNonPromoting :
      PrimeLaneGaugeAssignmentReceiptSurface.gaugeAssignmentPromoted
        lower6PrimeLaneGaugeSurface
      ≡
      false

    lower6PrimeLaneExactSMMatchStillFalse :
      ResidualHGroupBranchReceiptTarget.exactSMMatchProved
        (PrimeLaneGaugeAssignmentReceiptSurface.residualHBranchReceipt
          lower6PrimeLaneGaugeSurface)
      ≡
      false

    lower6PrimeLaneSMTableLinkRecorded :
      Bool

    lower6PrimeLaneSMTableLinkRecordedIsTrue :
      lower6PrimeLaneSMTableLinkRecorded ≡ true

    lower6PrimeLaneSMTableLinkPromoted :
      Bool

    lower6PrimeLaneSMTableLinkPromotedIsFalse :
      lower6PrimeLaneSMTableLinkPromoted ≡ false

    lower6PrimeLaneSMTableLinkBoundary :
      List String

open Lower6PrimeLaneSMRepresentationTableLinkReceipt public

canonicalLower6PrimeLaneSMRepresentationTableLinkReceipt :
  Lower6PrimeLaneSMRepresentationTableLinkReceipt
canonicalLower6PrimeLaneSMRepresentationTableLinkReceipt =
  record
    { lower6PrimeLaneMatterTable =
        Matter.canonicalLower6SMRepresentationTableReceipt
    ; lower6PrimeLaneMatterTableRecorded =
        refl
    ; lower6PrimeLaneMatterTableStillNonPromoting =
        refl
    ; lower6PrimeLaneGaugeSurface =
        canonicalPrimeLaneGaugeAssignmentReceiptSurface
    ; lower6PrimeLaneGaugeSurfaceStillNonPromoting =
        refl
    ; lower6PrimeLaneExactSMMatchStillFalse =
        refl
    ; lower6PrimeLaneSMTableLinkRecorded =
        true
    ; lower6PrimeLaneSMTableLinkRecordedIsTrue =
        refl
    ; lower6PrimeLaneSMTableLinkPromoted =
        false
    ; lower6PrimeLaneSMTableLinkPromotedIsFalse =
        refl
    ; lower6PrimeLaneSMTableLinkBoundary =
        "lower6/l3 links the local SM representation table into the prime-lane receipt surface"
        ∷ "the link does not prove an exact Standard Model gauge match"
        ∷ "prime-lane gauge assignment and residual-H branch selection remain non-promoted"
        ∷ []
    }

lower6PrimeLaneSMRepresentationTableLinkDoesNotPromote :
  lower6PrimeLaneSMTableLinkPromoted
    canonicalLower6PrimeLaneSMRepresentationTableLinkReceipt
  ≡
  false
lower6PrimeLaneSMRepresentationTableLinkDoesNotPromote =
  refl
