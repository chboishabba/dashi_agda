module DASHI.Physics.Closure.YMSprint117NormCriterionClosurePropagator where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)

import DASHI.Physics.Closure.YMSprint115NormWindowClosureCriterion
  as Norm115
import DASHI.Physics.Closure.YMSprint116NormGaugeWindowClosureReducer
  as Norm116

trans :
  {A : Set} {x y z : A} →
  x ≡ y →
  y ≡ z →
  x ≡ z
trans refl refl =
  refl

------------------------------------------------------------------------
-- Sprint117 norm-criterion closure propagator.
--
-- Sprint116 already packages a conditional norm/gauge-window reducer with
-- normCriterionClosedHere=true while keeping the external analytic and Clay
-- promotion gates false.  This module propagates exactly that conditional
-- closure into an explicit Sprint117 feed object.  It does not discharge the
-- external norm window, does not prove an unconditional norm-window theorem,
-- does not discharge quotient/gauge analytic feeds, and does not promote Clay
-- Yang-Mills.

sprintNumber : Nat
sprintNumber = 117

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMSprint117NormCriterionClosurePropagator.agda"

sprint116SourcePath : String
sprint116SourcePath =
  "DASHI/Physics/Closure/YMSprint116NormGaugeWindowClosureReducer.agda"

sprint115SourcePath : String
sprint115SourcePath =
  Norm116.sprint115SourcePath

normCriterionFeedPropagatorRecorded : Bool
normCriterionFeedPropagatorRecorded = true

normCriterionFeedClosedHere : Bool
normCriterionFeedClosedHere =
  Norm116.normCriterionClosedHere

externalNormWindowClosedHere : Bool
externalNormWindowClosedHere =
  false

unconditionalNormWindowTheoremProvedHere : Bool
unconditionalNormWindowTheoremProvedHere =
  false

quotientGaugeAnalyticFeedsDischargedHere : Bool
quotientGaugeAnalyticFeedsDischargedHere =
  false

externalAnalyticClosurePromotedHere : Bool
externalAnalyticClosurePromotedHere =
  false

terminalClayClaimPromoted : Bool
terminalClayClaimPromoted =
  false

clayYangMillsPromoted : Bool
clayYangMillsPromoted =
  false

propagatorStatementText : String
propagatorStatementText =
  "Sprint117 propagator: the Sprint116 conditional norm criterion closure is repackaged as an explicit norm criterion feed object."

sprint116FeedSourceText : String
sprint116FeedSourceText =
  "The feed source is the Sprint116 norm/gauge-window closure reducer receipt, whose normCriterionClosedHere flag is true by refl."

conditionalFeedText : String
conditionalFeedText =
  "The Sprint117 normCriterionFeedClosedHere flag is true because it is definitionally the Sprint116 normCriterionClosedHere flag."

externalBoundaryText : String
externalBoundaryText =
  "External norm-window closure, unconditional norm-window theorem closure, and quotient/gauge analytic-feed discharge remain false in Sprint117."

nonPromotionBoundaryText : String
nonPromotionBoundaryText =
  "Sprint117 only propagates a conditional feed object; terminal Clay claim promotion and Clay Yang-Mills promotion remain false."

data PropagatorLane : Set where
  sprint116-reducer-source-lane :
    PropagatorLane
  sprint115-criterion-source-lane :
    PropagatorLane
  conditional-norm-feed-lane :
    PropagatorLane
  boolean-equality-proof-lane :
    PropagatorLane
  external-boundary-lane :
    PropagatorLane
  nonpromotion-boundary-lane :
    PropagatorLane
  receipt-lane :
    PropagatorLane

data PropagatorStatus : Set where
  imported-sprint116-reducer :
    PropagatorStatus
  imported-sprint115-criterion :
    PropagatorStatus
  feed-propagated :
    PropagatorStatus
  equality-recorded :
    PropagatorStatus
  external-boundary-false :
    PropagatorStatus
  nonpromotion-false :
    PropagatorStatus
  receipt-recorded :
    PropagatorStatus

canonicalPropagatorLanes : List PropagatorLane
canonicalPropagatorLanes =
  sprint116-reducer-source-lane
  ∷ sprint115-criterion-source-lane
  ∷ conditional-norm-feed-lane
  ∷ boolean-equality-proof-lane
  ∷ external-boundary-lane
  ∷ nonpromotion-boundary-lane
  ∷ receipt-lane
  ∷ []

record Sprint116NormCriterionSource : Setω where
  constructor mkSprint116NormCriterionSource
  field
    reducerReceipt :
      Norm116.YMSprint116NormGaugeWindowClosureReducerReceipt
    reducerClosure :
      Norm116.ReducerClosure
    reducerTheoremBoundary :
      Norm116.ReducerTheoremBoundary
    reducerSourcePath :
      String
    criterionSourcePath :
      String
    importedReducerRecorded :
      Bool
    importedReducerRecordedIsTrue :
      importedReducerRecorded ≡ true
    importedNormCriterionClosed :
      Bool
    importedNormCriterionClosedIsTrue :
      importedNormCriterionClosed ≡ true
    importedClosureFieldClosed :
      Bool
    importedClosureFieldClosedIsTrue :
      importedClosureFieldClosed ≡ true
    importedExternalNormWindowClosed :
      Bool
    importedExternalNormWindowClosedIsFalse :
      importedExternalNormWindowClosed ≡ false
    importedUnconditionalNormWindowTheoremProved :
      Bool
    importedUnconditionalNormWindowTheoremProvedIsFalse :
      importedUnconditionalNormWindowTheoremProved ≡ false
    importedQuotientGaugeAnalyticFeedsDischarged :
      Bool
    importedQuotientGaugeAnalyticFeedsDischargedIsFalse :
      importedQuotientGaugeAnalyticFeedsDischarged ≡ false
    importedClayYangMillsPromoted :
      Bool
    importedClayYangMillsPromotedIsFalse :
      importedClayYangMillsPromoted ≡ false
    statement :
      String
    status :
      PropagatorStatus

sprint116NormCriterionSourceFromReceipt :
  Norm116.YMSprint116NormGaugeWindowClosureReducerReceipt →
  Sprint116NormCriterionSource
sprint116NormCriterionSourceFromReceipt receipt =
  mkSprint116NormCriterionSource
    receipt
    (Norm116.reducerClosure receipt)
    (Norm116.theoremBoundary receipt)
    sprint116SourcePath
    sprint115SourcePath
    Norm116.normGaugeWindowReducerRecorded
    refl
    Norm116.normCriterionClosedHere
    refl
    (Norm116.ReducerClosure.normCriterionClosed closure)
    (Norm116.ReducerClosure.normCriterionClosedIsTrue closure)
    (Norm116.ReducerClosure.externalNormWindowClosed closure)
    (Norm116.ReducerClosure.externalNormWindowClosedIsFalse closure)
    (Norm116.ReducerClosure.unconditionalNormWindowTheoremProved closure)
    (Norm116.ReducerClosure.unconditionalNormWindowTheoremProvedIsFalse
      closure)
    (Norm116.ReducerClosure.quotientGaugeAnalyticFeedsDischarged closure)
    (Norm116.ReducerClosure.quotientGaugeAnalyticFeedsDischargedIsFalse
      closure)
    (Norm116.clayYangMillsPromotedHere receipt)
    (Norm116.clayYangMillsPromotedHereIsFalse receipt)
    sprint116FeedSourceText
    imported-sprint116-reducer
  where
    closure : Norm116.ReducerClosure
    closure =
      Norm116.reducerClosure receipt

record NormCriterionFeedObject : Setω where
  constructor mkNormCriterionFeedObject
  field
    source :
      Sprint116NormCriterionSource
    sprint115Criterion :
      Norm115.NormWindowClosureCriterion
    packageConstant :
      Nat
    packageConstantIs645120 :
      packageConstant ≡ 645120
    packageConstantProduct :
      16 * 32 * 12 * 15 * 7 ≡ packageConstant
    normCriterionFeedClosed :
      Bool
    normCriterionFeedClosedIsTrue :
      normCriterionFeedClosed ≡ true
    feedEqualsSprint116Flag :
      normCriterionFeedClosed ≡ Norm116.normCriterionClosedHere
    importedClosureFieldEqualsFeed :
      Sprint116NormCriterionSource.importedClosureFieldClosed source ≡
      normCriterionFeedClosed
    externalNormWindowClosed :
      Bool
    externalNormWindowClosedIsFalse :
      externalNormWindowClosed ≡ false
    unconditionalNormWindowTheoremProved :
      Bool
    unconditionalNormWindowTheoremProvedIsFalse :
      unconditionalNormWindowTheoremProved ≡ false
    quotientGaugeAnalyticFeedsDischarged :
      Bool
    quotientGaugeAnalyticFeedsDischargedIsFalse :
      quotientGaugeAnalyticFeedsDischarged ≡ false
    externalAnalyticClosurePromoted :
      Bool
    externalAnalyticClosurePromotedIsFalse :
      externalAnalyticClosurePromoted ≡ false
    statement :
      String
    status :
      PropagatorStatus

normCriterionFeedObjectFromSource :
  Sprint116NormCriterionSource →
  NormCriterionFeedObject
normCriterionFeedObjectFromSource source =
  mkNormCriterionFeedObject
    source
    (Norm116.ReducerClosure.closedCriterion closure)
    645120
    refl
    refl
    normCriterionFeedClosedHere
    refl
    refl
    (Sprint116NormCriterionSource.importedClosureFieldClosedIsTrue source)
    externalNormWindowClosedHere
    refl
    unconditionalNormWindowTheoremProvedHere
    refl
    quotientGaugeAnalyticFeedsDischargedHere
    refl
    externalAnalyticClosurePromotedHere
    refl
    conditionalFeedText
    feed-propagated
  where
    closure : Norm116.ReducerClosure
    closure =
      Sprint116NormCriterionSource.reducerClosure source

record FeedBooleanEqualityLedger : Setω where
  constructor mkFeedBooleanEqualityLedger
  field
    feed :
      NormCriterionFeedObject
    feedClosed :
      Bool
    feedClosedIsTrue :
      feedClosed ≡ true
    sprint116Closed :
      Bool
    sprint116ClosedIsTrue :
      sprint116Closed ≡ true
    feedAndSprint116Agree :
      feedClosed ≡ sprint116Closed
    externalNormWindowClosed :
      Bool
    externalNormWindowClosedIsFalse :
      externalNormWindowClosed ≡ false
    unconditionalNormWindowTheoremProved :
      Bool
    unconditionalNormWindowTheoremProvedIsFalse :
      unconditionalNormWindowTheoremProved ≡ false
    quotientGaugeAnalyticFeedsDischarged :
      Bool
    quotientGaugeAnalyticFeedsDischargedIsFalse :
      quotientGaugeAnalyticFeedsDischarged ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    statement :
      String
    status :
      PropagatorStatus

booleanEqualityLedgerFromFeed :
  NormCriterionFeedObject →
  FeedBooleanEqualityLedger
booleanEqualityLedgerFromFeed feed =
  mkFeedBooleanEqualityLedger
    feed
    (NormCriterionFeedObject.normCriterionFeedClosed feed)
    (NormCriterionFeedObject.normCriterionFeedClosedIsTrue feed)
    Norm116.normCriterionClosedHere
    refl
    (trans
      (NormCriterionFeedObject.normCriterionFeedClosedIsTrue feed)
      refl)
    (NormCriterionFeedObject.externalNormWindowClosed feed)
    (NormCriterionFeedObject.externalNormWindowClosedIsFalse feed)
    (NormCriterionFeedObject.unconditionalNormWindowTheoremProved feed)
    (NormCriterionFeedObject.unconditionalNormWindowTheoremProvedIsFalse
      feed)
    (NormCriterionFeedObject.quotientGaugeAnalyticFeedsDischarged feed)
    (NormCriterionFeedObject.quotientGaugeAnalyticFeedsDischargedIsFalse
      feed)
    clayYangMillsPromoted
    refl
    conditionalFeedText
    equality-recorded

record ExternalNormCriterionBoundary : Setω where
  constructor mkExternalNormCriterionBoundary
  field
    source :
      Sprint116NormCriterionSource
    feed :
      NormCriterionFeedObject
    externalNormWindowClosed :
      Bool
    externalNormWindowClosedIsFalse :
      externalNormWindowClosed ≡ false
    unconditionalNormWindowTheoremProved :
      Bool
    unconditionalNormWindowTheoremProvedIsFalse :
      unconditionalNormWindowTheoremProved ≡ false
    quotientGaugeAnalyticFeedsDischarged :
      Bool
    quotientGaugeAnalyticFeedsDischargedIsFalse :
      quotientGaugeAnalyticFeedsDischarged ≡ false
    sourceExternalNormWindowClosed :
      Bool
    sourceExternalNormWindowClosedIsFalse :
      sourceExternalNormWindowClosed ≡ false
    sourceUnconditionalNormWindowTheoremProved :
      Bool
    sourceUnconditionalNormWindowTheoremProvedIsFalse :
      sourceUnconditionalNormWindowTheoremProved ≡ false
    sourceQuotientGaugeAnalyticFeedsDischarged :
      Bool
    sourceQuotientGaugeAnalyticFeedsDischargedIsFalse :
      sourceQuotientGaugeAnalyticFeedsDischarged ≡ false
    statement :
      String
    status :
      PropagatorStatus

externalBoundaryFromFeed :
  NormCriterionFeedObject →
  ExternalNormCriterionBoundary
externalBoundaryFromFeed feed =
  mkExternalNormCriterionBoundary
    source
    feed
    externalNormWindowClosedHere
    refl
    unconditionalNormWindowTheoremProvedHere
    refl
    quotientGaugeAnalyticFeedsDischargedHere
    refl
    (Sprint116NormCriterionSource.importedExternalNormWindowClosed source)
    (Sprint116NormCriterionSource.importedExternalNormWindowClosedIsFalse
      source)
    (Sprint116NormCriterionSource.importedUnconditionalNormWindowTheoremProved
      source)
    (Sprint116NormCriterionSource.importedUnconditionalNormWindowTheoremProvedIsFalse
      source)
    (Sprint116NormCriterionSource.importedQuotientGaugeAnalyticFeedsDischarged
      source)
    (Sprint116NormCriterionSource.importedQuotientGaugeAnalyticFeedsDischargedIsFalse
      source)
    externalBoundaryText
    external-boundary-false
  where
    source : Sprint116NormCriterionSource
    source =
      NormCriterionFeedObject.source feed

record NonPromotionBoundary : Setω where
  constructor mkNonPromotionBoundary
  field
    feed :
      NormCriterionFeedObject
    terminalClayClaimPromotedHere :
      Bool
    terminalClayClaimPromotedHereIsFalse :
      terminalClayClaimPromotedHere ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    sourceClayYangMillsPromoted :
      Bool
    sourceClayYangMillsPromotedIsFalse :
      sourceClayYangMillsPromoted ≡ false
    feedExternalAnalyticClosurePromoted :
      Bool
    feedExternalAnalyticClosurePromotedIsFalse :
      feedExternalAnalyticClosurePromoted ≡ false
    statement :
      String
    status :
      PropagatorStatus

nonPromotionBoundaryFromFeed :
  NormCriterionFeedObject →
  NonPromotionBoundary
nonPromotionBoundaryFromFeed feed =
  mkNonPromotionBoundary
    feed
    terminalClayClaimPromoted
    refl
    clayYangMillsPromoted
    refl
    (Sprint116NormCriterionSource.importedClayYangMillsPromoted source)
    (Sprint116NormCriterionSource.importedClayYangMillsPromotedIsFalse
      source)
    (NormCriterionFeedObject.externalAnalyticClosurePromoted feed)
    (NormCriterionFeedObject.externalAnalyticClosurePromotedIsFalse feed)
    nonPromotionBoundaryText
    nonpromotion-false
  where
    source : Sprint116NormCriterionSource
    source =
      NormCriterionFeedObject.source feed

record YMSprint117NormCriterionClosurePropagatorReceipt : Setω where
  constructor mkYMSprint117NormCriterionClosurePropagatorReceipt
  field
    sprint :
      Nat
    sourcePath :
      String
    sprint116Source :
      Sprint116NormCriterionSource
    normCriterionFeed :
      NormCriterionFeedObject
    booleanEqualityLedger :
      FeedBooleanEqualityLedger
    externalBoundary :
      ExternalNormCriterionBoundary
    nonPromotionBoundary :
      NonPromotionBoundary
    lanes :
      List PropagatorLane
    sourcePaths :
      List String
    evidenceLedger :
      List String
    recorded :
      Bool
    recordedIsTrue :
      recorded ≡ true
    normCriterionFeedClosedHereFlag :
      Bool
    normCriterionFeedClosedHereFlagIsTrue :
      normCriterionFeedClosedHereFlag ≡ true
    externalNormWindowClosedHereFlag :
      Bool
    externalNormWindowClosedHereFlagIsFalse :
      externalNormWindowClosedHereFlag ≡ false
    unconditionalNormWindowTheoremProvedHereFlag :
      Bool
    unconditionalNormWindowTheoremProvedHereFlagIsFalse :
      unconditionalNormWindowTheoremProvedHereFlag ≡ false
    quotientGaugeAnalyticFeedsDischargedHereFlag :
      Bool
    quotientGaugeAnalyticFeedsDischargedHereFlagIsFalse :
      quotientGaugeAnalyticFeedsDischargedHereFlag ≡ false
    terminalClayClaimPromotedHereFlag :
      Bool
    terminalClayClaimPromotedHereFlagIsFalse :
      terminalClayClaimPromotedHereFlag ≡ false
    clayYangMillsPromotedHere :
      Bool
    clayYangMillsPromotedHereIsFalse :
      clayYangMillsPromotedHere ≡ false
    finalReceiptStatement :
      String

open YMSprint117NormCriterionClosurePropagatorReceipt public

canonicalSprint116NormCriterionSource :
  Sprint116NormCriterionSource
canonicalSprint116NormCriterionSource =
  sprint116NormCriterionSourceFromReceipt Norm116.canonicalReceipt

canonicalNormCriterionFeedObject :
  NormCriterionFeedObject
canonicalNormCriterionFeedObject =
  normCriterionFeedObjectFromSource canonicalSprint116NormCriterionSource

canonicalFeedBooleanEqualityLedger :
  FeedBooleanEqualityLedger
canonicalFeedBooleanEqualityLedger =
  booleanEqualityLedgerFromFeed canonicalNormCriterionFeedObject

canonicalExternalNormCriterionBoundary :
  ExternalNormCriterionBoundary
canonicalExternalNormCriterionBoundary =
  externalBoundaryFromFeed canonicalNormCriterionFeedObject

canonicalNonPromotionBoundary :
  NonPromotionBoundary
canonicalNonPromotionBoundary =
  nonPromotionBoundaryFromFeed canonicalNormCriterionFeedObject

canonicalSourcePaths : List String
canonicalSourcePaths =
  sprint116SourcePath
  ∷ sprint115SourcePath
  ∷ modulePath
  ∷ []

canonicalEvidenceLedger : List String
canonicalEvidenceLedger =
  propagatorStatementText
  ∷ sprint116FeedSourceText
  ∷ Norm116.reducerStatementText
  ∷ Norm116.normAnalyticFeedText
  ∷ Norm115.normWindowCriterionStatementText
  ∷ conditionalFeedText
  ∷ externalBoundaryText
  ∷ Norm116.blockedAnalyticClosureText
  ∷ nonPromotionBoundaryText
  ∷ []

canonicalYMSprint117NormCriterionClosurePropagatorReceipt :
  YMSprint117NormCriterionClosurePropagatorReceipt
canonicalYMSprint117NormCriterionClosurePropagatorReceipt =
  mkYMSprint117NormCriterionClosurePropagatorReceipt
    sprintNumber
    modulePath
    canonicalSprint116NormCriterionSource
    canonicalNormCriterionFeedObject
    canonicalFeedBooleanEqualityLedger
    canonicalExternalNormCriterionBoundary
    canonicalNonPromotionBoundary
    canonicalPropagatorLanes
    canonicalSourcePaths
    canonicalEvidenceLedger
    normCriterionFeedPropagatorRecorded
    refl
    normCriterionFeedClosedHere
    refl
    externalNormWindowClosedHere
    refl
    unconditionalNormWindowTheoremProvedHere
    refl
    quotientGaugeAnalyticFeedsDischargedHere
    refl
    terminalClayClaimPromoted
    refl
    clayYangMillsPromoted
    refl
    propagatorStatementText

canonicalReceipt :
  YMSprint117NormCriterionClosurePropagatorReceipt
canonicalReceipt =
  canonicalYMSprint117NormCriterionClosurePropagatorReceipt

canonicalNormCriterionFeedClosedHere :
  normCriterionFeedClosedHereFlag canonicalReceipt ≡ true
canonicalNormCriterionFeedClosedHere =
  refl

canonicalNormCriterionFeedAgreesWithSprint116 :
  normCriterionFeedClosedHereFlag canonicalReceipt ≡
  Norm116.normCriterionClosedHere
canonicalNormCriterionFeedAgreesWithSprint116 =
  refl

canonicalExternalNormWindowClosedHereIsFalse :
  externalNormWindowClosedHereFlag canonicalReceipt ≡ false
canonicalExternalNormWindowClosedHereIsFalse =
  refl

canonicalUnconditionalNormWindowTheoremProvedHereIsFalse :
  unconditionalNormWindowTheoremProvedHereFlag canonicalReceipt ≡ false
canonicalUnconditionalNormWindowTheoremProvedHereIsFalse =
  refl

canonicalQuotientGaugeAnalyticFeedsDischargedHereIsFalse :
  quotientGaugeAnalyticFeedsDischargedHereFlag canonicalReceipt ≡ false
canonicalQuotientGaugeAnalyticFeedsDischargedHereIsFalse =
  refl

canonicalTerminalClayClaimPromotedHereIsFalse :
  terminalClayClaimPromotedHereFlag canonicalReceipt ≡ false
canonicalTerminalClayClaimPromotedHereIsFalse =
  refl

canonicalClayYangMillsPromotedIsFalse :
  clayYangMillsPromotedHere canonicalReceipt ≡ false
canonicalClayYangMillsPromotedIsFalse =
  refl

canonicalFeedObjectClosed :
  NormCriterionFeedObject.normCriterionFeedClosed
    (normCriterionFeed canonicalReceipt)
  ≡ true
canonicalFeedObjectClosed =
  refl

canonicalFeedObjectExternalBoundaryFalse :
  NormCriterionFeedObject.externalNormWindowClosed
    (normCriterionFeed canonicalReceipt)
  ≡ false
canonicalFeedObjectExternalBoundaryFalse =
  refl

canonicalFeedObjectUnconditionalBoundaryFalse :
  NormCriterionFeedObject.unconditionalNormWindowTheoremProved
    (normCriterionFeed canonicalReceipt)
  ≡ false
canonicalFeedObjectUnconditionalBoundaryFalse =
  refl

canonicalFeedObjectQuotientGaugeBoundaryFalse :
  NormCriterionFeedObject.quotientGaugeAnalyticFeedsDischarged
    (normCriterionFeed canonicalReceipt)
  ≡ false
canonicalFeedObjectQuotientGaugeBoundaryFalse =
  refl

canonicalFeedObjectClayBoundaryFalse :
  NonPromotionBoundary.clayYangMillsPromotedHere
    (nonPromotionBoundary canonicalReceipt)
  ≡ false
canonicalFeedObjectClayBoundaryFalse =
  refl
