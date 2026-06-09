module DASHI.Physics.Closure.PenguinDecayProjectionDefectReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Rare penguin decays as projection-defect detectors.
--
-- This receipt is intentionally finite and non-promoting.  It records a
-- closed local model in which flavour-changing neutral-current tree paths are
-- forbidden, the allowed Standard-Model route is loop-only/suppressed, and a
-- hidden residual surface can be extracted only as an indirect projection
-- defect.  No empirical promotion or new-physics claim is constructed here.

data PenguinReceiptStatus : Set where
  finiteProjectionDefectDetectorNonPromoting :
    PenguinReceiptStatus

data HeavyFlavour : Set where
  bottom :
    HeavyFlavour
  charm :
    HeavyFlavour

data RarePenguinDecay : Set where
  bToSLeptonPair :
    RarePenguinDecay
  bToDPhoton :
    RarePenguinDecay
  cToULeptonPair :
    RarePenguinDecay

canonicalRarePenguinDecays : List RarePenguinDecay
canonicalRarePenguinDecays =
  bToSLeptonPair
  ∷ bToDPhoton
  ∷ cToULeptonPair
  ∷ []

decaySourceFlavour : RarePenguinDecay → HeavyFlavour
decaySourceFlavour bToSLeptonPair =
  bottom
decaySourceFlavour bToDPhoton =
  bottom
decaySourceFlavour cToULeptonPair =
  charm

data NeutralCurrentTreePath : Set where
  zTreeFCNC :
    NeutralCurrentTreePath
  photonTreeFCNC :
    NeutralCurrentTreePath
  higgsTreeFCNC :
    NeutralCurrentTreePath

canonicalForbiddenTreePaths : List NeutralCurrentTreePath
canonicalForbiddenTreePaths =
  zTreeFCNC
  ∷ photonTreeFCNC
  ∷ higgsTreeFCNC
  ∷ []

treePathAllowed :
  RarePenguinDecay →
  NeutralCurrentTreePath →
  Bool
treePathAllowed bToSLeptonPair zTreeFCNC =
  false
treePathAllowed bToSLeptonPair photonTreeFCNC =
  false
treePathAllowed bToSLeptonPair higgsTreeFCNC =
  false
treePathAllowed bToDPhoton zTreeFCNC =
  false
treePathAllowed bToDPhoton photonTreeFCNC =
  false
treePathAllowed bToDPhoton higgsTreeFCNC =
  false
treePathAllowed cToULeptonPair zTreeFCNC =
  false
treePathAllowed cToULeptonPair photonTreeFCNC =
  false
treePathAllowed cToULeptonPair higgsTreeFCNC =
  false

allTreePathsForbidden :
  (decay : RarePenguinDecay) →
  (path : NeutralCurrentTreePath) →
  treePathAllowed decay path ≡ false
allTreePathsForbidden bToSLeptonPair zTreeFCNC =
  refl
allTreePathsForbidden bToSLeptonPair photonTreeFCNC =
  refl
allTreePathsForbidden bToSLeptonPair higgsTreeFCNC =
  refl
allTreePathsForbidden bToDPhoton zTreeFCNC =
  refl
allTreePathsForbidden bToDPhoton photonTreeFCNC =
  refl
allTreePathsForbidden bToDPhoton higgsTreeFCNC =
  refl
allTreePathsForbidden cToULeptonPair zTreeFCNC =
  refl
allTreePathsForbidden cToULeptonPair photonTreeFCNC =
  refl
allTreePathsForbidden cToULeptonPair higgsTreeFCNC =
  refl

data TransportRoute : Set where
  forbiddenTreeRoute :
    TransportRoute
  penguinLoopRoute :
    TransportRoute
  boxLoopRoute :
    TransportRoute
  hiddenResidualRoute :
    TransportRoute

data TransportSuppression : Set where
  unsuppressedTree :
    TransportSuppression
  loopSuppressed :
    TransportSuppression
  loopAndCKMSuppressed :
    TransportSuppression
  hiddenResidualSuppressed :
    TransportSuppression

transportSuppression :
  RarePenguinDecay →
  TransportRoute →
  TransportSuppression
transportSuppression bToSLeptonPair forbiddenTreeRoute =
  unsuppressedTree
transportSuppression bToSLeptonPair penguinLoopRoute =
  loopAndCKMSuppressed
transportSuppression bToSLeptonPair boxLoopRoute =
  loopAndCKMSuppressed
transportSuppression bToSLeptonPair hiddenResidualRoute =
  hiddenResidualSuppressed
transportSuppression bToDPhoton forbiddenTreeRoute =
  unsuppressedTree
transportSuppression bToDPhoton penguinLoopRoute =
  loopAndCKMSuppressed
transportSuppression bToDPhoton boxLoopRoute =
  loopSuppressed
transportSuppression bToDPhoton hiddenResidualRoute =
  hiddenResidualSuppressed
transportSuppression cToULeptonPair forbiddenTreeRoute =
  unsuppressedTree
transportSuppression cToULeptonPair penguinLoopRoute =
  loopAndCKMSuppressed
transportSuppression cToULeptonPair boxLoopRoute =
  loopAndCKMSuppressed
transportSuppression cToULeptonPair hiddenResidualRoute =
  hiddenResidualSuppressed

treeRouteRejected :
  RarePenguinDecay →
  TransportRoute
treeRouteRejected _ =
  forbiddenTreeRoute

acceptedSMTransport :
  RarePenguinDecay →
  List TransportRoute
acceptedSMTransport _ =
  penguinLoopRoute
  ∷ boxLoopRoute
  ∷ []

acceptedSMTransportIsLoopOnly :
  (decay : RarePenguinDecay) →
  acceptedSMTransport decay
  ≡
  (penguinLoopRoute ∷ boxLoopRoute ∷ [])
acceptedSMTransportIsLoopOnly _ =
  refl

data AmplitudeLayer : Set where
  smLoopAmplitude :
    AmplitudeLayer
  hiddenResidualAmplitude :
    AmplitudeLayer

data ProjectionSurface : Set where
  standardModelSurface :
    ProjectionSurface
  residualDefectSurface :
    ProjectionSurface
  totalDetectorSurface :
    ProjectionSurface

record AmplitudeCell : Set where
  constructor mkAmplitudeCell
  field
    decay :
      RarePenguinDecay

    layer :
      AmplitudeLayer

    route :
      TransportRoute

    coefficient :
      Nat

open AmplitudeCell public

smCell :
  RarePenguinDecay →
  AmplitudeCell
smCell decay =
  mkAmplitudeCell decay smLoopAmplitude penguinLoopRoute (suc zero)

hiddenResidualCell :
  RarePenguinDecay →
  AmplitudeCell
hiddenResidualCell decay =
  mkAmplitudeCell decay hiddenResidualAmplitude hiddenResidualRoute (suc zero)

projectToSM :
  AmplitudeCell →
  ProjectionSurface
projectToSM (mkAmplitudeCell _ smLoopAmplitude _ _) =
  standardModelSurface
projectToSM (mkAmplitudeCell _ hiddenResidualAmplitude _ _) =
  residualDefectSurface

projectionDefect :
  AmplitudeCell →
  ProjectionSurface
projectionDefect (mkAmplitudeCell _ smLoopAmplitude _ _) =
  totalDetectorSurface
projectionDefect (mkAmplitudeCell _ hiddenResidualAmplitude _ _) =
  residualDefectSurface

smAmplitudeProjectsToSMSurface :
  (decay : RarePenguinDecay) →
  projectToSM (smCell decay) ≡ standardModelSurface
smAmplitudeProjectsToSMSurface _ =
  refl

hiddenResidualProjectsToDefectSurface :
  (decay : RarePenguinDecay) →
  projectToSM (hiddenResidualCell decay) ≡ residualDefectSurface
hiddenResidualProjectsToDefectSurface _ =
  refl

hiddenResidualDefectIsResidualSurface :
  (decay : RarePenguinDecay) →
  projectionDefect (hiddenResidualCell decay) ≡ residualDefectSurface
hiddenResidualDefectIsResidualSurface _ =
  refl

data IndirectObservable : Set where
  branchingRatioDeviation :
    IndirectObservable
  angularCoefficientDeviation :
    IndirectObservable
  cpAsymmetryDeviation :
    IndirectObservable

canonicalIndirectObservables : List IndirectObservable
canonicalIndirectObservables =
  branchingRatioDeviation
  ∷ angularCoefficientDeviation
  ∷ cpAsymmetryDeviation
  ∷ []

data WitnessExtractionMode : Set where
  directAmplitudeInspection :
    WitnessExtractionMode
  indirectProjectionDefectExtraction :
    WitnessExtractionMode

extractionModeAllowed :
  WitnessExtractionMode →
  Bool
extractionModeAllowed directAmplitudeInspection =
  false
extractionModeAllowed indirectProjectionDefectExtraction =
  true

directAmplitudeInspectionRejected :
  extractionModeAllowed directAmplitudeInspection ≡ false
directAmplitudeInspectionRejected =
  refl

indirectProjectionDefectExtractionAllowed :
  extractionModeAllowed indirectProjectionDefectExtraction ≡ true
indirectProjectionDefectExtractionAllowed =
  refl

record IndirectWitness : Set where
  constructor mkIndirectWitness
  field
    witnessDecay :
      RarePenguinDecay

    observable :
      IndirectObservable

    extractionMode :
      WitnessExtractionMode

    projectedAmplitude :
      ProjectionSurface

    extractedDefect :
      ProjectionSurface

    extractionModeIsIndirect :
      extractionMode
      ≡
      indirectProjectionDefectExtraction

    projectedAmplitudeIsSM :
      projectedAmplitude
      ≡
      standardModelSurface

    extractedDefectIsResidual :
      extractedDefect
      ≡
      residualDefectSurface

open IndirectWitness public

extractIndirectWitness :
  RarePenguinDecay →
  IndirectObservable →
  IndirectWitness
extractIndirectWitness decay observable =
  mkIndirectWitness
    decay
    observable
    indirectProjectionDefectExtraction
    (projectToSM (smCell decay))
    (projectionDefect (hiddenResidualCell decay))
    refl
    refl
    refl

data PromotionObligation : Set where
  missingAcceptedSMAmplitudeReceipt :
    PromotionObligation
  missingLoopTransportNormalizationReceipt :
    PromotionObligation
  missingProjectionDefectCalibrationReceipt :
    PromotionObligation
  missingIndirectObservableExtractionReceipt :
    PromotionObligation
  missingExternalEmpiricalAuthorityReceipt :
    PromotionObligation
  missingNonSMPromotionAuthorityReceipt :
    PromotionObligation

canonicalPromotionObligations : List PromotionObligation
canonicalPromotionObligations =
  missingAcceptedSMAmplitudeReceipt
  ∷ missingLoopTransportNormalizationReceipt
  ∷ missingProjectionDefectCalibrationReceipt
  ∷ missingIndirectObservableExtractionReceipt
  ∷ missingExternalEmpiricalAuthorityReceipt
  ∷ missingNonSMPromotionAuthorityReceipt
  ∷ []

data PenguinDecayPromotionToken : Set where

penguinDecayPromotionImpossibleHere :
  PenguinDecayPromotionToken →
  ⊥
penguinDecayPromotionImpossibleHere ()

record PenguinDecayProjectionDefectReceipt : Set where
  field
    status :
      PenguinReceiptStatus

    decays :
      List RarePenguinDecay

    decaysAreCanonical :
      decays ≡ canonicalRarePenguinDecays

    forbiddenTreePaths :
      List NeutralCurrentTreePath

    forbiddenTreePathsAreCanonical :
      forbiddenTreePaths ≡ canonicalForbiddenTreePaths

    treePathAllowedBySM :
      RarePenguinDecay →
      NeutralCurrentTreePath →
      Bool

    treePathAllowedBySMIsFalse :
      (decay : RarePenguinDecay) →
      (path : NeutralCurrentTreePath) →
      treePathAllowedBySM decay path ≡ false

    smTransport :
      RarePenguinDecay →
      List TransportRoute

    smTransportIsLoopOnly :
      (decay : RarePenguinDecay) →
      smTransport decay ≡ penguinLoopRoute ∷ boxLoopRoute ∷ []

    suppressionLaw :
      RarePenguinDecay →
      TransportRoute →
      TransportSuppression

    smAmplitude :
      RarePenguinDecay →
      AmplitudeCell

    hiddenResidual :
      RarePenguinDecay →
      AmplitudeCell

    smAmplitudeProjectsCorrectly :
      (decay : RarePenguinDecay) →
      projectToSM (smAmplitude decay) ≡ standardModelSurface

    hiddenResidualProjectsCorrectly :
      (decay : RarePenguinDecay) →
      projectToSM (hiddenResidual decay) ≡ residualDefectSurface

    indirectObservables :
      List IndirectObservable

    indirectObservablesAreCanonical :
      indirectObservables ≡ canonicalIndirectObservables

    witnessExtractor :
      RarePenguinDecay →
      IndirectObservable →
      IndirectWitness

    witnessExtractorIsIndirect :
      (decay : RarePenguinDecay) →
      (observable : IndirectObservable) →
      extractionMode (witnessExtractor decay observable)
      ≡
      indirectProjectionDefectExtraction

    witnessExtractorReturnsSMProjection :
      (decay : RarePenguinDecay) →
      (observable : IndirectObservable) →
      projectedAmplitude (witnessExtractor decay observable)
      ≡
      standardModelSurface

    witnessExtractorReturnsResidualDefect :
      (decay : RarePenguinDecay) →
      (observable : IndirectObservable) →
      extractedDefect (witnessExtractor decay observable)
      ≡
      residualDefectSurface

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

    nonSMPromotionConstructedHere :
      Bool

    nonSMPromotionConstructedHereIsFalse :
      nonSMPromotionConstructedHere ≡ false

    promotionObligations :
      List PromotionObligation

    promotionObligationsAreCanonical :
      promotionObligations ≡ canonicalPromotionObligations

    promotionTokenBlocked :
      PenguinDecayPromotionToken →
      ⊥

    receiptBoundary :
      List String

open PenguinDecayProjectionDefectReceipt public

canonicalPenguinDecayProjectionDefectReceipt :
  PenguinDecayProjectionDefectReceipt
canonicalPenguinDecayProjectionDefectReceipt =
  record
    { status =
        finiteProjectionDefectDetectorNonPromoting
    ; decays =
        canonicalRarePenguinDecays
    ; decaysAreCanonical =
        refl
    ; forbiddenTreePaths =
        canonicalForbiddenTreePaths
    ; forbiddenTreePathsAreCanonical =
        refl
    ; treePathAllowedBySM =
        treePathAllowed
    ; treePathAllowedBySMIsFalse =
        allTreePathsForbidden
    ; smTransport =
        acceptedSMTransport
    ; smTransportIsLoopOnly =
        acceptedSMTransportIsLoopOnly
    ; suppressionLaw =
        transportSuppression
    ; smAmplitude =
        smCell
    ; hiddenResidual =
        hiddenResidualCell
    ; smAmplitudeProjectsCorrectly =
        smAmplitudeProjectsToSMSurface
    ; hiddenResidualProjectsCorrectly =
        hiddenResidualProjectsToDefectSurface
    ; indirectObservables =
        canonicalIndirectObservables
    ; indirectObservablesAreCanonical =
        refl
    ; witnessExtractor =
        extractIndirectWitness
    ; witnessExtractorIsIndirect =
        λ _ _ → refl
    ; witnessExtractorReturnsSMProjection =
        λ _ _ → refl
    ; witnessExtractorReturnsResidualDefect =
        λ _ _ → refl
    ; promoted =
        false
    ; promotedIsFalse =
        refl
    ; nonSMPromotionConstructedHere =
        false
    ; nonSMPromotionConstructedHereIsFalse =
        refl
    ; promotionObligations =
        canonicalPromotionObligations
    ; promotionObligationsAreCanonical =
        refl
    ; promotionTokenBlocked =
        penguinDecayPromotionImpossibleHere
    ; receiptBoundary =
        "Finite receipt for rare penguin decays as projection-defect detectors"
        ∷ "All neutral-current tree FCNC paths are rejected by explicit pattern matching"
        ∷ "Standard-Model transport is recorded as penguin-loop and box-loop only"
        ∷ "The hidden residual appears only on the residual projection-defect surface"
        ∷ "Witness extraction is indirect through observable deviations"
        ∷ "No direct amplitude inspection, empirical authority, or non-Standard-Model promotion is constructed here"
        ∷ []
    }

canonicalPenguinReceiptPromotedIsFalse :
  promoted canonicalPenguinDecayProjectionDefectReceipt ≡ false
canonicalPenguinReceiptPromotedIsFalse =
  refl

canonicalPenguinReceiptRejectsTree :
  (decay : RarePenguinDecay) →
  (path : NeutralCurrentTreePath) →
  treePathAllowedBySM
    canonicalPenguinDecayProjectionDefectReceipt
    decay
    path
  ≡
  false
canonicalPenguinReceiptRejectsTree decay path =
  treePathAllowedBySMIsFalse
    canonicalPenguinDecayProjectionDefectReceipt
    decay
    path

canonicalPenguinReceiptExtractsIndirectResidual :
  (decay : RarePenguinDecay) →
  (observable : IndirectObservable) →
  extractedDefect
    (witnessExtractor
      canonicalPenguinDecayProjectionDefectReceipt
      decay
      observable)
  ≡
  residualDefectSurface
canonicalPenguinReceiptExtractsIndirectResidual decay observable =
  witnessExtractorReturnsResidualDefect
    canonicalPenguinDecayProjectionDefectReceipt
    decay
    observable
