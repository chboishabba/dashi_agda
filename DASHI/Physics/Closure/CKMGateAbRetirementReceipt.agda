module DASHI.Physics.Closure.CKMGateAbRetirementReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CKM Gate A(b) angle-formula retirement receipt.
--
-- CKMGateAPartialCloseReceipt records the clean CM geometry at D=-7.
-- CKMGateAExperimentalStatusReceipt records that the pure
-- arctan(sqrt(7)) angle is in 5.4 sigma tension with HFLAV 2023.
-- This receipt closes the ledger entry that could otherwise be mistaken
-- for a prediction: arctan(sqrt(7)) is the canonical D=-7 CM angle, not
-- an adjustable or currently physical carrier prediction.

data GateAbAngleStatus : Set where
  formulaRetired :
    GateAbAngleStatus

data GateAbRetirementReason : Set where
  experimentalTensionFivePointFourSigma :
    GateAbRetirementReason

  noIsogenyKernelCorrection :
    GateAbRetirementReason

  atkinLehnerFixesCanonicalAngle :
    GateAbRetirementReason

  frobeniusArgumentSameCanonicalAngle :
    GateAbRetirementReason

data IsogenyAngleAuditStatus : Set where
  allSevenImagesChecked :
    IsogenyAngleAuditStatus

data PromotionToken : Set where

promotionImpossibleHere :
  PromotionToken →
  ⊥
promotionImpossibleHere ()

gammaPureDegrees :
  Float
gammaPureDegrees =
  69.30

gammaHFLAV2023Degrees :
  Float
gammaHFLAV2023Degrees =
  65.50

gammaHFLAV2023SigmaDegrees :
  Float
gammaHFLAV2023SigmaDegrees =
  0.70

gammaHFLAVTensionSigma :
  Float
gammaHFLAVTensionSigma =
  5.40

canonicalIsogenyImageAngleAudit :
  List Float
canonicalIsogenyImageAngleAudit =
  69.30
  ∷ 69.30
  ∷ 41.40
  ∷ 27.90
  ∷ 20.70
  ∷ 16.40
  ∷ 13.50
  ∷ []

canonicalRetirementReasons :
  List GateAbRetirementReason
canonicalRetirementReasons =
  experimentalTensionFivePointFourSigma
  ∷ noIsogenyKernelCorrection
  ∷ atkinLehnerFixesCanonicalAngle
  ∷ frobeniusArgumentSameCanonicalAngle
  ∷ []

canonicalSupersededAngleSurfaces :
  List String
canonicalSupersededAngleSurfaces =
  "CPPhaseFromArcTanSqrt7Receipt"
  ∷ "CPPhaseStructuralOriginReceipt"
  ∷ "CKMCPPhaseUpgradeReceipt"
  ∷ "YukawaCKMPaperReadinessReceipt"
  ∷ "CKMBetaCarrierDerivationReceipt"
  ∷ "ProgrammeUpgradeSummaryReceipt"
  ∷ "VubFromCKMUnitarityReceipt"
  ∷ "VubOpenStatusReceipt"
  ∷ []

angleFormulaStatement :
  String
angleFormulaStatement =
  "The pure D=-7 CM angle arctan(sqrt(7)) is 69.30 degrees, while HFLAV 2023 gives gamma=65.5+-0.7 degrees; the tension is 5.4 sigma."

isogenyAuditStatement :
  String
isogenyAuditStatement =
  "The seven cyclic 7-isogeny image angles were audited; the Atkin-Lehner image fixes arctan(sqrt(7)), and the remaining finite images lie near 41.4, 27.9, 20.7, 16.4, and 13.5 degrees rather than 65.5 degrees."

canonicalAngleStatement :
  String
canonicalAngleStatement =
  "The Frobenius argument arg((1+sqrt(-7))/2) gives the same canonical D=-7 CM angle, so the CM geometry supplies no adjustable correction mechanism."

record CKMGateAbRetirementReceipt : Set where
  field
    status :
      GateAbAngleStatus

    statusIsFormulaRetired :
      status ≡ formulaRetired

    gammaCarrierPure :
      Float

    gammaCarrierPureIs69Point30 :
      gammaCarrierPure ≡ gammaPureDegrees

    gammaExperimentalCentral :
      Float

    gammaExperimentalCentralIs65Point50 :
      gammaExperimentalCentral ≡ gammaHFLAV2023Degrees

    gammaExperimentalSigma :
      Float

    gammaExperimentalSigmaIs0Point70 :
      gammaExperimentalSigma ≡ gammaHFLAV2023SigmaDegrees

    hflavTension :
      Float

    hflavTensionIs5Point40Sigma :
      hflavTension ≡ gammaHFLAVTensionSigma

    formulaRetiredAsPrediction :
      Bool

    formulaRetiredAsPredictionIsTrue :
      formulaRetiredAsPrediction ≡ true

    notACarrierPrediction :
      Bool

    notACarrierPredictionIsTrue :
      notACarrierPrediction ≡ true

    gateAbAngleDerivationOpen :
      Bool

    gateAbAngleDerivationOpenIsTrue :
      gateAbAngleDerivationOpen ≡ true

    isogenyAngleAuditStatus :
      IsogenyAngleAuditStatus

    isogenyAngleAuditStatusIsComplete :
      isogenyAngleAuditStatus ≡ allSevenImagesChecked

    isogenyImageAnglesDegrees :
      List Float

    isogenyImageAnglesAreCanonical :
      isogenyImageAnglesDegrees ≡ canonicalIsogenyImageAngleAudit

    noIsogenyImageNearExperiment :
      Bool

    noIsogenyImageNearExperimentIsTrue :
      noIsogenyImageNearExperiment ≡ true

    atkinLehnerFixesAngle :
      Bool

    atkinLehnerFixesAngleIsTrue :
      atkinLehnerFixesAngle ≡ true

    frobeniusArgumentSameAngle :
      Bool

    frobeniusArgumentSameAngleIsTrue :
      frobeniusArgumentSameAngle ≡ true

    retirementReasons :
      List GateAbRetirementReason

    retirementReasonsAreCanonical :
      retirementReasons ≡ canonicalRetirementReasons

    supersededAngleSurfaces :
      List String

    supersededAngleSurfacesAreCanonical :
      supersededAngleSurfaces ≡ canonicalSupersededAngleSurfaces

    angleFormulaSummary :
      String

    angleFormulaSummaryIsCanonical :
      angleFormulaSummary ≡ angleFormulaStatement

    isogenyAuditSummary :
      String

    isogenyAuditSummaryIsCanonical :
      isogenyAuditSummary ≡ isogenyAuditStatement

    canonicalAngleSummary :
      String

    canonicalAngleSummaryIsCanonical :
      canonicalAngleSummary ≡ canonicalAngleStatement

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    G7Unblocked :
      Bool

    G7UnblockedIsFalse :
      G7Unblocked ≡ false

open CKMGateAbRetirementReceipt public

canonicalCKMGateAbRetirementReceipt :
  CKMGateAbRetirementReceipt
canonicalCKMGateAbRetirementReceipt =
  record
    { status =
        formulaRetired
    ; statusIsFormulaRetired =
        refl
    ; gammaCarrierPure =
        gammaPureDegrees
    ; gammaCarrierPureIs69Point30 =
        refl
    ; gammaExperimentalCentral =
        gammaHFLAV2023Degrees
    ; gammaExperimentalCentralIs65Point50 =
        refl
    ; gammaExperimentalSigma =
        gammaHFLAV2023SigmaDegrees
    ; gammaExperimentalSigmaIs0Point70 =
        refl
    ; hflavTension =
        gammaHFLAVTensionSigma
    ; hflavTensionIs5Point40Sigma =
        refl
    ; formulaRetiredAsPrediction =
        true
    ; formulaRetiredAsPredictionIsTrue =
        refl
    ; notACarrierPrediction =
        true
    ; notACarrierPredictionIsTrue =
        refl
    ; gateAbAngleDerivationOpen =
        true
    ; gateAbAngleDerivationOpenIsTrue =
        refl
    ; isogenyAngleAuditStatus =
        allSevenImagesChecked
    ; isogenyAngleAuditStatusIsComplete =
        refl
    ; isogenyImageAnglesDegrees =
        canonicalIsogenyImageAngleAudit
    ; isogenyImageAnglesAreCanonical =
        refl
    ; noIsogenyImageNearExperiment =
        true
    ; noIsogenyImageNearExperimentIsTrue =
        refl
    ; atkinLehnerFixesAngle =
        true
    ; atkinLehnerFixesAngleIsTrue =
        refl
    ; frobeniusArgumentSameAngle =
        true
    ; frobeniusArgumentSameAngleIsTrue =
        refl
    ; retirementReasons =
        canonicalRetirementReasons
    ; retirementReasonsAreCanonical =
        refl
    ; supersededAngleSurfaces =
        canonicalSupersededAngleSurfaces
    ; supersededAngleSurfacesAreCanonical =
        refl
    ; angleFormulaSummary =
        angleFormulaStatement
    ; angleFormulaSummaryIsCanonical =
        refl
    ; isogenyAuditSummary =
        isogenyAuditStatement
    ; isogenyAuditSummaryIsCanonical =
        refl
    ; canonicalAngleSummary =
        canonicalAngleStatement
    ; canonicalAngleSummaryIsCanonical =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; G7Unblocked =
        false
    ; G7UnblockedIsFalse =
        refl
    }

gateAbFormulaRetired :
  formulaRetiredAsPrediction canonicalCKMGateAbRetirementReceipt ≡ true
gateAbFormulaRetired =
  refl

gateAbNotACarrierPrediction :
  notACarrierPrediction canonicalCKMGateAbRetirementReceipt ≡ true
gateAbNotACarrierPrediction =
  refl

gateAbStillOpen :
  gateAbAngleDerivationOpen canonicalCKMGateAbRetirementReceipt ≡ true
gateAbStillOpen =
  refl

gateAbDoesNotPromoteCKM :
  physicalCKMPromoted canonicalCKMGateAbRetirementReceipt ≡ false
gateAbDoesNotPromoteCKM =
  refl
