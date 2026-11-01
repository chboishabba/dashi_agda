module DASHI.Physics.Closure.YMBTToFourDimensionalContinuumRouteBoundary where

-- BT -> flat 4D Euclidean continuum transfer boundary.
--
-- This module records the remaining route
--
--   finite BT quotient Hamiltonian + finite uniform gap route
--   -> depth-limit spectral stability
--   -> flat 4D Euclidean scaling window
--   -> continuum Schwinger-function / OS package
--   -> Wightman reconstruction and mass-gap survival
--
-- as a fail-closed ledger only.  It does not prove Balaban transfer, does
-- not prove no spectral pollution, does not prove the interacting continuum
-- construction, and keeps all promotion booleans false.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set; Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMSeiler1982GapCompatibilityBoundary
  as Seiler
import DASHI.Physics.Closure.YMBruhatTitsToOSLatticeTransferBoundary
  as Transfer

------------------------------------------------------------------------
-- Local utility.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Imported support.

record YMBTToFourDimensionalContinuumSupport : Setω where
  field
    seilerCompatibilityBoundary :
      Seiler.YMSeiler1982GapCompatibilityBoundary

    seilerCompatibilityBoundaryCanonical :
      Bool

    seilerCompatibilityBoundaryCanonicalIsTrue :
      seilerCompatibilityBoundaryCanonical ≡ true

    btToOSLatticeTransferBoundary :
      Transfer.YMBruhatTitsToOSLatticeTransferBoundary

    btToOSLatticeTransferBoundaryCanonical :
      Bool

    btToOSLatticeTransferBoundaryCanonicalIsTrue :
      btToOSLatticeTransferBoundaryCanonical ≡ true

open YMBTToFourDimensionalContinuumSupport public

canonicalYMBTToFourDimensionalContinuumSupport :
  YMBTToFourDimensionalContinuumSupport
canonicalYMBTToFourDimensionalContinuumSupport =
  record
    { seilerCompatibilityBoundary =
        Seiler.canonicalYMSeiler1982GapCompatibilityBoundary
    ; seilerCompatibilityBoundaryCanonical =
        true
    ; seilerCompatibilityBoundaryCanonicalIsTrue =
        refl
    ; btToOSLatticeTransferBoundary =
        Transfer.canonicalYMBruhatTitsToOSLatticeTransferBoundary
    ; btToOSLatticeTransferBoundaryCanonical =
        true
    ; btToOSLatticeTransferBoundaryCanonicalIsTrue =
        refl
    }

data YMBTToFourDimensionalContinuumImportedSurface : Set where
  seilerUniformGapCompatibilityImported :
    YMBTToFourDimensionalContinuumImportedSurface

  btToOSLatticeTransferImported :
    YMBTToFourDimensionalContinuumImportedSurface

canonicalYMBTToFourDimensionalContinuumImportedSurfaces :
  List YMBTToFourDimensionalContinuumImportedSurface
canonicalYMBTToFourDimensionalContinuumImportedSurfaces =
  seilerUniformGapCompatibilityImported
  ∷ btToOSLatticeTransferImported
  ∷ []

------------------------------------------------------------------------
-- Route vocabulary.

data YMBTToFourDimensionalContinuumRouteStatus : Set where
  btToFlat4DContinuumRouteRecordedNonPromotionBlockersRemain :
    YMBTToFourDimensionalContinuumRouteStatus

data YMBTToFourDimensionalContinuumStage : Set where
  consumeFiniteBTGapRouteStage :
    YMBTToFourDimensionalContinuumStage

  recordDepthLimitNoSpectralPollutionStage :
    YMBTToFourDimensionalContinuumStage

  recordFlatEuclideanScalingWindowStage :
    YMBTToFourDimensionalContinuumStage

  recordContinuumTightnessAndCylinderConsistencyStage :
    YMBTToFourDimensionalContinuumStage

  recordContinuumSchwingerFunctionStage :
    YMBTToFourDimensionalContinuumStage

  recordOSAxiomsStage :
    YMBTToFourDimensionalContinuumStage

  recordWightmanReconstructionStage :
    YMBTToFourDimensionalContinuumStage

  recordMassGapSurvivalStage :
    YMBTToFourDimensionalContinuumStage

  holdPromotionStage :
    YMBTToFourDimensionalContinuumStage

canonicalYMBTToFourDimensionalContinuumStages :
  List YMBTToFourDimensionalContinuumStage
canonicalYMBTToFourDimensionalContinuumStages =
  consumeFiniteBTGapRouteStage
  ∷ recordDepthLimitNoSpectralPollutionStage
  ∷ recordFlatEuclideanScalingWindowStage
  ∷ recordContinuumTightnessAndCylinderConsistencyStage
  ∷ recordContinuumSchwingerFunctionStage
  ∷ recordOSAxiomsStage
  ∷ recordWightmanReconstructionStage
  ∷ recordMassGapSurvivalStage
  ∷ holdPromotionStage
  ∷ []

data YMBTToFourDimensionalContinuumBlocker : Set where
  missingDepthLimitNoSpectralPollutionProof :
    YMBTToFourDimensionalContinuumBlocker

  missingFlatWindowCalibration :
    YMBTToFourDimensionalContinuumBlocker

  missingContinuumTightnessControl :
    YMBTToFourDimensionalContinuumBlocker

  missingCylinderObservableCompatibility :
    YMBTToFourDimensionalContinuumBlocker

  missingOS0ToOS4Closure :
    YMBTToFourDimensionalContinuumBlocker

  missingWightmanReconstructionCarrier :
    YMBTToFourDimensionalContinuumBlocker

  missingMassGapSurvivalTheorem :
    YMBTToFourDimensionalContinuumBlocker

  missingClayYangMillsAuthorityToken :
    YMBTToFourDimensionalContinuumBlocker

  missingTerminalPromotionAuthority :
    YMBTToFourDimensionalContinuumBlocker

canonicalYMBTToFourDimensionalContinuumBlockers :
  List YMBTToFourDimensionalContinuumBlocker
canonicalYMBTToFourDimensionalContinuumBlockers =
  missingDepthLimitNoSpectralPollutionProof
  ∷ missingFlatWindowCalibration
  ∷ missingContinuumTightnessControl
  ∷ missingCylinderObservableCompatibility
  ∷ missingOS0ToOS4Closure
  ∷ missingWightmanReconstructionCarrier
  ∷ missingMassGapSurvivalTheorem
  ∷ missingClayYangMillsAuthorityToken
  ∷ missingTerminalPromotionAuthority
  ∷ []

record YMBTToFourDimensionalContinuumStageRow : Set where
  field
    stage :
      YMBTToFourDimensionalContinuumStage

    label :
      String

    input :
      String

    output :
      String

    blocker :
      YMBTToFourDimensionalContinuumBlocker

    closed :
      Bool

    closedIsFalse :
      closed ≡ false

open YMBTToFourDimensionalContinuumStageRow public

finiteGapInputRow :
  YMBTToFourDimensionalContinuumStageRow
finiteGapInputRow =
  record
    { stage =
        consumeFiniteBTGapRouteStage
    ; label =
        "consume finite BT gap route"
    ; input =
        "finite BT quotient Hamiltonian plus uniform gamma_infty route ledger"
    ; output =
        "starting lower-bound package for continuum passage"
    ; blocker =
        missingDepthLimitNoSpectralPollutionProof
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

depthLimitRow :
  YMBTToFourDimensionalContinuumStageRow
depthLimitRow =
  record
    { stage =
        recordDepthLimitNoSpectralPollutionStage
    ; label =
        "depth-limit no spectral pollution"
    ; input =
        "finite BT lower bounds along depth truncations"
    ; output =
        "stable bottom-of-spectrum target through depth refinement"
    ; blocker =
        missingDepthLimitNoSpectralPollutionProof
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

flatWindowRow :
  YMBTToFourDimensionalContinuumStageRow
flatWindowRow =
  record
    { stage =
        recordFlatEuclideanScalingWindowStage
    ; label =
        "flat 4D scaling window"
    ; input =
        "BT lattice spacing, coupling normalization, and Euclidean rescaling choice"
    ; output =
        "candidate flat four-dimensional continuum window"
    ; blocker =
        missingFlatWindowCalibration
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

tightnessRow :
  YMBTToFourDimensionalContinuumStageRow
tightnessRow =
  record
    { stage =
        recordContinuumTightnessAndCylinderConsistencyStage
    ; label =
        "tightness and cylinder consistency"
    ; input =
        "observable families on depth-truncated BT approximants"
    ; output =
        "tight continuum candidate measures with compatible cylinder marginals"
    ; blocker =
        missingContinuumTightnessControl
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

schwingerRow :
  YMBTToFourDimensionalContinuumStageRow
schwingerRow =
  record
    { stage =
        recordContinuumSchwingerFunctionStage
    ; label =
        "continuum Schwinger functions"
    ; input =
        "tight measure candidate plus gauge-invariant cylinder observables"
    ; output =
        "Schwinger-function package on flat Euclidean 4-space"
    ; blocker =
        missingCylinderObservableCompatibility
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

osAxiomsRow :
  YMBTToFourDimensionalContinuumStageRow
osAxiomsRow =
  record
    { stage =
        recordOSAxiomsStage
    ; label =
        "OS0-OS4"
    ; input =
        "continuum Schwinger-function candidate"
    ; output =
        "full OS axiom package for constructive-QFT transfer"
    ; blocker =
        missingOS0ToOS4Closure
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

wightmanRow :
  YMBTToFourDimensionalContinuumStageRow
wightmanRow =
  record
    { stage =
        recordWightmanReconstructionStage
    ; label =
        "Wightman reconstruction"
    ; input =
        "OS0-OS4 plus reflection-positive continuum data"
    ; output =
        "Hilbert/QFT carrier with Hamiltonian spectrum"
    ; blocker =
        missingWightmanReconstructionCarrier
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

massGapSurvivalRow :
  YMBTToFourDimensionalContinuumStageRow
massGapSurvivalRow =
  record
    { stage =
        recordMassGapSurvivalStage
    ; label =
        "mass-gap survival"
    ; input =
        "positive gamma_infty candidate plus continuum reconstruction"
    ; output =
        "continuum spectral gap candidate Delta > 0"
    ; blocker =
        missingMassGapSurvivalTheorem
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

promotionHoldRow :
  YMBTToFourDimensionalContinuumStageRow
promotionHoldRow =
  record
    { stage =
        holdPromotionStage
    ; label =
        "non-promotion governance"
    ; input =
        "continuum route recorded with remaining constructive blockers"
    ; output =
        "Clay and terminal promotion kept false"
    ; blocker =
        missingClayYangMillsAuthorityToken
    ; closed =
        false
    ; closedIsFalse =
        refl
    }

canonicalYMBTToFourDimensionalContinuumStageRows :
  List YMBTToFourDimensionalContinuumStageRow
canonicalYMBTToFourDimensionalContinuumStageRows =
  finiteGapInputRow
  ∷ depthLimitRow
  ∷ flatWindowRow
  ∷ tightnessRow
  ∷ schwingerRow
  ∷ osAxiomsRow
  ∷ wightmanRow
  ∷ massGapSurvivalRow
  ∷ promotionHoldRow
  ∷ []

record YMBTToFourDimensionalContinuumBlockerRow : Set where
  field
    blocker :
      YMBTToFourDimensionalContinuumBlocker

    label :
      String

    routeImpact :
      String

    promotionStillFalse :
      Bool

    promotionStillFalseIsTrue :
      promotionStillFalse ≡ true

open YMBTToFourDimensionalContinuumBlockerRow public

depthPollutionBlockerRow : YMBTToFourDimensionalContinuumBlockerRow
depthPollutionBlockerRow =
  record
    { blocker =
        missingDepthLimitNoSpectralPollutionProof
    ; label =
        "depth-limit spectral stability missing"
    ; routeImpact =
        "cannot pass finite spectral bottoms to the continuum candidate"
    ; promotionStillFalse =
        true
    ; promotionStillFalseIsTrue =
        refl
    }

flatCalibrationBlockerRow : YMBTToFourDimensionalContinuumBlockerRow
flatCalibrationBlockerRow =
  record
    { blocker =
        missingFlatWindowCalibration
    ; label =
        "flat-window calibration missing"
    ; routeImpact =
        "cannot identify the BT route with flat Euclidean four-space"
    ; promotionStillFalse =
        true
    ; promotionStillFalseIsTrue =
        refl
    }

tightnessBlockerRow : YMBTToFourDimensionalContinuumBlockerRow
tightnessBlockerRow =
  record
    { blocker =
        missingContinuumTightnessControl
    ; label =
        "tightness control missing"
    ; routeImpact =
        "continuum measures may fail to exist or leak mass"
    ; promotionStillFalse =
        true
    ; promotionStillFalseIsTrue =
        refl
    }

cylinderCompatibilityBlockerRow : YMBTToFourDimensionalContinuumBlockerRow
cylinderCompatibilityBlockerRow =
  record
    { blocker =
        missingCylinderObservableCompatibility
    ; label =
        "cylinder observable compatibility missing"
    ; routeImpact =
        "continuum Schwinger functions are not yet coherent across observables"
    ; promotionStillFalse =
        true
    ; promotionStillFalseIsTrue =
        refl
    }

osClosureBlockerRow : YMBTToFourDimensionalContinuumBlockerRow
osClosureBlockerRow =
  record
    { blocker =
        missingOS0ToOS4Closure
    ; label =
        "OS axiom closure missing"
    ; routeImpact =
        "constructive-QFT reconstruction gate stays shut"
    ; promotionStillFalse =
        true
    ; promotionStillFalseIsTrue =
        refl
    }

wightmanBlockerRow : YMBTToFourDimensionalContinuumBlockerRow
wightmanBlockerRow =
  record
    { blocker =
        missingWightmanReconstructionCarrier
    ; label =
        "Wightman reconstruction carrier missing"
    ; routeImpact =
        "no physical Hilbert-space Hamiltonian is available"
    ; promotionStillFalse =
        true
    ; promotionStillFalseIsTrue =
        refl
    }

massGapBlockerRow : YMBTToFourDimensionalContinuumBlockerRow
massGapBlockerRow =
  record
    { blocker =
        missingMassGapSurvivalTheorem
    ; label =
        "mass-gap survival theorem missing"
    ; routeImpact =
        "positive lattice lower bounds do not yet survive to the continuum"
    ; promotionStillFalse =
        true
    ; promotionStillFalseIsTrue =
        refl
    }

clayAuthorityBlockerRow : YMBTToFourDimensionalContinuumBlockerRow
clayAuthorityBlockerRow =
  record
    { blocker =
        missingClayYangMillsAuthorityToken
    ; label =
        "Clay authority token missing"
    ; routeImpact =
        "no Clay-facing submission promotion is justified"
    ; promotionStillFalse =
        true
    ; promotionStillFalseIsTrue =
        refl
    }

terminalAuthorityBlockerRow : YMBTToFourDimensionalContinuumBlockerRow
terminalAuthorityBlockerRow =
  record
    { blocker =
        missingTerminalPromotionAuthority
    ; label =
        "terminal authority missing"
    ; routeImpact =
        "terminal unification promotion remains impossible"
    ; promotionStillFalse =
        true
    ; promotionStillFalseIsTrue =
        refl
    }

canonicalYMBTToFourDimensionalContinuumBlockerRows :
  List YMBTToFourDimensionalContinuumBlockerRow
canonicalYMBTToFourDimensionalContinuumBlockerRows =
  depthPollutionBlockerRow
  ∷ flatCalibrationBlockerRow
  ∷ tightnessBlockerRow
  ∷ cylinderCompatibilityBlockerRow
  ∷ osClosureBlockerRow
  ∷ wightmanBlockerRow
  ∷ massGapBlockerRow
  ∷ clayAuthorityBlockerRow
  ∷ terminalAuthorityBlockerRow
  ∷ []

------------------------------------------------------------------------
-- Fail-closed flags.

btContinuumRouteRecorded : Bool
btContinuumRouteRecorded =
  true

depthLimitNoSpectralPollutionProvedHere : Bool
depthLimitNoSpectralPollutionProvedHere =
  false

flat4DContinuumTransferProvedHere : Bool
flat4DContinuumTransferProvedHere =
  false

osWightmanContinuumConstructionProvedHere : Bool
osWightmanContinuumConstructionProvedHere =
  false

continuumMassGapPromoted : Bool
continuumMassGapPromoted =
  false

clayYangMillsPromoted : Bool
clayYangMillsPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

btContinuumRouteRecordedIsTrue :
  btContinuumRouteRecorded ≡ true
btContinuumRouteRecordedIsTrue =
  refl

depthLimitNoSpectralPollutionProvedHereIsFalse :
  depthLimitNoSpectralPollutionProvedHere ≡ false
depthLimitNoSpectralPollutionProvedHereIsFalse =
  refl

flat4DContinuumTransferProvedHereIsFalse :
  flat4DContinuumTransferProvedHere ≡ false
flat4DContinuumTransferProvedHereIsFalse =
  refl

osWightmanContinuumConstructionProvedHereIsFalse :
  osWightmanContinuumConstructionProvedHere ≡ false
osWightmanContinuumConstructionProvedHereIsFalse =
  refl

continuumMassGapPromotedIsFalse :
  continuumMassGapPromoted ≡ false
continuumMassGapPromotedIsFalse =
  refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

btToFlat4DRouteFormula : String
btToFlat4DRouteFormula =
  "finite BT gap route + no spectral pollution + flat 4D scaling + OS/Wightman reconstruction -> candidate continuum Delta > 0"

------------------------------------------------------------------------
-- Boundary receipt.

record YMBTToFourDimensionalContinuumRouteBoundary : Setω where
  field
    status :
      YMBTToFourDimensionalContinuumRouteStatus

    support :
      YMBTToFourDimensionalContinuumSupport

    supportCanonical :
      Bool

    supportCanonicalIsTrue :
      supportCanonical ≡ true

    importedSurfaces :
      List YMBTToFourDimensionalContinuumImportedSurface

    importedSurfacesAreCanonical :
      importedSurfaces ≡ canonicalYMBTToFourDimensionalContinuumImportedSurfaces

    importedSurfaceCount :
      Nat

    importedSurfaceCountIs2 :
      importedSurfaceCount ≡ 2

    stages :
      List YMBTToFourDimensionalContinuumStage

    stagesAreCanonical :
      stages ≡ canonicalYMBTToFourDimensionalContinuumStages

    stageCount :
      Nat

    stageCountIs9 :
      stageCount ≡ 9

    stageRows :
      List YMBTToFourDimensionalContinuumStageRow

    stageRowsAreCanonical :
      stageRows ≡ canonicalYMBTToFourDimensionalContinuumStageRows

    stageRowCount :
      Nat

    stageRowCountIs9 :
      stageRowCount ≡ 9

    blockers :
      List YMBTToFourDimensionalContinuumBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYMBTToFourDimensionalContinuumBlockers

    blockerCount :
      Nat

    blockerCountIs9 :
      blockerCount ≡ 9

    blockerRows :
      List YMBTToFourDimensionalContinuumBlockerRow

    blockerRowsAreCanonical :
      blockerRows ≡ canonicalYMBTToFourDimensionalContinuumBlockerRows

    blockerRowCount :
      Nat

    blockerRowCountIs9 :
      blockerRowCount ≡ 9

    firstBlocker :
      YMBTToFourDimensionalContinuumBlocker

    firstBlockerIsDepthLimitNoSpectralPollution :
      firstBlocker ≡ missingDepthLimitNoSpectralPollutionProof

    routeFormula :
      String

    routeFormulaIsCanonical :
      routeFormula ≡ btToFlat4DRouteFormula

    btContinuumRouteRecordedField :
      Bool

    btContinuumRouteRecordedFieldIsTrue :
      btContinuumRouteRecordedField ≡ true

    depthLimitNoSpectralPollutionProvedHereField :
      Bool

    depthLimitNoSpectralPollutionProvedHereFieldIsFalse :
      depthLimitNoSpectralPollutionProvedHereField ≡ false

    flat4DContinuumTransferProvedHereField :
      Bool

    flat4DContinuumTransferProvedHereFieldIsFalse :
      flat4DContinuumTransferProvedHereField ≡ false

    osWightmanContinuumConstructionProvedHereField :
      Bool

    osWightmanContinuumConstructionProvedHereFieldIsFalse :
      osWightmanContinuumConstructionProvedHereField ≡ false

    continuumMassGapPromotedField :
      Bool

    continuumMassGapPromotedFieldIsFalse :
      continuumMassGapPromotedField ≡ false

    clayYangMillsPromotedField :
      Bool

    clayYangMillsPromotedFieldIsFalse :
      clayYangMillsPromotedField ≡ false

    terminalPromotionField :
      Bool

    terminalPromotionFieldIsFalse :
      terminalPromotionField ≡ false

open YMBTToFourDimensionalContinuumRouteBoundary public

canonicalYMBTToFourDimensionalContinuumRouteBoundary :
  YMBTToFourDimensionalContinuumRouteBoundary
canonicalYMBTToFourDimensionalContinuumRouteBoundary =
  record
    { status =
        btToFlat4DContinuumRouteRecordedNonPromotionBlockersRemain
    ; support =
        canonicalYMBTToFourDimensionalContinuumSupport
    ; supportCanonical =
        true
    ; supportCanonicalIsTrue =
        refl
    ; importedSurfaces =
        canonicalYMBTToFourDimensionalContinuumImportedSurfaces
    ; importedSurfacesAreCanonical =
        refl
    ; importedSurfaceCount =
        listCount canonicalYMBTToFourDimensionalContinuumImportedSurfaces
    ; importedSurfaceCountIs2 =
        refl
    ; stages =
        canonicalYMBTToFourDimensionalContinuumStages
    ; stagesAreCanonical =
        refl
    ; stageCount =
        listCount canonicalYMBTToFourDimensionalContinuumStages
    ; stageCountIs9 =
        refl
    ; stageRows =
        canonicalYMBTToFourDimensionalContinuumStageRows
    ; stageRowsAreCanonical =
        refl
    ; stageRowCount =
        listCount canonicalYMBTToFourDimensionalContinuumStageRows
    ; stageRowCountIs9 =
        refl
    ; blockers =
        canonicalYMBTToFourDimensionalContinuumBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCount =
        listCount canonicalYMBTToFourDimensionalContinuumBlockers
    ; blockerCountIs9 =
        refl
    ; blockerRows =
        canonicalYMBTToFourDimensionalContinuumBlockerRows
    ; blockerRowsAreCanonical =
        refl
    ; blockerRowCount =
        listCount canonicalYMBTToFourDimensionalContinuumBlockerRows
    ; blockerRowCountIs9 =
        refl
    ; firstBlocker =
        missingDepthLimitNoSpectralPollutionProof
    ; firstBlockerIsDepthLimitNoSpectralPollution =
        refl
    ; routeFormula =
        btToFlat4DRouteFormula
    ; routeFormulaIsCanonical =
        refl
    ; btContinuumRouteRecordedField =
        btContinuumRouteRecorded
    ; btContinuumRouteRecordedFieldIsTrue =
        refl
    ; depthLimitNoSpectralPollutionProvedHereField =
        depthLimitNoSpectralPollutionProvedHere
    ; depthLimitNoSpectralPollutionProvedHereFieldIsFalse =
        refl
    ; flat4DContinuumTransferProvedHereField =
        flat4DContinuumTransferProvedHere
    ; flat4DContinuumTransferProvedHereFieldIsFalse =
        refl
    ; osWightmanContinuumConstructionProvedHereField =
        osWightmanContinuumConstructionProvedHere
    ; osWightmanContinuumConstructionProvedHereFieldIsFalse =
        refl
    ; continuumMassGapPromotedField =
        continuumMassGapPromoted
    ; continuumMassGapPromotedFieldIsFalse =
        refl
    ; clayYangMillsPromotedField =
        clayYangMillsPromoted
    ; clayYangMillsPromotedFieldIsFalse =
        refl
    ; terminalPromotionField =
        terminalPromotion
    ; terminalPromotionFieldIsFalse =
        refl
    }
