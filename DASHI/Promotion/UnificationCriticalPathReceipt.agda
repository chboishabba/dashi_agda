module DASHI.Promotion.UnificationCriticalPathReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Physics.Closure.ContractionForcesQuadraticTheorem as CFQT
import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
import DASHI.Physics.Closure.HodgeVariationPairingDepth9 as HV9
import DASHI.Physics.Closure.YangMillsFieldEquationObstruction as YMObs
import DASHI.Promotion.ChemistryFiniteComputationSurface as Chemistry
import DASHI.Promotion.DefectQuadraticClosureDependencyIndex as DefectIndex
import DASHI.Promotion.DownloadedNewAdditionsReferenceIndex as Downloaded
import DASHI.Promotion.FiniteQuantumQFTScopedClosure as Quantum
import DASHI.Promotion.StandardModelHiggsCovariantComparisonLaw as Higgs
import DASHI.Promotion.YMStrictHodgeVariationBlockerIndex as YMHodgeIndex

------------------------------------------------------------------------
-- Unification critical-path receipt.
--
-- This module consumes the strongest checked owners for the current
-- unification gap map.  It records the important correction from the latest
-- corpus review: the contraction/quadratic/signature spine is already
-- inhabited on the internal carrier, and YM/Hodge has a finite Route-B /
-- pure-zero current surface.  The remaining blockers are stricter:
-- real/authority metrology, strict selected YM variation pairing, empirical
-- authority, and continuum/terminal promotion.

data CriticalPathLayer : Set where
  formalQuadraticLayer :
    CriticalPathLayer

  hodgeYangMillsLayer :
    CriticalPathLayer

  standardModelHiggsLayer :
    CriticalPathLayer

  chemistryMetrologyLayer :
    CriticalPathLayer

  finiteQuantumScopeLayer :
    CriticalPathLayer

  downloadedCorpusLayer :
    CriticalPathLayer

  terminalPromotionLayer :
    CriticalPathLayer

data CriticalPathStatus : Set where
  internallyChecked :
    CriticalPathStatus

  finiteCheckedStrictPromotionBlocked :
    CriticalPathStatus

  executableAdapterCheckedAuthorityBlocked :
    CriticalPathStatus

  finiteComputationCheckedAuthorityBlocked :
    CriticalPathStatus

  scopedFiniteClosureChecked :
    CriticalPathStatus

  corpusIntakeCheckedNoAuthority :
    CriticalPathStatus

  terminalBlockedByLanePromotions :
    CriticalPathStatus

layerStatus : CriticalPathLayer → CriticalPathStatus
layerStatus formalQuadraticLayer =
  internallyChecked
layerStatus hodgeYangMillsLayer =
  finiteCheckedStrictPromotionBlocked
layerStatus standardModelHiggsLayer =
  executableAdapterCheckedAuthorityBlocked
layerStatus chemistryMetrologyLayer =
  finiteComputationCheckedAuthorityBlocked
layerStatus finiteQuantumScopeLayer =
  scopedFiniteClosureChecked
layerStatus downloadedCorpusLayer =
  corpusIntakeCheckedNoAuthority
layerStatus terminalPromotionLayer =
  terminalBlockedByLanePromotions

data CriticalPathBlocker : Set where
  noBlockerForInternalQuadraticSpine :
    CriticalPathBlocker

  missingStrictSelectedYMVariationPairing :
    CriticalPathBlocker

  missingAcceptedHiggsAuthorityAndHoldout :
    CriticalPathBlocker

  missingMeasuredSpectroscopyThermochemistryAuthority :
    CriticalPathBlocker

  noInfiniteQuantumOrQFTPromotion :
    CriticalPathBlocker

  downloadedArtifactsNotTheoremAuthority :
    CriticalPathBlocker

  terminalRequiresAllLanePromotionOrAuthority :
    CriticalPathBlocker

layerBlocker : CriticalPathLayer → CriticalPathBlocker
layerBlocker formalQuadraticLayer =
  noBlockerForInternalQuadraticSpine
layerBlocker hodgeYangMillsLayer =
  missingStrictSelectedYMVariationPairing
layerBlocker standardModelHiggsLayer =
  missingAcceptedHiggsAuthorityAndHoldout
layerBlocker chemistryMetrologyLayer =
  missingMeasuredSpectroscopyThermochemistryAuthority
layerBlocker finiteQuantumScopeLayer =
  noInfiniteQuantumOrQFTPromotion
layerBlocker downloadedCorpusLayer =
  downloadedArtifactsNotTheoremAuthority
layerBlocker terminalPromotionLayer =
  terminalRequiresAllLanePromotionOrAuthority

record CriticalPathRow : Set where
  field
    layer :
      CriticalPathLayer

    status :
      CriticalPathStatus

    statusMatchesLayer :
      status ≡ layerStatus layer

    primaryCheckedOwner :
      String

    strongestCheckedContent :
      String

    remainingGate :
      String

    blocker :
      CriticalPathBlocker

    blockerMatchesLayer :
      blocker ≡ layerBlocker layer

    promotesTerminal :
      Bool

    promotesTerminalIsFalse :
      promotesTerminal ≡ false

open CriticalPathRow public

mkCriticalPathRow :
  (layer : CriticalPathLayer) →
  String →
  String →
  String →
  CriticalPathRow
mkCriticalPathRow layer owner checked gate =
  record
    { layer = layer
    ; status = layerStatus layer
    ; statusMatchesLayer = refl
    ; primaryCheckedOwner = owner
    ; strongestCheckedContent = checked
    ; remainingGate = gate
    ; blocker = layerBlocker layer
    ; blockerMatchesLayer = refl
    ; promotesTerminal = false
    ; promotesTerminalIsFalse = refl
    }

formalQuadraticRow : CriticalPathRow
formalQuadraticRow =
  mkCriticalPathRow
    formalQuadraticLayer
    "DASHI.Physics.Closure.ContractionForcesQuadraticTheorem"
    "canonicalRealStackContractionForcesQuadraticTheorem and canonicalContractionQuadraticToSignatureBridgeTheorem are inhabited"
    "real-world physics/metrology consumers must still cite their own authority and validation gates"

hodgeYangMillsRow : CriticalPathRow
hodgeYangMillsRow =
  mkCriticalPathRow
    hodgeYangMillsLayer
    "DASHI.Physics.Closure.HodgeVariationPairingDepth9"
    "Route-B selected D * F = J and pure zero-current finite D * F = J are inhabited on the finite carrier"
    "missingVariationPairingForSelectedHodgeStar remains the strict selected YM variation blocker"

standardModelHiggsRow : CriticalPathRow
standardModelHiggsRow =
  mkCriticalPathRow
    standardModelHiggsLayer
    "DASHI.Promotion.StandardModelHiggsCovariantComparisonLaw"
    "four covariance-aware fixture-baseline Higgs comparison rows and the chi-square law are checked"
    "accepted SM baseline authority, raw provider vector binding, HEPData/ATLAS authority token, and holdout remain absent"

chemistryMetrologyRow : CriticalPathRow
chemistryMetrologyRow =
  mkCriticalPathRow
    chemistryMetrologyLayer
    "DASHI.Promotion.ChemistryFiniteComputationSurface and DASHI.Constants.Registry"
    "finite Aufbau/Pauli/Hund, Rydberg rational factors, Gibbs arithmetic, and exact known-input population are checked"
    "measured numeric payloads, spectroscopy authority, thermochemistry authority, bonding interpretation, physical chemistry, and wet-lab validation remain gated"

finiteQuantumScopeRow : CriticalPathRow
finiteQuantumScopeRow =
  mkCriticalPathRow
    finiteQuantumScopeLayer
    "DASHI.Promotion.FiniteQuantumQFTScopedClosure"
    "finite Schrodinger/Born adapter and finite-mode QFT scope are checked"
    "infinite Hilbert, Stone, spectral theorem, general Born, and QFT promotion remain false"

downloadedCorpusRow : CriticalPathRow
downloadedCorpusRow =
  mkCriticalPathRow
    downloadedCorpusLayer
    "DASHI.Promotion.DownloadedNewAdditionsReferenceIndex"
    "36 downloaded artifacts are checksum-routed into context families without theorem or empirical authority"
    "downloaded artifacts must be consumed by specific proof or authority receipts before promotion"

terminalPromotionRow : CriticalPathRow
terminalPromotionRow =
  mkCriticalPathRow
    terminalPromotionLayer
    "DASHI.Promotion.UnificationCriticalPathReceipt"
    "the current critical path is separated into internal, finite-adapter, authority, and terminal layers"
    "terminal promotion requires every lane to be internally proved or explicitly authority-scoped with compatible guards"

canonicalCriticalPathRows : List CriticalPathRow
canonicalCriticalPathRows =
  formalQuadraticRow
  ∷ hodgeYangMillsRow
  ∷ standardModelHiggsRow
  ∷ chemistryMetrologyRow
  ∷ finiteQuantumScopeRow
  ∷ downloadedCorpusRow
  ∷ terminalPromotionRow
  ∷ []

record UnificationCriticalPathReceipt : Setω where
  field
    formalQuadraticTheorem :
      CFQT.ContractionForcesQuadraticTheorem

    contractionQuadraticSignatureBridge :
      CQSB.ContractionQuadraticToSignatureBridgeTheorem

    defectQuadraticDependencyIndex :
      DefectIndex.DefectQuadraticClosureDependencyIndex

    hodgeVariationDepth9 :
      HV9.HodgeVariationPairingDepth9Receipt

    ymStrictHodgeVariationBlockerIndex :
      YMHodgeIndex.YMStrictHodgeVariationBlockerIndex

    exactHodgeVariationBlocker :
      YMObs.YangMillsVariationalEquationMissingPrimitive

    exactHodgeVariationBlockerIsSelectedPairing :
      exactHodgeVariationBlocker
      ≡
      YMObs.missingVariationPairingForSelectedHodgeStar

    higgsCovariantComparison :
      Higgs.StandardModelHiggsCovariantComparisonLaw

    chemistryFiniteComputation :
      Chemistry.ChemistryFiniteComputationSurface

    finiteQuantumScope :
      Quantum.FiniteQuantumQFTScopedClosure

    knownInputsPopulation :
      Registry.KnownInputsPopulationReceipt

    downloadedArtifactIndex :
      Downloaded.DownloadedNewAdditionsReferenceIndex

    criticalPathRows :
      List CriticalPathRow

    rowCount :
      Nat

    rowCountIs7 :
      rowCount ≡ 7

    internalQuadraticSpineChecked :
      Bool

    internalQuadraticSpineCheckedIsTrue :
      internalQuadraticSpineChecked ≡ true

    finiteHodgeCurrentChecked :
      Bool

    finiteHodgeCurrentCheckedIsTrue :
      finiteHodgeCurrentChecked ≡ true

    strictYMVariationPairingPromoted :
      Bool

    strictYMVariationPairingPromotedIsFalse :
      strictYMVariationPairingPromoted ≡ false

    higgsEmpiricalPromotion :
      Bool

    higgsEmpiricalPromotionIsFalse :
      higgsEmpiricalPromotion ≡ false

    physicalChemistryPromotion :
      Bool

    physicalChemistryPromotionIsFalse :
      physicalChemistryPromotion ≡ false

    qftPromotion :
      Bool

    qftPromotionIsFalse :
      qftPromotion ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    sprintDecision :
      List String

open UnificationCriticalPathReceipt public

canonicalUnificationCriticalPathReceipt :
  UnificationCriticalPathReceipt
canonicalUnificationCriticalPathReceipt =
  record
    { formalQuadraticTheorem =
        CFQT.canonicalRealStackContractionForcesQuadraticTheorem
    ; contractionQuadraticSignatureBridge =
        CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
    ; defectQuadraticDependencyIndex =
        DefectIndex.canonicalDefectQuadraticClosureDependencyIndex
    ; hodgeVariationDepth9 =
        HV9.canonicalHodgeVariationPairingDepth9Receipt
    ; ymStrictHodgeVariationBlockerIndex =
        YMHodgeIndex.canonicalYMStrictHodgeVariationBlockerIndex
    ; exactHodgeVariationBlocker =
        YMObs.missingVariationPairingForSelectedHodgeStar
    ; exactHodgeVariationBlockerIsSelectedPairing =
        refl
    ; higgsCovariantComparison =
        Higgs.canonicalStandardModelHiggsCovariantComparisonLaw
    ; chemistryFiniteComputation =
        Chemistry.canonicalChemistryFiniteComputationSurface
    ; finiteQuantumScope =
        Quantum.canonicalFiniteQuantumQFTScopedClosure
    ; knownInputsPopulation =
        Registry.canonicalKnownInputsPopulationReceipt
    ; downloadedArtifactIndex =
        Downloaded.canonicalDownloadedNewAdditionsReferenceIndex
    ; criticalPathRows =
        canonicalCriticalPathRows
    ; rowCount =
        7
    ; rowCountIs7 =
        refl
    ; internalQuadraticSpineChecked =
        true
    ; internalQuadraticSpineCheckedIsTrue =
        refl
    ; finiteHodgeCurrentChecked =
        true
    ; finiteHodgeCurrentCheckedIsTrue =
        refl
    ; strictYMVariationPairingPromoted =
        HV9.HodgeVariationPairingDepth9Receipt.variationPairingPromoted
          HV9.canonicalHodgeVariationPairingDepth9Receipt
    ; strictYMVariationPairingPromotedIsFalse =
        HV9.HodgeVariationPairingDepth9Receipt.variationPairingPromotedIsFalse
          HV9.canonicalHodgeVariationPairingDepth9Receipt
    ; higgsEmpiricalPromotion =
        Higgs.StandardModelHiggsCovariantComparisonLaw.empiricalValidationPromoted
          Higgs.canonicalStandardModelHiggsCovariantComparisonLaw
    ; higgsEmpiricalPromotionIsFalse =
        Higgs.StandardModelHiggsCovariantComparisonLaw.empiricalValidationPromotedIsFalse
          Higgs.canonicalStandardModelHiggsCovariantComparisonLaw
    ; physicalChemistryPromotion =
        Chemistry.ChemistryFiniteComputationSurface.physicalChemistryPromoted
          Chemistry.canonicalChemistryFiniteComputationSurface
    ; physicalChemistryPromotionIsFalse =
        Chemistry.ChemistryFiniteComputationSurface.physicalChemistryPromotedIsFalse
          Chemistry.canonicalChemistryFiniteComputationSurface
    ; qftPromotion =
        Quantum.FiniteQuantumQFTScopedClosure.qftPromoted
          Quantum.canonicalFiniteQuantumQFTScopedClosure
    ; qftPromotionIsFalse =
        Quantum.FiniteQuantumQFTScopedClosure.qftPromotedIsFalse
          Quantum.canonicalFiniteQuantumQFTScopedClosure
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; sprintDecision =
        "Do not spend another sprint rediscovering Hodge: finite Route-B and pure zero-current D * F = J are already checked"
        ∷ "The YM proof calculation is now the strict selected variation pairing over the user-supplied variation/action carriers"
        ∷ "Do not spend another sprint asking whether contraction gives a quadratic spine on the shift carrier: the internal theorem and dependency index are already inhabited"
        ∷ "The broader open theorem is strict contraction plus defect monotonicity plus admissibility quotient plus hierarchy consistency forcing the projection-defect/parallelogram package"
        ∷ "The next empirical calculation is authority replacement for the Higgs fixture baseline and raw HEPData vector binding"
        ∷ "Terminal unification remains false until lane promotions or authority boundaries compose without contradiction"
        ∷ []
    }

canonicalUnificationCriticalPathRowCountIs7 :
  rowCount canonicalUnificationCriticalPathReceipt ≡ 7
canonicalUnificationCriticalPathRowCountIs7 =
  refl

canonicalUnificationCriticalPathHodgeBlockerIsVariationPairing :
  exactHodgeVariationBlocker canonicalUnificationCriticalPathReceipt
  ≡
  YMObs.missingVariationPairingForSelectedHodgeStar
canonicalUnificationCriticalPathHodgeBlockerIsVariationPairing =
  refl

canonicalUnificationCriticalPathQuadraticSpineChecked :
  internalQuadraticSpineChecked canonicalUnificationCriticalPathReceipt
  ≡
  true
canonicalUnificationCriticalPathQuadraticSpineChecked =
  refl

canonicalUnificationCriticalPathFiniteHodgeCurrentChecked :
  finiteHodgeCurrentChecked canonicalUnificationCriticalPathReceipt
  ≡
  true
canonicalUnificationCriticalPathFiniteHodgeCurrentChecked =
  refl

canonicalUnificationCriticalPathTerminalPromotionFalse :
  terminalPromotion canonicalUnificationCriticalPathReceipt ≡ false
canonicalUnificationCriticalPathTerminalPromotionFalse =
  refl
