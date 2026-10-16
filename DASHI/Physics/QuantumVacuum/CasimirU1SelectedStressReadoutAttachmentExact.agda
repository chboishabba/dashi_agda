module DASHI.Physics.QuantumVacuum.CasimirU1SelectedStressReadoutAttachmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.BalabanRound131RecoveredQFTTransportCompilerExact as R131Transport
import DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact as R129
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.QuantumVacuum.CasimirU1RecoveredQFTStressAttachmentExact as Selected
import DASHI.Physics.QuantumVacuum.CasimirU1ActionVariationMaxCutExact as Action
import DASHI.Physics.QuantumVacuum.CasimirU1MetricVariationTransportExact as MetricTransport

------------------------------------------------------------------------
-- SELECTED RECOVERED-QFT STRESS <-> COMMON METRIC-VARIATION READOUT
--
-- R129 already exports the literal stress derivative of the SAME source-native
-- Yang--Mills construction, and the Round131 recovered-QFT transport compiler
-- transports that literal construction to the selected qftTarget.  The Casimir
-- lane therefore must not ask for a second abstract "quantum stress = Maxwell
-- stress" theorem.
--
-- What remains is one same-object attachment: identify the already-selected
-- U(1)-restricted QFT stress with the common metric-variation stress readout.
-- Once attached, the action/variation compiler transports it to the Maxwell
-- readout automatically.
------------------------------------------------------------------------

record SelectedQFTMetricVariationReadoutAttachment
    (U : Weld.UnifiedCandidate)
    (selected : Selected.CasimirU1RecoveredQFTStressAttachment U)
    (variation : Action.CasimirRestrictedMetricVariationPayment) : Set₁ where
  field
    background :
      MetricTransport.MetricConfiguration
        (Action.metricActionFamily variation)

    perturbation :
      MetricTransport.MetricPerturbation
        (Action.metricActionFamily variation)

    readoutToSelectedQFTStress :
      MetricTransport.StressCarrier
        (Action.commonStressReadout variation) →
      QFT.StressTensor (Weld.qftCarriers U)

    selectedRestrictedStressIsMetricVariationReadout :
      Selected.u1RestrictedSelectedQFTStress selected
      ≡
      readoutToSelectedQFTStress
        (MetricTransport.stressFromFirstVariation
          (Action.commonStressReadout variation)
          (MetricTransport.restrictedYMMetricFirstVariation
            (Action.derivativeLaws variation)
            (Action.metricActionFamily variation)
            background perturbation))

    reading : String

open SelectedQFTMetricVariationReadoutAttachment public

maxwellStressReadoutInSelectedQFTCarrier :
  ∀ {U : Weld.UnifiedCandidate}
    {selected : Selected.CasimirU1RecoveredQFTStressAttachment U}
    {variation : Action.CasimirRestrictedMetricVariationPayment} →
  SelectedQFTMetricVariationReadoutAttachment U selected variation →
  QFT.StressTensor (Weld.qftCarriers U)
maxwellStressReadoutInSelectedQFTCarrier
    {variation = variation} attachment =
  readoutToSelectedQFTStress attachment
    (MetricTransport.stressFromFirstVariation
      (Action.commonStressReadout variation)
      (MetricTransport.maxwellMetricFirstVariation
        (Action.derivativeLaws variation)
        (Action.metricActionFamily variation)
        (background attachment)
        (perturbation attachment)))

selectedRestrictedQFTStressEqualsMaxwellReadout :
  ∀ {U : Weld.UnifiedCandidate}
    {selected : Selected.CasimirU1RecoveredQFTStressAttachment U}
    {variation : Action.CasimirRestrictedMetricVariationPayment} →
  (attachment :
    SelectedQFTMetricVariationReadoutAttachment U selected variation) →
  Selected.u1RestrictedSelectedQFTStress selected
  ≡ maxwellStressReadoutInSelectedQFTCarrier attachment
selectedRestrictedQFTStressEqualsMaxwellReadout
    {variation = variation} attachment =
  trans
    (selectedRestrictedStressIsMetricVariationReadout attachment)
    (cong (readoutToSelectedQFTStress attachment)
      (Action.restrictedVariationCommonStressEqualsMaxwell
        variation
        (background attachment)
        (perturbation attachment)))

------------------------------------------------------------------------
-- Route/status.
------------------------------------------------------------------------

round129LiteralStressDerivativeOwner : String
round129LiteralStressDerivativeOwner =
  "DASHI.Physics.YangMills.BalabanSectorQFTRecoveryExportRound129Exact"

round131RecoveredQFTTransportOwner : String
round131RecoveredQFTTransportOwner =
  "DASHI.Physics.Foundations.BalabanRound131RecoveredQFTTransportCompilerExact"

data SelectedStressReadoutAttachmentAutomaticallySuppliesBrownMaclayBoundaryRenormalization : Set where

stressReadoutDoesNotSupplyBoundaryRenormalization :
  SelectedStressReadoutAttachmentAutomaticallySuppliesBrownMaclayBoundaryRenormalization → ⊥
stressReadoutDoesNotSupplyBoundaryRenormalization ()

record CasimirSelectedStressReadoutBoundary : Set where
  constructor casimir-selected-stress-readout-boundary
  field
    round129LiteralStressDerivativeExporterReused : Bool
    round131RecoveredQFTTransportCompilerReused : Bool
    selectedStressToMaxwellReadoutEqualityCompilerOwned : Bool
    independentRestrictedQuantumStressMaxwellEqualityRequiredAfterAttachment : Bool
    selectedQFTStressMetricVariationReadoutAttachmentRequired : Bool
    samePlateBoundaryAndRenormalizationStillRequired : Bool

open CasimirSelectedStressReadoutBoundary public

canonicalSelectedStressReadoutBoundary : CasimirSelectedStressReadoutBoundary
canonicalSelectedStressReadoutBoundary =
  casimir-selected-stress-readout-boundary true true true false true true

casimirSelectedStressReadoutReading : String
casimirSelectedStressReadoutReading =
  "The source-native YM stack already exports the literal QFT stress derivative (R129) and transports recovered literal constructions into the selected qftTarget/common-metric lane (Round131). Casimir therefore needs one same-object attachment from its U(1)-restricted selected QFT stress to the common metric-variation readout. Once that attachment is supplied, the same-path action/variation compiler proves equality with the Maxwell stress readout; no second independent restricted-quantum-stress=Maxwell theorem remains. Conducting-plate boundary and renormalization identification remain separate."
