module DASHI.Physics.QuantumVacuum.CasimirU1ModeRenormalizedStressAttachmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as QFT
import DASHI.Physics.QuantumVacuum.ZeroPointModeHyperfabricExact as ZPE
import DASHI.Physics.QuantumVacuum.CasimirModeHyperfabricBridgeExact as Mode
import DASHI.Physics.QuantumVacuum.CasimirU1RecoveredQFTStressAttachmentExact as Selected
import DASHI.Physics.QuantumVacuum.CasimirU1ActionVariationMaxCutExact as Action
import DASHI.Physics.QuantumVacuum.CasimirU1SelectedStressReadoutAttachmentExact as StressReadout

------------------------------------------------------------------------
-- MAXWELL STRESS READOUT -> EXISTING CASIMIR MODE/RENORMALISATION OBJECT
--
-- CasimirModeHyperfabricWeld already owns the same-field/different-boundary
-- retopology, regulator, scheme, reference, separation, area, analytic kernel,
-- and same-observable evidence connecting the renormalized vacuum difference
-- to Casimir energy/pressure.  The U(1) lane must reuse that exact object rather
-- than introduce a second plate boundary or renormalization prescription.
--
-- The remaining payment is one same-object stress map: identify the Maxwell
-- metric-variation readout with the stress assigned to THAT renormalized mode
-- observable.  Once attached, boundary and renormalization identity are
-- inherited from the existing mode weld.
------------------------------------------------------------------------

record MaxwellModeRenormalizedStressAttachment
    {S : ZPE.ScalarSpectrum}
    (free cavity : ZPE.FiniteVacuumHyperfabric S)
    {U : Weld.UnifiedCandidate}
    {selected : Selected.CasimirU1RecoveredQFTStressAttachment U}
    {variation : Action.CasimirRestrictedMetricVariationPayment}
    (stressAttachment :
      StressReadout.SelectedQFTMetricVariationReadoutAttachment
        U selected variation) : Set₁ where
  field
    modeWeld : Mode.CasimirModeHyperfabricWeld free cavity

    modeObservableToSelectedQFTStress :
      Mode.Observable (Mode.difference modeWeld) →
      QFT.StressTensor (Weld.qftCarriers U)

    maxwellReadoutIsStressOfSameRenormalizedObservable :
      StressReadout.maxwellStressReadoutInSelectedQFTCarrier stressAttachment
      ≡
      modeObservableToSelectedQFTStress
        (Mode.observable (Mode.difference modeWeld))

    reading : String

open MaxwellModeRenormalizedStressAttachment public

selectedRestrictedStressIsStressOfSameRenormalizedObservable :
  ∀ {S : ZPE.ScalarSpectrum}
    {free cavity : ZPE.FiniteVacuumHyperfabric S}
    {U : Weld.UnifiedCandidate}
    {selected : Selected.CasimirU1RecoveredQFTStressAttachment U}
    {variation : Action.CasimirRestrictedMetricVariationPayment}
    {stressAttachment :
      StressReadout.SelectedQFTMetricVariationReadoutAttachment
        U selected variation} →
  (attachment :
    MaxwellModeRenormalizedStressAttachment
      free cavity stressAttachment) →
  Selected.u1RestrictedSelectedQFTStress selected
  ≡
  modeObservableToSelectedQFTStress attachment
    (Mode.observable (Mode.difference (modeWeld attachment)))
selectedRestrictedStressIsStressOfSameRenormalizedObservable
    {stressAttachment = stressAttachment} attachment =
  trans
    (StressReadout.selectedRestrictedQFTStressEqualsMaxwellReadout
      stressAttachment)
    (maxwellReadoutIsStressOfSameRenormalizedObservable attachment)

modeRenormalizationScheme :
  ∀ {S : ZPE.ScalarSpectrum}
    {free cavity : ZPE.FiniteVacuumHyperfabric S}
    {U : Weld.UnifiedCandidate}
    {selected : Selected.CasimirU1RecoveredQFTStressAttachment U}
    {variation : Action.CasimirRestrictedMetricVariationPayment}
    {stressAttachment :
      StressReadout.SelectedQFTMetricVariationReadoutAttachment
        U selected variation} →
  (attachment : MaxwellModeRenormalizedStressAttachment free cavity stressAttachment) →
  Mode.Scheme (Mode.difference (modeWeld attachment))
modeRenormalizationScheme attachment =
  Mode.scheme (Mode.difference (modeWeld attachment))

modeRenormalizationRegulator :
  ∀ {S : ZPE.ScalarSpectrum}
    {free cavity : ZPE.FiniteVacuumHyperfabric S}
    {U : Weld.UnifiedCandidate}
    {selected : Selected.CasimirU1RecoveredQFTStressAttachment U}
    {variation : Action.CasimirRestrictedMetricVariationPayment}
    {stressAttachment :
      StressReadout.SelectedQFTMetricVariationReadoutAttachment
        U selected variation} →
  (attachment : MaxwellModeRenormalizedStressAttachment free cavity stressAttachment) →
  Mode.Regulator (Mode.difference (modeWeld attachment))
modeRenormalizationRegulator attachment =
  Mode.regulator (Mode.difference (modeWeld attachment))

modeRenormalizationReference :
  ∀ {S : ZPE.ScalarSpectrum}
    {free cavity : ZPE.FiniteVacuumHyperfabric S}
    {U : Weld.UnifiedCandidate}
    {selected : Selected.CasimirU1RecoveredQFTStressAttachment U}
    {variation : Action.CasimirRestrictedMetricVariationPayment}
    {stressAttachment :
      StressReadout.SelectedQFTMetricVariationReadoutAttachment
        U selected variation} →
  (attachment : MaxwellModeRenormalizedStressAttachment free cavity stressAttachment) →
  Mode.Reference (Mode.difference (modeWeld attachment))
modeRenormalizationReference attachment =
  Mode.reference (Mode.difference (modeWeld attachment))

data StressOfSameRenormalizedObservableAutomaticallyPaysExperimentalGravity : Set where

modeStressDoesNotPayExperimentalGravity :
  StressOfSameRenormalizedObservableAutomaticallyPaysExperimentalGravity → ⊥
modeStressDoesNotPayExperimentalGravity ()

record CasimirU1ModeRenormalizedStressBoundary : Set where
  constructor casimir-u1-mode-renormalized-stress-boundary
  field
    existingCasimirModeHyperfabricWeldReused : Bool
    secondRenormalizationSchemeRequired : Bool
    secondConductingPlateBoundaryObjectRequired : Bool
    maxwellReadoutToModeObservableStressAttachmentRequired : Bool
    directGravityMeasurementPromoted : Bool

open CasimirU1ModeRenormalizedStressBoundary public

canonicalModeRenormalizedStressBoundary : CasimirU1ModeRenormalizedStressBoundary
canonicalModeRenormalizedStressBoundary =
  casimir-u1-mode-renormalized-stress-boundary true false false true false

casimirU1ModeRenormalizedStressReading : String
casimirU1ModeRenormalizedStressReading =
  "The canonical Casimir mode-hyperfabric weld already owns the boundary retopology and the regulator/scheme/reference defining the renormalized vacuum-difference observable, together with its same-observable energy/pressure weld. The U(1) stress lane therefore needs no second boundary object or renormalization prescription. Its remaining payment is a same-object map from the Maxwell metric-variation stress readout to the stress of that exact renormalized mode observable. This still does not imply measured gravitational backreaction."
