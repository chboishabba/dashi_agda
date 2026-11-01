module DASHI.Cognition.EndogenousPhospheneObservationBridge where

------------------------------------------------------------------------
-- Closed-eye / reduced-input visual observation bridge.
--
-- The claim represented here is intentionally modest: attenuation of external
-- visual drive does not imply an inactive carrier, so endogenous activity may
-- still project observable geometry.  No particular cause is inferred from a
-- reported phosphene or form constant.

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Biology.CoupledElectrochemicalPatternCarrier using
  ( CoupledElectrochemicalCarrier
  ; PatternSelectionInput
  )
open import DASHI.Cognition.KlueverFormConstantProjection using
  ( KlueverForm )
open import DASHI.Cognition.CorticalLogPolarProjectionGeometry using
  ( CorticalProjectionGeometry
  ; CorticalModeProjection
  )

------------------------------------------------------------------------

data VisualInputCondition : Set where
  ordinaryExternalDrive : VisualInputCondition
  attenuatedExternalDrive : VisualInputCondition
  eyesClosedCondition : VisualInputCondition
  mechanicallyPerturbedCondition : VisualInputCondition

record EndogenousVisualObservation : Set₁ where
  constructor endogenousVisualObservation
  field
    carrier : CoupledElectrochemicalCarrier
    selectionInput : PatternSelectionInput
    projectionGeometry : CorticalProjectionGeometry
    inputCondition : VisualInputCondition
    observedForm : KlueverForm

    externalConstraintReduced : Set
    endogenousCarrierRemainsActive : Set
    internallySelectedModeAvailable : Set
    projectionAvailable : Set

record PhospheneProjectionWitness : Set₁ where
  constructor phospheneProjectionWitness
  field
    observation : EndogenousVisualObservation
    corticalProjection : CorticalModeProjection

    formAgreement :
      CorticalModeProjection.observedForm corticalProjection
        ≡
      EndogenousVisualObservation.observedForm observation

    observationIsRealContact : Set
    observationIsLossy : Set
    noUniqueEtiologyRecovery : Set
    noClinicalDiagnosis : Set
    noSemanticAuthority : Set
