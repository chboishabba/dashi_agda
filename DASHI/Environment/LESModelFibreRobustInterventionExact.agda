module DASHI.Environment.LESModelFibreRobustInterventionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.RobustInterventionAcrossHypothesesExact as Robust
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis

------------------------------------------------------------------------
-- PURPOSE
--
-- Turn the Stage-6 compatible-state fibre into the live hypothesis family for
-- intervention choice.  A control can be decision-safe even before complete
-- identification when it is no worse than the declared baseline for every
-- state still compatible with the evidence.  A new measurement may then refine
-- the fibre and unlock actions previously blocked by model conflict.
--
-- Decision preference/utility remains application supplied; no ecological
-- welfare ordering or authority is invented here.
------------------------------------------------------------------------

record LESInterventionConsumer
    (mechanism : Basis.DomainMechanismSocket) : Set₁ where
  constructor lesInterventionConsumer
  field
    baselineControl : Basis.Control mechanism
    NoWorse : Basis.Observation mechanism → Basis.Observation mechanism → Set
    StrictlyBetter : Basis.Observation mechanism → Basis.Observation mechanism → Set
    consumerReference : String
    baselineReference : String
    preferenceOrConstraintReference : String

open LESInterventionConsumer public

lesHypothesisInterventionSystem :
  ∀ {mechanism} →
  LESInterventionConsumer mechanism →
  Robust.HypothesisInterventionSystem
    (Basis.State mechanism)
    (Basis.Control mechanism)
    (Basis.Observation mechanism)
lesHypothesisInterventionSystem {mechanism} consumer =
  Robust.hypothesisInterventionSystem
    (baselineControl consumer)
    (λ state control →
      Basis.observe mechanism (Basis.evolve mechanism control state))
    (NoWorse consumer)
    (StrictlyBetter consumer)

LESRobustAtEvidence :
  ∀ {mechanism Evidence}
    (consumer : LESInterventionConsumer mechanism)
    (compatible : Envelope.Compatible Evidence (Basis.State mechanism)) →
  Evidence → Basis.Control mechanism → Set₁
LESRobustAtEvidence consumer compatible evidence control =
  Robust.RobustlyNoWorseThanBaseline
    (lesHypothesisInterventionSystem consumer)
    (compatible evidence)
    control

LESDominatesAtEvidence :
  ∀ {mechanism Evidence}
    (consumer : LESInterventionConsumer mechanism)
    (compatible : Envelope.Compatible Evidence (Basis.State mechanism)) →
  Evidence → Basis.Control mechanism → Set₁
LESDominatesAtEvidence consumer compatible evidence control =
  Robust.RobustlyDominatesBaseline
    (lesHypothesisInterventionSystem consumer)
    (compatible evidence)
    control

------------------------------------------------------------------------
-- More evidence narrows the compatible-state fibre.  A control already robust
-- on the weaker evidence remains robust after refinement.
------------------------------------------------------------------------

robustControlSurvivesEvidenceRefinement :
  ∀ {mechanism Evidence}
    {consumer : LESInterventionConsumer mechanism}
    {compatible : Envelope.Compatible Evidence (Basis.State mechanism)}
    {stronger weaker : Evidence}
    {control : Basis.Control mechanism} →
  Envelope.EvidenceRefines compatible stronger weaker →
  LESRobustAtEvidence consumer compatible weaker control →
  LESRobustAtEvidence consumer compatible stronger control
robustControlSurvivesEvidenceRefinement refines robust =
  Robust.robustnessSurvivesHypothesisRefinement refines robust

------------------------------------------------------------------------
-- Measurement refinement gives the exact Before -> After relation consumed by
-- InformationUnlocksIntervention.
------------------------------------------------------------------------

measuredFibreRefinesPrior :
  ∀ {mechanism Evidence Measurement}
    {compatible : Envelope.Compatible Evidence (Basis.State mechanism)}
    {measure : Basis.State mechanism → Measurement}
    {evidence : Evidence} {measurement : Measurement} →
  Robust.DeclaredRefines
    (Envelope.MeasuredCompatible compatible measure (evidence , measurement))
    (compatible evidence)
measuredFibreRefinesPrior state measured = proj₁ measured

measurementUnlocksControl :
  ∀ {mechanism Evidence Measurement}
    {consumer : LESInterventionConsumer mechanism}
    {compatible : Envelope.Compatible Evidence (Basis.State mechanism)}
    {measure : Basis.State mechanism → Measurement}
    {evidence : Evidence} {measurement : Measurement}
    {control : Basis.Control mechanism} →
  Robust.HypothesisActionConflict
    (lesHypothesisInterventionSystem consumer)
    (compatible evidence) →
  Robust.RobustlyNoWorseThanBaseline
    (lesHypothesisInterventionSystem consumer)
    (Envelope.MeasuredCompatible compatible measure (evidence , measurement))
    control →
  String → String →
  Robust.InformationUnlocksIntervention
    (lesHypothesisInterventionSystem consumer)
    control
measurementUnlocksControl conflict robustAfter informationRef interventionRef =
  Robust.informationUnlocksIntervention
    _ _
    measuredFibreRefinesPrior
    conflict
    robustAfter
    informationRef
    interventionRef

record LESModelFibreInterventionBoundary : Set where
  constructor lesModelFibreInterventionBoundary
  field
    fullPointIdentificationRequiredBeforeEveryControl : Bool
    fullPointIdentificationRequiredBeforeEveryControlIsFalse :
      fullPointIdentificationRequiredBeforeEveryControl ≡ false
    robustAcrossCompatibleStatesCanPrecedeIdentification : Bool
    robustAcrossCompatibleStatesCanPrecedeIdentificationIsTrue :
      robustAcrossCompatibleStatesCanPrecedeIdentification ≡ true
    moreEvidenceCanPreserveAlreadyRobustControl : Bool
    moreEvidenceCanPreserveAlreadyRobustControlIsTrue :
      moreEvidenceCanPreserveAlreadyRobustControl ≡ true
    measurementCanUnlockControlByRemovingConflictingHypotheses : Bool
    measurementCanUnlockControlByRemovingConflictingHypothesesIsTrue :
      measurementCanUnlockControlByRemovingConflictingHypotheses ≡ true
    robustControlEqualsDeploymentAuthority : Bool
    robustControlEqualsDeploymentAuthorityIsFalse :
      robustControlEqualsDeploymentAuthority ≡ false

canonicalLESModelFibreInterventionBoundary : LESModelFibreInterventionBoundary
canonicalLESModelFibreInterventionBoundary =
  lesModelFibreInterventionBoundary false refl true refl true refl true refl false refl
