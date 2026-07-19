module DASHI.Physics.QuantumVacuum.FullDASHIFormalism where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ObservableContactGeometry as Contact
import DASHI.Physics.QuantumVacuum.ExtractionPhysicsSurface as Surface
import DASHI.Physics.QuantumVacuum.EvidenceReceipts as Receipts
import DASHI.Physics.QuantumVacuum.SourceTraceability as Source

------------------------------------------------------------------------
-- Domain × formal role × evidence -> typed term.
--
-- This is the physics-facing specialization of the broad DASHI grammar.  A
-- mechanism, equation, measurement, residual or obstruction is never stored
-- as an untyped assertion: it carries its role and evidence status.
------------------------------------------------------------------------

data QuantumVacuumDomain : Set where
  electromagneticVacuum : QuantumVacuumDomain
  cavityElectrodynamics  : QuantumVacuumDomain
  circuitNoise           : QuantumVacuumDomain
  materialResponse       : QuantumVacuumDomain
  reservoirThermodynamics : QuantumVacuumDomain

data FormalRole : Set where
  carrierSpace proofState operator observable spectrumTool boundaryGate
    obstruction algebra proofObligation decomposition hamiltonian metric
    projection residual receipt functor transition invariant symmetry mode
    source sink flow constraint remedy conjecture : FormalRole

data EvidenceStatus : Set where
  candidateOnly sourceBound measured controlled replicated cycleClosed
    blocked : EvidenceStatus

record TypedTerm : Set where
  constructor typedTerm
  field
    domain    : QuantumVacuumDomain
    role      : FormalRole
    mechanism : Surface.Mechanism
    evidence  : EvidenceStatus
    source    : Source.SourceReceipt

------------------------------------------------------------------------
-- Claim-stage separation.
------------------------------------------------------------------------

data ClaimStage : Set where
  proposedMechanism      : ClaimStage
  observableEffectStage  : ClaimStage
  controlledAnomalyStage : ClaimStage
  sourceDiscriminationStage : ClaimStage
  resetClosureStage      : ClaimStage
  continuousPowerStage   : ClaimStage

record StageTransition (from to : ClaimStage) : Set where
  constructor stageTransition
  field
    receipt : Set

-- There is deliberately no constructor from an observed effect directly to
-- continuous power.  The missing intermediate receipts remain visible.

record FullPromotionClosure (c : Surface.ExtractionClaim) : Set where
  constructor fullPromotionClosure
  field
    typedEvidence : Receipts.TypedPromotionWitness c
    sourceDiscrimination : Set
    cycleAccounting      : Set
    reservoirClosure     : Set

fullClosurePromotes :
  (c : Surface.ExtractionClaim) → FullPromotionClosure c →
  Surface.promotable? c ≡ true
fullClosurePromotes c closure =
  Receipts.typedPromotionImpliesPromotable c
    (FullPromotionClosure.typedEvidence closure)

------------------------------------------------------------------------
-- Observable-contact specialization.
------------------------------------------------------------------------

record VacuumExperimentGeometry : Set₁ where
  constructor vacuumExperimentGeometry
  field
    HiddenCarrier : Set
    Measurement   : Set
    ExperimentalTrace : Set
    Evidence      : Set
    projectCarrier : HiddenCarrier → Measurement
    projectTrace   : ExperimentalTrace → Measurement
    Fibre          : Measurement → Set
    Residual       : Measurement → Measurement → Set
    ComparisonLaw  : Measurement → Measurement → Set
    restricts      : Evidence → Measurement → Set
    Transition     : ExperimentalTrace → ExperimentalTrace → Set
    ContactReceipt : Set

asObservableContactGeometry :
  VacuumExperimentGeometry → Contact.ObservableContactGeometry
asObservableContactGeometry g =
  Contact.observableContactGeometry
    (VacuumExperimentGeometry.HiddenCarrier g)
    (VacuumExperimentGeometry.Measurement g)
    (VacuumExperimentGeometry.ExperimentalTrace g)
    (VacuumExperimentGeometry.Evidence g)
    (VacuumExperimentGeometry.projectCarrier g)
    (VacuumExperimentGeometry.Fibre g)
    (VacuumExperimentGeometry.projectTrace g)
    (VacuumExperimentGeometry.Residual g)
    (VacuumExperimentGeometry.ComparisonLaw g)
    (VacuumExperimentGeometry.restricts g)
    true
    false
    (VacuumExperimentGeometry.Transition g)
    (VacuumExperimentGeometry.ContactReceipt g)

contactDoesNotPromoteTruth :
  (g : VacuumExperimentGeometry) →
  Contact.fibreRestrictionPromotesTruth
    (asObservableContactGeometry g) ≡ false
contactDoesNotPromoteTruth g = refl
