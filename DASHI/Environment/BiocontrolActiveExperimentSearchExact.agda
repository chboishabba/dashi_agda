module DASHI.Environment.BiocontrolActiveExperimentSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AffectedDependencyClosureExact as Affected
import DASHI.Environment.BiocontrolExternalityExperimentExact as Experiment

------------------------------------------------------------------------
-- Ecological certificate dependency graph.
------------------------------------------------------------------------

data Artifact : Set where
  oxygenObservation : Artifact
  oxygenOutcomeCertificate : Artifact
  netOutcomeCertificate : Artifact
  hostSpecificityCertificate : Artifact


data Depends : Artifact → Artifact → Set where
  oxygenObservationAffectsOxygenOutcome :
    Depends oxygenObservation oxygenOutcomeCertificate
  oxygenOutcomeAffectsNetOutcome :
    Depends oxygenOutcomeCertificate netOutcomeCertificate

------------------------------------------------------------------------
-- Canonical reopening obligations.
------------------------------------------------------------------------

record OxygenReopeningReceipt : Set where
  constructor oxygenReopeningReceipt
  field
    obligation :
      Affected.ReopeningObligation
        Depends oxygenObservation oxygenOutcomeCertificate

canonicalOxygenReopening : OxygenReopeningReceipt
canonicalOxygenReopening = oxygenReopeningReceipt
  (Affected.oneEdgeCreatesReopeningObligation oxygenObservationAffectsOxygenOutcome)

record NetOutcomeReopeningReceipt : Set where
  constructor netOutcomeReopeningReceipt
  field
    obligation :
      Affected.ReopeningObligation
        Depends oxygenObservation netOutcomeCertificate

canonicalNetOutcomeReopening : NetOutcomeReopeningReceipt
canonicalNetOutcomeReopening = netOutcomeReopeningReceipt
  (Affected.obligationsCompose
    (Affected.oneEdgeCreatesReopeningObligation oxygenObservationAffectsOxygenOutcome)
    (Affected.oneEdgeCreatesReopeningObligation oxygenOutcomeAffectsNetOutcome))

------------------------------------------------------------------------
-- Host-specificity is deliberately outside the oxygen reverse dependency
-- closure.  This is represented constructively by the absence of an edge/path
-- constructor into that artifact in the declared dependency language.
------------------------------------------------------------------------

record HostSpecificityUnaffectedReceipt : Set where
  constructor hostSpecificityUnaffectedReceipt
  field
    noDirectOxygenDependency : Depends oxygenObservation hostSpecificityCertificate → ⊥
    noOxygenOutcomeDependency : Depends oxygenOutcomeCertificate hostSpecificityCertificate → ⊥

canonicalHostSpecificityUnaffected : HostSpecificityUnaffectedReceipt
canonicalHostSpecificityUnaffected = hostSpecificityUnaffectedReceipt (λ ()) (λ ())

------------------------------------------------------------------------
-- Active ecological experiment-search weld.
------------------------------------------------------------------------

record BiocontrolActiveExperimentSearch : Set₁ where
  constructor biocontrolActiveExperimentSearch
  field
    oxygenCollision : Experiment.OxygenCollisionReceipt
    oxygenDiscriminator : Experiment.OxygenDiscriminatorReceipt
    restorationCollision : Experiment.RestorationCollisionReceipt
    restorationDiscriminator : Experiment.RestorationDiscriminatorReceipt
    oxygenReopening : OxygenReopeningReceipt
    netOutcomeReopening : NetOutcomeReopeningReceipt
    hostSpecificityUnaffected : HostSpecificityUnaffectedReceipt
    searchReference : String

canonicalBiocontrolActiveExperimentSearch : BiocontrolActiveExperimentSearch
canonicalBiocontrolActiveExperimentSearch = biocontrolActiveExperimentSearch
  Experiment.canonicalOxygenCollision
  Experiment.canonicalOxygenDiscriminator
  Experiment.canonicalRestorationCollision
  Experiment.canonicalRestorationDiscriminator
  canonicalOxygenReopening
  canonicalNetOutcomeReopening
  canonicalHostSpecificityUnaffected
  "consumer collision -> minimal separating ecological discriminator -> fibre refinement -> selective reopening of only affected outcome certificates"

record BiocontrolActiveSearchBoundary : Set where
  constructor biocontrolActiveSearchBoundary
  field
    everyEcologicalObservationReopensEveryCertificate : Bool
    everyEcologicalObservationReopensEveryCertificateIsFalse :
      everyEcologicalObservationReopensEveryCertificate ≡ false
    completeHiddenEcosystemStateRequiredBeforeConsumerClosure : Bool
    completeHiddenEcosystemStateRequiredBeforeConsumerClosureIsFalse :
      completeHiddenEcosystemStateRequiredBeforeConsumerClosure ≡ false
    hostSpecificityAutomaticallyPaidByOxygenObservation : Bool
    hostSpecificityAutomaticallyPaidByOxygenObservationIsFalse :
      hostSpecificityAutomaticallyPaidByOxygenObservation ≡ false

canonicalBiocontrolActiveSearchBoundary : BiocontrolActiveSearchBoundary
canonicalBiocontrolActiveSearchBoundary =
  biocontrolActiveSearchBoundary false refl false refl false refl
