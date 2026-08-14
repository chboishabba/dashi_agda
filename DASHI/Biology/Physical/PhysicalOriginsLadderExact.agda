module DASHI.Biology.Physical.PhysicalOriginsLadderExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jeremy L. England,
-- "Statistical physics of self-replication", The Journal of Chemical Physics
-- 139 (2013), 121923. DOI: 10.1063/1.4818538.
--
-- Sumantra Sarkar and Jeremy L. England,
-- "Design of conditions for self-replication", Physical Review E 100 (2019),
-- 022414. DOI: 10.1103/PhysRevE.100.022414.
--
-- The cited papers motivate thermodynamic/kinetic treatment of replication.
-- This finite module does not claim to formalize England's continuous
-- stochastic heat bound.  It formalizes the DASHI distinction between driven
-- persistence, templated amplification, compartmentalization, and closed-loop
-- corrective agency.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.AgenticMaterialsControlCore as Agentic

record CapabilitySignature : Set where
  constructor capabilitySignature
  field
    energyGradient : Bool
    selfAmplification : Bool
    compartmentBoundary : Bool
    observationChannel : Bool
    targetDefect : Bool
    correctiveFeedback : Bool

open CapabilitySignature public

capabilities : Agentic.OriginStage → CapabilitySignature
capabilities Agentic.geochemicalGradient =
  capabilitySignature true false false false false false
capabilities Agentic.autocatalyticNetwork =
  capabilitySignature true true false false false false
capabilities Agentic.compartmentalisedMetabolism =
  capabilitySignature true true true false false false
capabilities Agentic.closedLoopProtoAgency =
  capabilitySignature true true true true true true
capabilities Agentic.multiscaleBiologicalAgency =
  capabilitySignature true true true true true true

replicationAppearsBeforeAgency :
  selfAmplification (capabilities Agentic.autocatalyticNetwork) ≡ true
replicationAppearsBeforeAgency = refl

autocatalysisLacksCorrectiveTarget :
  correctiveFeedback (capabilities Agentic.autocatalyticNetwork) ≡ false
autocatalysisLacksCorrectiveTarget = refl

compartmentStillLacksCorrectiveTarget :
  correctiveFeedback (capabilities Agentic.compartmentalisedMetabolism) ≡ false
compartmentStillLacksCorrectiveTarget = refl

protoAgencyHasCorrectiveTarget :
  correctiveFeedback (capabilities Agentic.closedLoopProtoAgency) ≡ true
protoAgencyHasCorrectiveTarget = refl

------------------------------------------------------------------------
-- Concrete finite self-amplification regression.
------------------------------------------------------------------------

replicatePopulation : Nat → Nat
replicatePopulation n = n + n

replicateOnceFromOne : replicatePopulation 1 ≡ 2
replicateOnceFromOne = refl

replicateTwiceFromOne : replicatePopulation (replicatePopulation 1) ≡ 4
replicateTwiceFromOne = refl

replicateThriceFromOne :
  replicatePopulation (replicatePopulation (replicatePopulation 1)) ≡ 8
replicateThriceFromOne = refl

------------------------------------------------------------------------
-- Concrete closed-loop corrective dynamics.  Replication and correction are
-- mathematically independent operators here.
------------------------------------------------------------------------

data ViabilityState : Set where
  damaged target : ViabilityState

correctiveStep : ViabilityState → ViabilityState
correctiveStep damaged = target
correctiveStep target = target

targetFixed : correctiveStep target ≡ target
targetFixed = refl

damageCorrected : correctiveStep damaged ≡ target
damageCorrected = refl

record PhysicalOriginSeparation : Set where
  field
    replicationWithoutCorrectionExists :
      selfAmplification (capabilities Agentic.autocatalyticNetwork) ≡ true
    replicationDoesNotSupplyCorrection :
      correctiveFeedback (capabilities Agentic.autocatalyticNetwork) ≡ false
    correctiveProtoAgencyExists :
      correctiveFeedback (capabilities Agentic.closedLoopProtoAgency) ≡ true
    correctiveTargetIsFixed : correctiveStep target ≡ target
    damagedStateIsRepaired : correctiveStep damaged ≡ target

canonicalPhysicalOriginSeparation : PhysicalOriginSeparation
canonicalPhysicalOriginSeparation = record
  { replicationWithoutCorrectionExists = refl
  ; replicationDoesNotSupplyCorrection = refl
  ; correctiveProtoAgencyExists = refl
  ; correctiveTargetIsFixed = refl
  ; damagedStateIsRepaired = refl
  }
