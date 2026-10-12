{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityVacuumExperimentDiscriminatorExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

import DASHI.Core.DiscriminatorSynthesisExact as Disc
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalSourceSectorActionExact as Canonical
import DASHI.Physics.Foundations.CMP119AntigravityVacuumSequenceNonidentifiabilityExact as NI
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as T4

------------------------------------------------------------------------
-- VACUUM NON-IDENTIFIABILITY -> EXPERIMENT-LANGUAGE EXTENSION
--
-- The non-identifiability owner constructs two normalized CMP119 source worlds
-- which agree definitionally on the current coupling / density / background /
-- fluctuation / E / R / B view but differ in projected vacuum amplitude.
--
-- DiscriminatorSynthesisExact already gives the generic theorem-shape for this
-- situation.  Here we instantiate it literally:
--
--   current source view            collapses the two worlds;
--   projected vacuum readout       separates them;
--   joined observation language    therefore separates them.
--
-- This is an information/experiment-design theorem.  It does NOT assert that a
-- laboratory already has a calibrated physical observable equal to the formal
-- plaquette projector.  That same-object calibration remains a physical leaf.
------------------------------------------------------------------------

record CurrentSourceViewAtScale
    (Density Background Fluctuation : Set) : Set where
  constructor current-source-view-at-scale
  field
    coupling : ℚ
    density : Density
    background : Background
    fluctuation : Fluctuation
    eSector rSector bSector : T4.LocalizedAction

open CurrentSourceViewAtScale public

currentSourceViewAtScale :
  ∀ {Density Background Fluctuation} →
  Canonical.CMP119NormalizedSectorSource Density Background Fluctuation →
  Nat →
  CurrentSourceViewAtScale Density Background Fluctuation
currentSourceViewAtScale source scale =
  current-source-view-at-scale
    (Canonical.couplingAt source scale)
    (Canonical.densityAt source scale)
    (Canonical.backgroundAt source scale)
    (Canonical.fluctuationAt source scale)
    (Canonical.eAt source scale)
    (Canonical.rAt source scale)
    (Canonical.bAt source scale)

canonicalVacuumObserverCollision :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource
      Density Background Fluctuation)
    (scale : Nat) →
  Disc.CurrentObserverCollision
    (λ candidate → currentSourceViewAtScale candidate scale)
canonicalVacuumObserverCollision source scale =
  Disc.currentObserverCollision
    (NI.zeroVacuumSource source)
    (NI.unitVacuumSource source)
    refl

vacuumReadoutBundleAtScale :
  ∀ {Density Background Fluctuation} →
  Nat →
  Disc.ExperimentBundle
    (Canonical.CMP119NormalizedSectorSource
      Density Background Fluctuation)
vacuumReadoutBundleAtScale scale =
  Disc.experimentBundle
    ℚ
    (λ source → NI.projectedVacuum source scale)
    1
    "CMP119 literal projected-vacuum coordinate at one selected scale"
    "formal plaquette-projector readout only; physical same-object calibration required"

vacuumReadoutSeparatesCanonicalCollision :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource
      Density Background Fluctuation)
    (scale : Nat) →
  Disc.BundleSeparates
    (vacuumReadoutBundleAtScale scale)
    (NI.zeroVacuumSource source)
    (NI.unitVacuumSource source)
vacuumReadoutSeparatesCanonicalCollision source scale =
  Disc.bundleSeparates (NI.projectedVacuumSequencesDiffer source scale)

canonicalVacuumDiscriminatingExtension :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource
      Density Background Fluctuation)
    (scale : Nat) →
  Disc.DiscriminatingLanguageExtension
    (λ candidate → currentSourceViewAtScale candidate scale)
canonicalVacuumDiscriminatingExtension source scale =
  Disc.discriminatingLanguageExtension
    (canonicalVacuumObserverCollision source scale)
    (vacuumReadoutBundleAtScale scale)
    (vacuumReadoutSeparatesCanonicalCollision source scale)

joinedCurrentViewAndVacuumReadoutSeparates :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource
      Density Background Fluctuation)
    (scale : Nat) →
  Disc.joinedObservation
    (λ candidate → currentSourceViewAtScale candidate scale)
    (vacuumReadoutBundleAtScale scale)
    (NI.zeroVacuumSource source)
  ≡ Disc.joinedObservation
      (λ candidate → currentSourceViewAtScale candidate scale)
      (vacuumReadoutBundleAtScale scale)
      (NI.unitVacuumSource source) → ⊥
joinedCurrentViewAndVacuumReadoutSeparates source scale =
  Disc.extensionJoinSeparates
    (canonicalVacuumDiscriminatingExtension source scale)

------------------------------------------------------------------------
-- Stronger consumer statement: there is no decoder from ONLY the current
-- source view that recovers the projected vacuum coordinate for every source.
------------------------------------------------------------------------

currentSourceViewCannotCloseVacuumConsumer :
  ∀ {Density Background Fluctuation}
    (source : Canonical.CMP119NormalizedSectorSource
      Density Background Fluctuation)
    (scale : Nat)
    (decoder : CurrentSourceViewAtScale Density Background Fluctuation → ℚ) →
    ((candidate : Canonical.CMP119NormalizedSectorSource
        Density Background Fluctuation) →
      decoder (currentSourceViewAtScale candidate scale)
        ≡ NI.projectedVacuum candidate scale) →
    ⊥
currentSourceViewCannotCloseVacuumConsumer source scale decoder reconstructs =
  NI.projectedVacuumSequencesDiffer source scale
    (trans
      (sym (reconstructs (NI.zeroVacuumSource source)))
      (trans
        (cong decoder
          (Disc.collapsed (canonicalVacuumObserverCollision source scale)))
        (reconstructs (NI.unitVacuumSource source))))

record VacuumExperimentDiscriminatorBoundary : Set where
  constructor vacuum-experiment-discriminator-boundary
  field
    currentSourceViewHasExplicitVacuumCollision : Bool
    formalVacuumReadoutSeparatesThatCollision : Bool
    currentSourceViewAloneCannotRecoverVacuumConsumer : Bool
    physicalVacuumMeasurementStillRequiresCalibration : Bool
    experimentalBundleAutomaticallyProvesPhysicalVacuumObservable : Bool

canonicalVacuumExperimentDiscriminatorBoundary :
  VacuumExperimentDiscriminatorBoundary
canonicalVacuumExperimentDiscriminatorBoundary =
  vacuum-experiment-discriminator-boundary
    true true true true true

-- The final flag above means the QUESTION remains live; keep the explicit
-- promotion firewall below as the authoritative polarity used by schedulers.
physicalVacuumMeasurementStillRequiresCalibration : Bool
physicalVacuumMeasurementStillRequiresCalibration = true

formalBundleIsAlreadyPhysicalMeasurement : Bool
formalBundleIsAlreadyPhysicalMeasurement = false
