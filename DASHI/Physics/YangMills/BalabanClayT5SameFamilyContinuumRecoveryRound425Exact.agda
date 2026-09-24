{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SameFamilyContinuumRecoveryRound425Exact where

------------------------------------------------------------------------
-- ROUND425 / SAME-FAMILY CONTINUUM + OS RECOVERY OWNER
--
-- Full-Clay max-cut owner.
--
-- The physical expectation-convergence lane and the selected continuum/OS lane
-- historically carry separate presentations of the cutoff family and continuum
-- measure.  This record welds them once and then projects:
--
--   * P2-style selected expectation convergence on the SAME continuum target;
--   * reflected-Gram positivity on that SAME target;
--   * the selected OS axiom bundle on that SAME Schwinger family;
--   * one reconstructed theory produced from that SAME OS bundle.
--
-- It deliberately contains no finite-clustering/B hypothesis and no mass-gap
-- conclusion.  Hence it can be built in parallel with P1 and reused by the
-- eventual same-Hamiltonian, local-family and nontriviality lanes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Physical
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS
import DASHI.Physics.YangMills.BalabanClayT5SelectedContinuumOSExact as Selected

record SameFamilyContinuumCoreRecovery
    (Measure Observable Schwinger Scalar Reconstructed : Set) : Set₁ where
  field
    physicalGramDataCore :
      Physical.PhysicalMeasureToOSGramData Measure Observable Scalar

    selectedCore :
      Selected.SelectedFiniteToContinuumOSCore Measure Schwinger

    physicalMeasureSequenceAgreesCore :
      ∀ cutoff →
      Physical.measureSequence
        (Physical.convergenceData physicalGramDataCore) cutoff
      ≡
      Selected.finiteMeasuresCore selectedCore cutoff

    physicalContinuumMeasureAgreesCore :
      Physical.continuumMeasure
        (Physical.convergenceData physicalGramDataCore)
      ≡
      Selected.continuumMeasureCore selectedCore

    gramReflectionImpliesSelectedReflectionCore :
      OS.GramReflectionPositive
        (Physical.physicalMeasureTopologyControlsOSGram physicalGramDataCore)
        (Selected.continuumMeasureCore selectedCore) →
      Selected.ReflectionPositiveCore selectedCore
        (Selected.schwingerCore selectedCore
          (Selected.continuumMeasureCore selectedCore))

    reconstructFromSelectedOSCore :
      Selected.SelectedContinuumOSCoreAxioms selectedCore →
      Reconstructed

open SameFamilyContinuumCoreRecovery public

selectedPhysicalGramReflectionPositiveCore :
  ∀ {Measure Observable Schwinger Scalar Reconstructed}
    (recovery :
      SameFamilyContinuumCoreRecovery
        Measure Observable Schwinger Scalar Reconstructed) →
  OS.GramReflectionPositive
    (Physical.physicalMeasureTopologyControlsOSGram
      (physicalGramDataCore recovery))
    (Selected.continuumMeasureCore (selectedCore recovery))
selectedPhysicalGramReflectionPositiveCore recovery =
  subst
    (OS.GramReflectionPositive
      (Physical.physicalMeasureTopologyControlsOSGram
        (physicalGramDataCore recovery)))
    (physicalContinuumMeasureAgreesCore recovery)
    (Physical.physicalContinuumReflectionPositive
      (physicalGramDataCore recovery))

selectedPhysicalReflectionPositiveCore :
  ∀ {Measure Observable Schwinger Scalar Reconstructed}
    (recovery :
      SameFamilyContinuumCoreRecovery
        Measure Observable Schwinger Scalar Reconstructed) →
  Selected.ReflectionPositiveCore (selectedCore recovery)
    (Selected.schwingerCore (selectedCore recovery)
      (Selected.continuumMeasureCore (selectedCore recovery)))
selectedPhysicalReflectionPositiveCore recovery =
  gramReflectionImpliesSelectedReflectionCore recovery
    (selectedPhysicalGramReflectionPositiveCore recovery)

selectedOSCoreAxioms :
  ∀ {Measure Observable Schwinger Scalar Reconstructed}
    (recovery :
      SameFamilyContinuumCoreRecovery
        Measure Observable Schwinger Scalar Reconstructed) →
  Selected.SelectedContinuumOSCoreAxioms (selectedCore recovery)
selectedOSCoreAxioms recovery =
  Selected.assembleSelectedContinuumOSCoreAxioms (selectedCore recovery)

selectedCoreReconstructedTheory :
  ∀ {Measure Observable Schwinger Scalar Reconstructed}
    (recovery :
      SameFamilyContinuumCoreRecovery
        Measure Observable Schwinger Scalar Reconstructed) →
  Reconstructed
selectedCoreReconstructedTheory recovery =
  reconstructFromSelectedOSCore recovery (selectedOSCoreAxioms recovery)

boundedExpectationConvergesToSelectedCoreContinuum :
  ∀ {Measure Observable Schwinger Scalar Reconstructed}
    (recovery :
      SameFamilyContinuumCoreRecovery
        Measure Observable Schwinger Scalar Reconstructed)
    observable →
  Physical.BoundedObservable
    (Physical.convergenceData (physicalGramDataCore recovery)) observable →
  Physical.Converges
    (Physical.scalarConvergence
      (Physical.convergenceData (physicalGramDataCore recovery)))
    (λ cutoff →
      Physical.expectation
        (Physical.operations
          (Physical.convergenceData (physicalGramDataCore recovery)))
        (Physical.measureSequence
          (Physical.convergenceData (physicalGramDataCore recovery)) cutoff)
        observable)
    (Physical.expectation
      (Physical.operations
        (Physical.convergenceData (physicalGramDataCore recovery)))
      (Selected.continuumMeasureCore (selectedCore recovery))
      observable)
boundedExpectationConvergesToSelectedCoreContinuum recovery observable bounded =
  subst
    (λ target →
      Physical.Converges
        (Physical.scalarConvergence
          (Physical.convergenceData (physicalGramDataCore recovery)))
        (λ cutoff →
          Physical.expectation
            (Physical.operations
              (Physical.convergenceData (physicalGramDataCore recovery)))
            (Physical.measureSequence
              (Physical.convergenceData (physicalGramDataCore recovery)) cutoff)
            observable)
        (Physical.expectation
          (Physical.operations
            (Physical.convergenceData (physicalGramDataCore recovery)))
          target observable))
    (physicalContinuumMeasureAgreesCore recovery)
    (Physical.boundedWeakConvergenceImpliesExpectationConvergence
      (Physical.convergenceData (physicalGramDataCore recovery))
      observable bounded)

round425SameFamilyContinuumCoreRecoveryCompilerLevel : ProofLevel
round425SameFamilyContinuumCoreRecoveryCompilerLevel = machineChecked

-- The historical in-repo authority consumes the clustered OS package.
-- A weaker pre-gap reconstruction theorem must be bound explicitly before this
-- field can be promoted to standardImported.
round425CoreOSReconstructionAuthorityLevel : ProofLevel
round425CoreOSReconstructionAuthorityLevel = conditional

round425CoreRecoveryRequiresClustering : Bool
round425CoreRecoveryRequiresClustering = false

record SameFamilyContinuumRecovery
    (Measure Observable Schwinger Scalar Reconstructed : Set) : Set₁ where
  field
    physicalGramData :
      Physical.PhysicalMeasureToOSGramData Measure Observable Scalar

    selectedClosure :
      Selected.SelectedFiniteToContinuumOS Measure Schwinger

    -- SAME cutoff family and SAME continuum target.
    physicalMeasureSequenceAgrees :
      ∀ cutoff →
      Physical.measureSequence
        (Physical.convergenceData physicalGramData) cutoff
      ≡
      Selected.finiteMeasures selectedClosure cutoff

    physicalContinuumMeasureAgrees :
      Physical.continuumMeasure
        (Physical.convergenceData physicalGramData)
      ≡
      Selected.continuumMeasure selectedClosure

    -- Physical reflected-Gram positivity is interpreted as the OS reflection
    -- predicate of this exact selected Schwinger family.
    gramReflectionImpliesSelectedReflection :
      OS.GramReflectionPositive
        (Physical.physicalMeasureTopologyControlsOSGram physicalGramData)
        (Selected.continuumMeasure selectedClosure) →
      Selected.ReflectionPositive selectedClosure
        (Selected.schwinger selectedClosure
          (Selected.continuumMeasure selectedClosure))

    -- Standard reconstruction authority, specialized to THIS selected bundle.
    reconstructFromSelectedOSAxioms :
      Selected.SelectedContinuumOSAxioms selectedClosure →
      Reconstructed

open SameFamilyContinuumRecovery public

selectedPhysicalGramReflectionPositive :
  ∀ {Measure Observable Schwinger Scalar Reconstructed}
    (recovery :
      SameFamilyContinuumRecovery
        Measure Observable Schwinger Scalar Reconstructed) →
  OS.GramReflectionPositive
    (Physical.physicalMeasureTopologyControlsOSGram
      (physicalGramData recovery))
    (Selected.continuumMeasure (selectedClosure recovery))
selectedPhysicalGramReflectionPositive recovery =
  subst
    (OS.GramReflectionPositive
      (Physical.physicalMeasureTopologyControlsOSGram
        (physicalGramData recovery)))
    (physicalContinuumMeasureAgrees recovery)
    (Physical.physicalContinuumReflectionPositive
      (physicalGramData recovery))

selectedPhysicalReflectionPositive :
  ∀ {Measure Observable Schwinger Scalar Reconstructed}
    (recovery :
      SameFamilyContinuumRecovery
        Measure Observable Schwinger Scalar Reconstructed) →
  Selected.ReflectionPositive (selectedClosure recovery)
    (Selected.schwinger (selectedClosure recovery)
      (Selected.continuumMeasure (selectedClosure recovery)))
selectedPhysicalReflectionPositive recovery =
  gramReflectionImpliesSelectedReflection recovery
    (selectedPhysicalGramReflectionPositive recovery)

selectedOSAxioms :
  ∀ {Measure Observable Schwinger Scalar Reconstructed}
    (recovery :
      SameFamilyContinuumRecovery
        Measure Observable Schwinger Scalar Reconstructed) →
  Selected.SelectedContinuumOSAxioms (selectedClosure recovery)
selectedOSAxioms recovery =
  Selected.assembleSelectedContinuumOSAxioms (selectedClosure recovery)

selectedReconstructedTheory :
  ∀ {Measure Observable Schwinger Scalar Reconstructed}
    (recovery :
      SameFamilyContinuumRecovery
        Measure Observable Schwinger Scalar Reconstructed) →
  Reconstructed
selectedReconstructedTheory recovery =
  reconstructFromSelectedOSAxioms recovery (selectedOSAxioms recovery)

------------------------------------------------------------------------
-- P2 projection: bounded physical observables converge to expectations on the
-- SAME continuum measure carried by the selected OS closure.
--
-- We intentionally keep the cutoff sequence in its original physical
-- presentation.  Per-cutoff equality with Selected.finiteMeasures is recorded
-- above; no function extensionality is required merely to prove provenance.
------------------------------------------------------------------------

boundedExpectationConvergesToSelectedContinuum :
  ∀ {Measure Observable Schwinger Scalar Reconstructed}
    (recovery :
      SameFamilyContinuumRecovery
        Measure Observable Schwinger Scalar Reconstructed)
    observable →
  Physical.BoundedObservable
    (Physical.convergenceData (physicalGramData recovery)) observable →
  Physical.Converges
    (Physical.scalarConvergence
      (Physical.convergenceData (physicalGramData recovery)))
    (λ cutoff →
      Physical.expectation
        (Physical.operations
          (Physical.convergenceData (physicalGramData recovery)))
        (Physical.measureSequence
          (Physical.convergenceData (physicalGramData recovery)) cutoff)
        observable)
    (Physical.expectation
      (Physical.operations
        (Physical.convergenceData (physicalGramData recovery)))
      (Selected.continuumMeasure (selectedClosure recovery))
      observable)
boundedExpectationConvergesToSelectedContinuum recovery observable bounded =
  subst
    (λ target →
      Physical.Converges
        (Physical.scalarConvergence
          (Physical.convergenceData (physicalGramData recovery)))
        (λ cutoff →
          Physical.expectation
            (Physical.operations
              (Physical.convergenceData (physicalGramData recovery)))
            (Physical.measureSequence
              (Physical.convergenceData (physicalGramData recovery)) cutoff)
            observable)
        (Physical.expectation
          (Physical.operations
            (Physical.convergenceData (physicalGramData recovery)))
          target observable))
    (physicalContinuumMeasureAgrees recovery)
    (Physical.boundedWeakConvergenceImpliesExpectationConvergence
      (Physical.convergenceData (physicalGramData recovery))
      observable bounded)

round425SameFamilyContinuumRecoveryCompilerLevel : ProofLevel
round425SameFamilyContinuumRecoveryCompilerLevel = machineChecked

round425PhysicalMeasurePresentationAgreementLevel : ProofLevel
round425PhysicalMeasurePresentationAgreementLevel = conditional

round425GramToSelectedReflectionMeaningLevel : ProofLevel
round425GramToSelectedReflectionMeaningLevel = conditional

round425SelectedOSReconstructionAuthorityLevel : ProofLevel
round425SelectedOSReconstructionAuthorityLevel = standardImported

-- P2 no longer needs a separate continuum target once this owner is inhabited.
round425SeparateP2ContinuumMeasureRequired : Bool
round425SeparateP2ContinuumMeasureRequired = false

-- The reconstruction is definitionally produced from the same selected OS
-- object, so a later same-H proof need only identify the physical Hamiltonian
-- with this reconstructed theory's generator; it need not re-prove provenance.
round425IndependentOSFamilyForP3Required : Bool
round425IndependentOSFamilyForP3Required = false
