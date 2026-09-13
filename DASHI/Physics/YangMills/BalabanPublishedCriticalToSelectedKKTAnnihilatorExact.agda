{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPublishedCriticalToSelectedKKTAnnihilatorExact where

------------------------------------------------------------------------
-- PUBLISHED VARIATIONAL CRITICALITY -> SELECTED KKT ANNIHILATOR
--
-- The published Bałaban variational authority already owns a `Critical`
-- conclusion for the selected background.  The exact carrier-matching ABI
-- already permits the repository-side critical predicate to be chosen
-- independently, provided one proves the source/repository interpretation.
--
-- Specialize that repository predicate to the literal finite KKT condition
-- used by the selected-background Green algebra:
--
--   first variation annihilates every tangent in ker L.
--
-- The theorem below contains no fresh analytic estimate.  Once the exact
-- carrier match supplies
--
--   published Critical -> AnnihilatesConstraintKernel,
--
-- the published Theorem-1 criticality constructs the local KKT annihilator
-- witness directly.  All multiplier/pseudoinverse consequences are already
-- machine-checked downstream.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPublishedAnalyticAuthorities as Published
import DASHI.Physics.YangMills.BalabanExactPublishedCarrierMatching as Match
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanSelectedConstraintAnnihilatorKKTExact as Annihilator

record PublishedCriticalKKTInterpretation
    {Index Coarse Fluctuation Bound Multiplier : Set}
    (authority : Published.PublishedVariationalBackgroundAuthority
      Index Coarse Fluctuation Bound)
    (pseudoDataAt : Index -> Coarse -> Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (covectorAt : Index -> Coarse -> Fluctuation -> KKT.StateVector) : Set₁ where
  field
    publishedCriticalImpliesKKTAnnihilator :
      ∀ index coarse fluctuation →
      Published.Critical authority index coarse fluctuation →
      Annihilator.AnnihilatesConstraintKernel
        (pseudoDataAt index coarse)
        (covectorAt index coarse fluctuation)

open PublishedCriticalKKTInterpretation public

publishedBackgroundCriticalGivesKKTAnnihilator :
  ∀ {Index Coarse Fluctuation Bound Multiplier}
    (authority : Published.PublishedVariationalBackgroundAuthority
      Index Coarse Fluctuation Bound)
    (pseudoDataAt : Index -> Coarse -> Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (covectorAt : Index -> Coarse -> Fluctuation -> KKT.StateVector)
    (interpretation : PublishedCriticalKKTInterpretation
      authority pseudoDataAt covectorAt)
    index coarse →
    Published.AdmissibleCoarseField authority index coarse →
  Annihilator.AnnihilatesConstraintKernel
    (pseudoDataAt index coarse)
    (covectorAt index coarse
      (Published.backgroundFluctuation authority index coarse))
publishedBackgroundCriticalGivesKKTAnnihilator
    authority pseudoDataAt covectorAt interpretation index coarse admissible =
  publishedCriticalImpliesKKTAnnihilator interpretation
    index coarse (Published.backgroundFluctuation authority index coarse)
    (Published.theorem1BackgroundCritical authority index coarse admissible)

publishedBackgroundCriticalGivesKKTMultiplier :
  ∀ {Index Coarse Fluctuation Bound Multiplier}
    (authority : Published.PublishedVariationalBackgroundAuthority
      Index Coarse Fluctuation Bound)
    (pseudoDataAt : Index -> Coarse -> Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (covectorAt : Index -> Coarse -> Fluctuation -> KKT.StateVector)
    (interpretation : PublishedCriticalKKTInterpretation
      authority pseudoDataAt covectorAt)
    index coarse
    (admissible : Published.AdmissibleCoarseField authority index coarse) →
  Annihilator.KKTMultiplierWitness
    (pseudoDataAt index coarse)
    (covectorAt index coarse
      (Published.backgroundFluctuation authority index coarse))
publishedBackgroundCriticalGivesKKTMultiplier
    authority pseudoDataAt covectorAt interpretation index coarse admissible =
  Annihilator.selectedKKTMultiplierExistence
    (pseudoDataAt index coarse)
    (covectorAt index coarse
      (Published.backgroundFluctuation authority index coarse))
    (publishedBackgroundCriticalGivesKKTAnnihilator
      authority pseudoDataAt covectorAt interpretation index coarse admissible)

publishedVariationalCriticalStatementLevel : ProofLevel
publishedVariationalCriticalStatementLevel = Published.publishedVariationalBackgroundLevel

publishedCriticalToKKTCompilerLevel : ProofLevel
publishedCriticalToKKTCompilerLevel = machineChecked

-- This is the remaining same-object/source-semantics payment.  It must identify
-- the source paper's critical equation with the literal repository Wilson/KKT
-- first-variation annihilator condition; theorem-name matching is insufficient.
publishedCriticalKKTInterpretationLevel : ProofLevel
publishedCriticalKKTInterpretationLevel = conditional
