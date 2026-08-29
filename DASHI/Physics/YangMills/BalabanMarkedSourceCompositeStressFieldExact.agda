module DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact where

------------------------------------------------------------------------
-- ROUND87: ONE COMPLETED MARKED RG STATE -> COMPOSITE + STRESS NUCLEAR FIELDS
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang-Mills Theory", official Clay Mathematics Institute problem
-- description, in The Millennium Prize Problems.  No DOI assigned.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Julien Fageot, Arash Amini and Michael Unser,
-- "On the Continuity of Characteristic Functionals and Sparse Stochastic
-- Modeling", Journal of Fourier Analysis and Applications 20 (2014),
-- 1179--1211. DOI: 10.1007/s00041-014-9351-4.
--
-- Jose Velhinho,
-- "Topics of Measure Theory on Infinite Dimensional Spaces", 2023.
-- DOI: 10.48550/arXiv.2312.04365.
--
-- MATHEMATICAL ROLE
--
-- Round85 proved that ONE same-family marked source derivative with a uniform
-- Hilbertian test-function modulus automatically gives a nuclear-continuous
-- continuum field.  The Clay problem requires both curvature/composite local
-- fields and a stress tensor.  There is no reason to run two unrelated
-- completion arguments if both insertions are coordinates of the SAME completed
-- differentiated RG state.
--
-- This module compiles two marked coordinates -- a composite coordinate and a
-- stress coordinate -- through the existing Round85 theorem and explicitly
-- retains equality of their completed-state provenance.
--
-- Thus the remaining physical theorem is not "construct a continuum stress
-- distribution by a separate method".  It is: prove that the same differentiated
-- physical RG state supplies the stress insertion with the same kind of linear
-- source derivative and cutoff-independent Hilbert modulus already required for
-- composite insertions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact as Nuclear
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked

record SameCompletedCompositeStressMarkedSource
    (C : Nuclear.ContinuityScale)
    (CompletedState Composite Stress : Set) : Set₁ where
  field
    compositeData : Marked.SameFamilyMarkedSourceData C CompletedState Composite
    stressData : Marked.SameFamilyMarkedSourceData C CompletedState Stress

    sameCompletedState :
      Marked.completedState compositeData ≡ Marked.completedState stressData

open SameCompletedCompositeStressMarkedSource public

record SameFamilyCompositeStressNuclearFields
    {C : Nuclear.ContinuityScale}
    {CompletedState Composite Stress : Set}
    (dataSet : SameCompletedCompositeStressMarkedSource
      C CompletedState Composite Stress) : Set₁ where
  field
    compositeField :
      Marked.SameFamilyNuclearCompositeField (compositeData dataSet)
    stressField :
      Marked.SameFamilyNuclearCompositeField (stressData dataSet)
    completedStateAgreement :
      Marked.completedState (compositeData dataSet)
      ≡ Marked.completedState (stressData dataSet)

open SameFamilyCompositeStressNuclearFields public

sameCompletedMarkedSourcesGiveCompositeAndStressFields :
  ∀ {C CompletedState Composite Stress}
    (dataSet : SameCompletedCompositeStressMarkedSource
      C CompletedState Composite Stress) →
  SameFamilyCompositeStressNuclearFields dataSet
sameCompletedMarkedSourcesGiveCompositeAndStressFields dataSet = record
  { compositeField =
      Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
        (compositeData dataSet)
  ; stressField =
      Marked.sameFamilyMarkedSourceGivesNuclearCompositeField
        (stressData dataSet)
  ; completedStateAgreement = sameCompletedState dataSet
  }

sameCompletedCompositeStressFieldCompilerLevel : ProofLevel
sameCompletedCompositeStressFieldCompilerLevel = machineChecked

-- Physical input still required: the literal differentiated Yang--Mills RG state
-- must actually provide BOTH marked source data sets, in particular a uniform
-- Hilbertian modulus for the stress insertion.  No such estimate is fabricated
-- here.
physicalStressMarkedSourceHilbertModulusLevel : ProofLevel
physicalStressMarkedSourceHilbertModulusLevel = conditional
