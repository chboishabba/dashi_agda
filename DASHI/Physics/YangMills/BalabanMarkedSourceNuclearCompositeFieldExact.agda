module DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact where

------------------------------------------------------------------------
-- ROUND85: MARKED SOURCE DERIVATIVE + ONE HILBERT MODULUS -> NUCLEAR FIELD
--
-- PRIMARY SOURCES / CALIBRATION
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
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- MATHEMATICAL ROLE
--
-- Round84 correctly refused to identify a bounded finite-scale composite mark
-- with a continuum local field.  However, once the SAME completed composite
-- projection supplies a linear source derivative with ONE Hilbertian continuity
-- modulus, the remaining passage to a nuclear-continuous distribution is not a
-- new Yang--Mills estimate: it is topology transport.
--
-- This file makes that compiler explicit.  The physical L4 seam is thereby
-- sharpened to the concrete data that must really come from L2/the RG limit:
--
--   1. the literal composite source derivative is linear in the test function;
--   2. it is the derivative of the SAME completed composite projection;
--   3. it obeys one cutoff-independent Hilbertian continuity modulus;
--   4. the declared nuclear test topology refines that Hilbertian topology.
--
-- Given those data, nuclear continuity and same-family provenance are theorem
-- outputs.  No independent "complete a distribution" receipt remains.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact as Nuclear

record SameFamilyMarkedSourceData
    (C : Nuclear.ContinuityScale)
    (CompletedState Composite : Set) : Set₁ where
  field
    completedState : CompletedState
    compositeProjection : CompletedState → Composite
    sourceDerivative : Composite → Nuclear.Test C → Nuclear.Value C

    Linear : (Nuclear.Test C → Nuclear.Value C) → Set

    nuclearNear hilbertNear : Nuclear.NearFamily C

    nuclearTopologyStronger :
      Nuclear.StrongerNear C nuclearNear hilbertNear

    literalCompositeDerivativeLinear :
      Linear (sourceDerivative (compositeProjection completedState))

    commonHilbertianCompositeModulus :
      Nuclear.ContinuousAtZeroWith C hilbertNear
        (sourceDerivative (compositeProjection completedState))

open SameFamilyMarkedSourceData public

record SameFamilyNuclearCompositeField
    {C : Nuclear.ContinuityScale}
    {CompletedState Composite : Set}
    (dataSet : SameFamilyMarkedSourceData C CompletedState Composite) : Set₁ where
  field
    continuumComposite : Composite
    fieldFunctional : Nuclear.Test C → Nuclear.Value C

    continuumCompositeIsSameProjection :
      continuumComposite ≡ compositeProjection dataSet (completedState dataSet)

    fieldFunctionalIsLiteralSourceDerivative :
      fieldFunctional ≡ sourceDerivative dataSet continuumComposite

    fieldLinear : Linear dataSet fieldFunctional

    fieldNuclearContinuous :
      Nuclear.ContinuousAtZeroWith C
        (nuclearNear dataSet)
        fieldFunctional

open SameFamilyNuclearCompositeField public

sameFamilyMarkedSourceGivesNuclearCompositeField :
  ∀ {C CompletedState Composite}
    (dataSet : SameFamilyMarkedSourceData C CompletedState Composite) →
  SameFamilyNuclearCompositeField dataSet
sameFamilyMarkedSourceGivesNuclearCompositeField dataSet = record
  { continuumComposite = compositeProjection dataSet (completedState dataSet)
  ; fieldFunctional =
      sourceDerivative dataSet (compositeProjection dataSet (completedState dataSet))
  ; continuumCompositeIsSameProjection = refl
  ; fieldFunctionalIsLiteralSourceDerivative = refl
  ; fieldLinear = literalCompositeDerivativeLinear dataSet
  ; fieldNuclearContinuous =
      Nuclear.continuityMovesUpAlongStrongerDomainTopology C
        (nuclearNear dataSet)
        (hilbertNear dataSet)
        (sourceDerivative dataSet
          (compositeProjection dataSet (completedState dataSet)))
        (nuclearTopologyStronger dataSet)
        (commonHilbertianCompositeModulus dataSet)
  }

markedSourceToNuclearCompositeFieldCompilerLevel : ProofLevel
markedSourceToNuclearCompositeFieldCompilerLevel = machineChecked

-- This is now the genuine fusion target for Round84 L2 -> L4.  If the physical
-- marked-coordinate/radius theorem is strengthened to provide the four fields of
-- `SameFamilyMarkedSourceData` on the completed RG state, L4 becomes downstream
-- and the strict hard-analytic count may legitimately fall 6 -> 5.
physicalMarkedSourceSameFamilyHilbertModulusLevel : ProofLevel
physicalMarkedSourceSameFamilyHilbertModulusLevel = conditional
