module DASHI.Physics.YangMills.BalabanClayLocalNoncollapseExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II", Communications in
-- Mathematical Physics 42 (1975), 281--305. DOI: 10.1007/BF01608978.
--
-- DASHI CONTRIBUTION
--
-- A positive gap for a reconstructed Hilbert space does not by itself prove
-- that the local gauge-invariant observable theory contains a non-vacuum
-- vector.  Local noncollapse is tracked separately: one explicit centered
-- local observable must have strictly positive OS norm.  The theorem below
-- turns that positive norm into a nonzero reconstructed vector without using
-- spectral-edge overlap.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

data Empty : Set where

record LocalNoncollapseData
    (Observable Vector NormSquared : Set) : Set₁ where
  field
    zeroVector : Vector
    reconstruct : Observable → Vector
    osNormSquared : Observable → NormSquared
    Positive : NormSquared → Set

    zeroVectorHasZeroNorm : ∀ observable →
      reconstruct observable ≡ zeroVector →
      Positive (osNormSquared observable) → Empty

open LocalNoncollapseData public

record LocalNoncollapseWitness
    {Observable Vector NormSquared : Set}
    (dataSet : LocalNoncollapseData Observable Vector NormSquared) : Set₁ where
  field
    observable : Observable
    positiveOSNorm : Positive dataSet (osNormSquared dataSet observable)

open LocalNoncollapseWitness public

localPositiveOSNormForcesNonzeroVector :
  ∀ {Observable Vector NormSquared}
    {dataSet : LocalNoncollapseData Observable Vector NormSquared} →
  (witness : LocalNoncollapseWitness dataSet) →
  reconstruct dataSet (observable witness) ≡ zeroVector dataSet → Empty
localPositiveOSNormForcesNonzeroVector {dataSet = dataSet} witness zero =
  zeroVectorHasZeroNorm dataSet (observable witness) zero
    (positiveOSNorm witness)

localNoncollapseLogicLevel : ProofLevel
localNoncollapseLogicLevel = machineChecked

physicalCurvatureObservableNormInputsLevel : ProofLevel
physicalCurvatureObservableNormInputsLevel = conditional
