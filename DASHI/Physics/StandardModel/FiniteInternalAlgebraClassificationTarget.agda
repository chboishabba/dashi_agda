module DASHI.Physics.StandardModel.FiniteInternalAlgebraClassificationTarget where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.StandardModel.FiniteRealStarAlgebraCandidates

------------------------------------------------------------------------
-- Mathematical theorem interface for the missing Standard-Model gate.
--
-- A future instance must supply actual finite spectral data and prove that
-- every competing finite real *-algebra satisfying the same C1-C5 obligations
-- is equal to the C + H + M3(C) spine.  No instance is provided here.
------------------------------------------------------------------------

record FiniteSpectralData (A : FiniteRealStarAlgebra) : Setω where
  field
    FiniteHilbertCarrier : Set
    InternalDiracCarrier : Set
    RealStructureCarrier : Set
    GradingCarrier : Set

open FiniteSpectralData public

record C1C5Admissible
  (A : FiniteRealStarAlgebra)
  (D : FiniteSpectralData A) : Setω where
  field
    realityLaw : Set
    gradingLaw : Set
    firstOrderLaw : Set
    commutantLaw : Set
    anomalyFreedomLaw : Set
    minimalityLaw : Set

open C1C5Admissible public

record FiniteInternalAlgebraClassification : Setω where
  field
    standardModelData : FiniteSpectralData standardModelSpine
    standardModelAdmissible :
      C1C5Admissible standardModelSpine standardModelData

    uniqueUnderC1C5 :
      (A : FiniteRealStarAlgebra) →
      (D : FiniteSpectralData A) →
      C1C5Admissible A D →
      A ≡ standardModelSpine

open FiniteInternalAlgebraClassification public

classificationReturnsStandardModelSpine :
  (classification : FiniteInternalAlgebraClassification) →
  (A : FiniteRealStarAlgebra) →
  (D : FiniteSpectralData A) →
  C1C5Admissible A D →
  A ≡ standardModelSpine
classificationReturnsStandardModelSpine classification =
  uniqueUnderC1C5 classification
