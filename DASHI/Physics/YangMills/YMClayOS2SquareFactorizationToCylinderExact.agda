{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayOS2SquareFactorizationToCylinderExact where

------------------------------------------------------------------------
-- SOURCE / STATUS
--
-- Generic finite square-factorization -> cylinder OS2 input compiler built
-- from DASHI/Physics/YangMills/FiniteReflectionPositivity.agda:29-102 and
-- DASHI/Physics/YangMills/YangMillsCylinderLimitOSReflectionPositiveExact.agda:48-68,246-254.
-- Roadmap context: Docs/roadmaps/ClayYMBSDRHOriginalMaxCutImplementation20261117.md:94.
-- This is only the finite algebra.  It does not construct the physical Wilson
-- square factorization, prove D2/E1, or promote any Clay endpoint.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _≤ℝ_; ≤ℝ-refl; +-mono-≤; +-identityˡ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2

realSumTerms : ∀ {Index : Set} → List Index → (Index → ℝ) → ℝ
realSumTerms [] term = 0ℝ
realSumTerms (index ∷ indices) term = term index +ℝ realSumTerms indices term

realSumTermsNonnegative :
  ∀ {Index : Set} (indices : List Index) (term : Index → ℝ) →
  (∀ index → 0ℝ ≤ℝ term index) →
  0ℝ ≤ℝ realSumTerms indices term
realSumTermsNonnegative [] term termNonnegative = ≤ℝ-refl
realSumTermsNonnegative (index ∷ indices) term termNonnegative =
  subst
    (λ lower → lower ≤ℝ term index +ℝ realSumTerms indices term)
    (+-identityˡ 0ℝ)
    (+-mono-≤
      (termNonnegative index)
      (realSumTermsNonnegative indices term termNonnegative))

record CylinderSquareFactorizationInputs
    {Observable Index : Set}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (cylinder :
      Cylinder.ScalarCylinderExpectationLimitData
        Observable ℝ
        (RealLimit.canonicalCylinderAlgebra limitLaws))
    (observableAlgebra : OS2.CylinderOSAlgebra Observable) : Set₁ where
  field
    indices : ∀ cutoff (family : Gram.PhysicalOSFiniteTestFamily Observable ℝ) →
      List Index
    squareTerm :
      ∀ cutoff (family : Gram.PhysicalOSFiniteTestFamily Observable ℝ) →
      Index → ℝ
    squareTermNonnegative :
      ∀ cutoff (family : Gram.PhysicalOSFiniteTestFamily Observable ℝ) index →
      0ℝ ≤ℝ squareTerm cutoff family index
    factorization :
      ∀ cutoff (family : Gram.PhysicalOSFiniteTestFamily Observable ℝ) →
      Gram.physicalReflectedGramQuadraticForm
        (OS2.operations observableAlgebra)
        (λ observable → Cylinder.finiteExpectation cylinder cutoff observable)
        family
      ≡ realSumTerms
          (indices cutoff family)
          (squareTerm cutoff family)

open CylinderSquareFactorizationInputs public

asCylinderOSInputs :
  ∀ {Observable Index sequenceLimit limitLaws cylinder observableAlgebra} →
  (inputs :
    CylinderSquareFactorizationInputs
      {Observable} {Index} {sequenceLimit}
      limitLaws cylinder observableAlgebra) →
  OS2.CylinderLimitOSInputs limitLaws cylinder observableAlgebra
asCylinderOSInputs inputs = record
  { OS2.CylinderLimitOSInputs.finiteReflectionPositive =
      λ cutoff family →
        subst
          (λ lower → 0ℝ ≤ℝ lower)
          (sym (factorization inputs cutoff family))
          (realSumTermsNonnegative
            (indices inputs cutoff family)
            (squareTerm inputs cutoff family)
            (squareTermNonnegative inputs cutoff family))
  }

continuumOS2FromSquareFactorization :
  ∀ {Observable Index sequenceLimit limitLaws cylinder observableAlgebra} →
  (inputs :
    CylinderSquareFactorizationInputs
      {Observable} {Index} {sequenceLimit}
      limitLaws cylinder observableAlgebra) →
  OS2.continuumReflectionPositive (asCylinderOSInputs inputs)
    ≡ OS2.continuumReflectionPositive (asCylinderOSInputs inputs)
continuumOS2FromSquareFactorization inputs = refl

squareFactorizationToOS2CompilerLevel : ProofLevel
squareFactorizationToOS2CompilerLevel = machineChecked
