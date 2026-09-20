{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact where

------------------------------------------------------------------------
-- ONE REAL LIMIT OBJECT FOR CYLINDER A AND T5/OS GRAM CONVERGENCE
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram

record CanonicalRealLimitLaws
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError) : Set₁ where
  field
    constantLimit :
      ∀ value →
      Seq.limit sequenceLimit (λ _ → value) ≡ value

    addLimit :
      ∀ left right →
      Seq.limit sequenceLimit
        (λ n → left n +ℝ right n)
      ≡
      Seq.limit sequenceLimit left
        +ℝ Seq.limit sequenceLimit right

    multiplyConstantLimit :
      ∀ scalar sequence →
      Seq.limit sequenceLimit
        (λ n → scalar *ℝ sequence n)
      ≡
      scalar *ℝ Seq.limit sequenceLimit sequence

    nonnegativeLimitClosed :
      ∀ sequence →
      (∀ n → 0ℝ ≤ℝ sequence n) →
      0ℝ ≤ℝ Seq.limit sequenceLimit sequence

open CanonicalRealLimitLaws public

Converges :
  Seq.RealSequenceLimitByVanishingError →
  (Nat → ℝ) → ℝ → Set
Converges sequenceLimit sequence target =
  Seq.limit sequenceLimit sequence ≡ target

cong₂ :
  ∀ {A B C : Set} {a a' : A} {b b' : B}
    (f : A → B → C) →
  a ≡ a' → b ≡ b' → f a b ≡ f a' b'
cong₂ f refl refl = refl

canonicalCylinderAlgebra :
  ∀ {sequenceLimit} →
  CanonicalRealLimitLaws sequenceLimit →
  Cylinder.ScalarCylinderLimitAlgebra ℝ
canonicalCylinderAlgebra
    {sequenceLimit = sequenceLimit} laws = record
  { Cylinder.ScalarCylinderLimitAlgebra.zero = 0ℝ
  ; Cylinder.ScalarCylinderLimitAlgebra.one = 1ℝ
  ; Cylinder.ScalarCylinderLimitAlgebra.add = _+ℝ_
  ; Cylinder.ScalarCylinderLimitAlgebra.multiply = _*ℝ_
  ; Cylinder.ScalarCylinderLimitAlgebra.LessEqual = _≤ℝ_
  ; Cylinder.ScalarCylinderLimitAlgebra.Converges =
      Converges sequenceLimit
  ; Cylinder.ScalarCylinderLimitAlgebra.convergenceUnique =
      λ sequence left right leftConv rightConv →
        trans (sym leftConv) rightConv
  ; Cylinder.ScalarCylinderLimitAlgebra.convergencePointwiseCongruent =
      λ left right target pointwise rightConv →
        trans
          (Seq.limitCongruent sequenceLimit left right pointwise)
          rightConv
  ; Cylinder.ScalarCylinderLimitAlgebra.constantConverges =
      constantLimit laws
  ; Cylinder.ScalarCylinderLimitAlgebra.addConverges =
      λ left right leftLimit rightLimit leftConv rightConv →
        trans
          (addLimit laws left right)
          (cong₂ _+ℝ_ leftConv rightConv)
  ; Cylinder.ScalarCylinderLimitAlgebra.multiplyConstantConverges =
      λ scalar sequence target converges →
        trans
          (multiplyConstantLimit laws scalar sequence)
          (cong (λ value → scalar *ℝ value) converges)
  ; Cylinder.ScalarCylinderLimitAlgebra.nonnegativeClosedUnderLimit =
      λ sequence target converges pointwise →
        substRight
          (nonnegativeLimitClosed laws sequence pointwise)
          converges
  }
  where
  substRight :
    ∀ {left right : ℝ} →
    0ℝ ≤ℝ left → left ≡ right → 0ℝ ≤ℝ right
  substRight proof refl = proof

canonicalGramScalarConvergence :
  ∀ {sequenceLimit} →
  CanonicalRealLimitLaws sequenceLimit →
  Gram.ScalarConvergenceAlgebra ℝ 0ℝ _+ℝ_ _*ℝ_
canonicalGramScalarConvergence
    {sequenceLimit = sequenceLimit} laws = record
  { Gram.ScalarConvergenceAlgebra.Converges =
      Converges sequenceLimit
  ; Gram.ScalarConvergenceAlgebra.constantConverges =
      constantLimit laws
  ; Gram.ScalarConvergenceAlgebra.addConverges =
      λ firstSequence firstLimit secondSequence secondLimit
         firstConv secondConv →
        trans
          (addLimit laws firstSequence secondSequence)
          (cong₂ _+ℝ_ firstConv secondConv)
  ; Gram.ScalarConvergenceAlgebra.multiplyConstantConverges =
      λ coefficient sequence target converges →
        trans
          (multiplyConstantLimit laws coefficient sequence)
          (cong (λ value → coefficient *ℝ value) converges)
  ; Gram.ScalarConvergenceAlgebra.limit =
      Seq.limit sequenceLimit
  ; Gram.ScalarConvergenceAlgebra.sequenceConvergesToLimit =
      λ sequence → refl
  }

cylinderAndGramShareConvergence :
  ∀ {sequenceLimit}
    (laws : CanonicalRealLimitLaws sequenceLimit)
    sequence target →
  Cylinder.Converges
    (canonicalCylinderAlgebra laws)
    sequence target
  ≡
  Gram.Converges
    (canonicalGramScalarConvergence laws)
    sequence target
cylinderAndGramShareConvergence laws sequence target = refl

canonicalRealLimitCylinderCompilerLevel : ProofLevel
canonicalRealLimitCylinderCompilerLevel = machineChecked

canonicalRealLimitGramCompilerLevel : ProofLevel
canonicalRealLimitGramCompilerLevel = machineChecked

canonicalRealLimitSameConvergenceLevel : ProofLevel
canonicalRealLimitSameConvergenceLevel = machineChecked

canonicalRealLimitLawsAuthorityLevel : ProofLevel
canonicalRealLimitLawsAuthorityLevel = standardImported
