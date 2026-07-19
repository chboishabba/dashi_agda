module DASHI.Physics.YangMills.BalabanCanonicalRealPolynomialSolver where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Maybe.Base using (just; nothing)
open import Relation.Binary.Definitions using (WeaklyDecidable)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import Algebra.Solver.Ring as LegacyRingSolver
import Algebra.Solver.Ring.AlmostCommutativeRing as LegacyACR

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using
  (_+R_; _*R_; -R_; zeroR; oneR)
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver as Base using
  ( IntegerCoefficient
  ; coefficient
  ; zeroCoefficient
  ; oneCoefficient
  ; addCoefficient
  ; multiplyCoefficient
  ; negateCoefficient
  ; coefficientRawRing
  ; realLegacyRing
  ; interpretCoefficient
  ; addCoefficientHomomorphic
  ; multiplyCoefficientHomomorphic
  ; negateCoefficientHomomorphic
  ; zeroCoefficientHomomorphic
  ; oneCoefficientHomomorphic
  ; coefficientWeakEquality
  )

canonicalInterpretCoefficient : IntegerCoefficient → ℝ
canonicalInterpretCoefficient (coefficient zero zero) = zeroR
canonicalInterpretCoefficient (coefficient (suc zero) zero) = oneR
canonicalInterpretCoefficient (coefficient (suc (suc positive)) zero) =
  interpretCoefficient (coefficient (suc (suc positive)) zero)
canonicalInterpretCoefficient (coefficient zero (suc negative)) =
  interpretCoefficient (coefficient zero (suc negative))
canonicalInterpretCoefficient (coefficient (suc positive) (suc negative)) =
  interpretCoefficient (coefficient (suc positive) (suc negative))

canonicalInterpretationCorrect :
  ∀ value → canonicalInterpretCoefficient value ≡ interpretCoefficient value
canonicalInterpretationCorrect (coefficient zero zero) =
  sym zeroCoefficientHomomorphic
canonicalInterpretationCorrect (coefficient (suc zero) zero) =
  sym oneCoefficientHomomorphic
canonicalInterpretationCorrect (coefficient (suc (suc positive)) zero) = refl
canonicalInterpretationCorrect (coefficient zero (suc negative)) = refl
canonicalInterpretationCorrect (coefficient (suc positive) (suc negative)) = refl

canonicalAddHomomorphic :
  ∀ left right →
  canonicalInterpretCoefficient (addCoefficient left right)
    ≡ canonicalInterpretCoefficient left +R canonicalInterpretCoefficient right
canonicalAddHomomorphic left right =
  trans
    (canonicalInterpretationCorrect (addCoefficient left right))
    (trans
      (addCoefficientHomomorphic left right)
      (cong₂ _+R_
        (sym (canonicalInterpretationCorrect left))
        (sym (canonicalInterpretationCorrect right))))

canonicalMultiplyHomomorphic :
  ∀ left right →
  canonicalInterpretCoefficient (multiplyCoefficient left right)
    ≡ canonicalInterpretCoefficient left *R canonicalInterpretCoefficient right
canonicalMultiplyHomomorphic left right =
  trans
    (canonicalInterpretationCorrect (multiplyCoefficient left right))
    (trans
      (multiplyCoefficientHomomorphic left right)
      (cong₂ _*R_
        (sym (canonicalInterpretationCorrect left))
        (sym (canonicalInterpretationCorrect right))))

canonicalNegateHomomorphic :
  ∀ value →
  canonicalInterpretCoefficient (negateCoefficient value)
    ≡ -R canonicalInterpretCoefficient value
canonicalNegateHomomorphic value =
  trans
    (canonicalInterpretationCorrect (negateCoefficient value))
    (trans
      (negateCoefficientHomomorphic value)
      (cong -R_ (sym (canonicalInterpretationCorrect value))))

canonicalCoefficientMorphism :
  coefficientRawRing LegacyACR.-Raw-AlmostCommutative⟶ realLegacyRing
canonicalCoefficientMorphism = record
  { ⟦_⟧ = canonicalInterpretCoefficient
  ; +-homo = canonicalAddHomomorphic
  ; *-homo = canonicalMultiplyHomomorphic
  ; -‿homo = canonicalNegateHomomorphic
  ; 0-homo = refl
  ; 1-homo = refl
  }

canonicalCoefficientWeakEquality :
  WeaklyDecidable
    (LegacyACR.Induced-equivalence canonicalCoefficientMorphism)
canonicalCoefficientWeakEquality left right
  with coefficientWeakEquality left right
... | just proof = just
  (trans
    (canonicalInterpretationCorrect left)
    (trans proof (sym (canonicalInterpretationCorrect right))))
... | nothing = nothing

module RealPolynomialSolver =
  LegacyRingSolver
    coefficientRawRing
    realLegacyRing
    canonicalCoefficientMorphism
    canonicalCoefficientWeakEquality
