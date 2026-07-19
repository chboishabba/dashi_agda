module DASHI.Physics.YangMills.BalabanCanonicalRealPolynomialSolver where

------------------------------------------------------------------------
-- Canonical coefficient interpretation for the computed polynomial socket.
--
-- The original integer-coefficient morphism is mathematically correct, but its
-- interpretations of 0 and 1 are only propositionally equal to DASHI's zeroR
-- and oneR.  The legacy solver exposes those interpretations in the type of a
-- generated proof, so large identities fail at the final definitional boundary.
--
-- This module changes only the coefficient interpretation: formal 0 and 1 map
-- definitionally to zeroR and oneR, while every other coefficient uses the
-- already proved interpretation.  A pointwise equivalence transports all ring
-- morphism laws and the weak coefficient decision procedure.  Thus this is a
-- proof-preserving normalization adapter, not another trusted solver.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Maybe.Base using (just; nothing)
open import Relation.Binary.Definitions using (WeaklyDecidable)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import Algebra.Solver.Ring as LegacyRingSolver
import Algebra.Solver.Ring.AlmostCommutativeRing as LegacyACR

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

canonicalInterpretCoefficient : IntegerCoefficient → _
canonicalInterpretCoefficient (coefficient zero zero) = zeroR
canonicalInterpretCoefficient (coefficient (suc zero) zero) = oneR
canonicalInterpretCoefficient value = interpretCoefficient value

canonicalInterpretationCorrect :
  ∀ value → canonicalInterpretCoefficient value ≡ interpretCoefficient value
canonicalInterpretationCorrect (coefficient zero zero) =
  sym zeroCoefficientHomomorphic
canonicalInterpretationCorrect (coefficient (suc zero) zero) =
  sym oneCoefficientHomomorphic
canonicalInterpretationCorrect (coefficient (suc (suc positive)) zero) = refl
canonicalInterpretationCorrect (coefficient positive (suc negative)) = refl

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
