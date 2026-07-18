module DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver where

------------------------------------------------------------------------
-- Polynomial solver for an axiomatic real carrier.
--
-- `Tactic.RingSolver` uses the target carrier as its coefficient carrier.
-- That is ideal for concrete rings, but it leaves coefficients such as
-- `-(1 * 1)` opaque for DASHI's postulated real operations.  Large identities
-- can then normalise to propositionally equal, but definitionally different,
-- coefficient terms.
--
-- Here the legacy standard-library solver is instantiated with a separate,
-- computable coefficient carrier.  A coefficient is a formal difference of
-- two natural numbers.  Its interpretation in the real ring is
--
--     positive · 1 - negative · 1.
--
-- Coefficient equality is decided by cross addition, while the target
-- polynomial variables still range over DASHI's canonical ℝ.  The only
-- foundational input is the commutative-ring structure already isolated in
-- `BalabanRealPolynomialRing`.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Bundles.Raw using (RawRing)
open import Data.List.Base using ([]; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base as Nat using (_+_; _*_)
import Data.Nat.Properties as NatP
open import Relation.Binary.Definitions using (WeaklyDecidable)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

import Algebra.Properties.Semiring.Mult.TCOptimised as NaturalMultiplication
import Algebra.Properties.Ring as RingProperties
import Algebra.Solver.Ring as LegacyRingSolver
import Algebra.Solver.Ring.AlmostCommutativeRing as LegacyACR
import Tactic.RingSolver as SmallSolver

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using
  ( _+R_
  ; _*R_
  ; -R_
  ; zeroR
  ; oneR
  ; realCommutativeRing
  ; realSolverRing
  )

private
  module RealRing = CommutativeRing realCommutativeRing
  module RealRingProperties = RingProperties RealRing.ring
  module Natural = NaturalMultiplication RealRing.semiring

open RealRing using
  ( +-identityˡ
  ; +-identityʳ
  )
open RealRingProperties using (-0#≈0#)
open Natural using (_×_; ×-homo-0; ×-homo-1; ×-homo-+; ×1-homo-*)

natCoefficient : Nat → ℝ
natCoefficient n = n × oneR

natCoefficientZero : natCoefficient zero ≡ zeroR
natCoefficientZero = ×-homo-0 oneR

natCoefficientOne : natCoefficient (suc zero) ≡ oneR
natCoefficientOne = ×-homo-1 oneR

natCoefficientAdd :
  ∀ m n →
  natCoefficient (m Nat.+ n)
    ≡ natCoefficient m +R natCoefficient n
natCoefficientAdd m n = ×-homo-+ oneR m n

natCoefficientMultiply :
  ∀ m n →
  natCoefficient (m Nat.* n)
    ≡ natCoefficient m *R natCoefficient n
natCoefficientMultiply m n = ×1-homo-* m n

record IntegerCoefficient : Set where
  constructor coefficient
  field
    positive negative : Nat

open IntegerCoefficient public

zeroCoefficient : IntegerCoefficient
zeroCoefficient = coefficient zero zero

oneCoefficient : IntegerCoefficient
oneCoefficient = coefficient (suc zero) zero

addCoefficient : IntegerCoefficient → IntegerCoefficient → IntegerCoefficient
addCoefficient (coefficient p n) (coefficient q m) =
  coefficient (p Nat.+ q) (n Nat.+ m)

multiplyCoefficient : IntegerCoefficient → IntegerCoefficient → IntegerCoefficient
multiplyCoefficient (coefficient p n) (coefficient q m) =
  coefficient
    ((p Nat.* q) Nat.+ (n Nat.* m))
    ((p Nat.* m) Nat.+ (n Nat.* q))

negateCoefficient : IntegerCoefficient → IntegerCoefficient
negateCoefficient (coefficient p n) = coefficient n p

interpretCoefficient : IntegerCoefficient → ℝ
interpretCoefficient (coefficient p n) =
  natCoefficient p +R (-R natCoefficient n)

addCoefficientHomomorphic :
  ∀ x y →
  interpretCoefficient (addCoefficient x y)
    ≡ interpretCoefficient x +R interpretCoefficient y
addCoefficientHomomorphic
  (coefficient p n) (coefficient q m)
  rewrite natCoefficientAdd p q | natCoefficientAdd n m =
  SmallSolver.solve
    (natCoefficient p ∷ natCoefficient n ∷
     natCoefficient q ∷ natCoefficient m ∷ [])
    realSolverRing

multiplyCoefficientHomomorphic :
  ∀ x y →
  interpretCoefficient (multiplyCoefficient x y)
    ≡ interpretCoefficient x *R interpretCoefficient y
multiplyCoefficientHomomorphic
  (coefficient p n) (coefficient q m)
  rewrite natCoefficientAdd (p Nat.* q) (n Nat.* m)
        | natCoefficientAdd (p Nat.* m) (n Nat.* q)
        | natCoefficientMultiply p q
        | natCoefficientMultiply n m
        | natCoefficientMultiply p m
        | natCoefficientMultiply n q =
  SmallSolver.solve
    (natCoefficient p ∷ natCoefficient n ∷
     natCoefficient q ∷ natCoefficient m ∷ [])
    realSolverRing

negateCoefficientHomomorphic :
  ∀ x →
  interpretCoefficient (negateCoefficient x)
    ≡ -R interpretCoefficient x
negateCoefficientHomomorphic (coefficient p n) =
  SmallSolver.solve
    (natCoefficient p ∷ natCoefficient n ∷ [])
    realSolverRing

zeroCoefficientHomomorphic :
  interpretCoefficient zeroCoefficient ≡ zeroR
zeroCoefficientHomomorphic =
  trans
    (cong₂ _+R_
      natCoefficientZero
      (cong -R_ natCoefficientZero))
    (trans
      (cong (zeroR +R_) -0#≈0#)
      (+-identityˡ zeroR))

oneCoefficientHomomorphic :
  interpretCoefficient oneCoefficient ≡ oneR
oneCoefficientHomomorphic =
  trans
    (cong₂ _+R_
      natCoefficientOne
      (cong -R_ natCoefficientZero))
    (trans
      (cong (oneR +R_) -0#≈0#)
      (+-identityʳ oneR))

coefficientRawRing : RawRing _ _
coefficientRawRing = record
  { Carrier = IntegerCoefficient
  ; _≈_ = _≡_
  ; _+_ = addCoefficient
  ; _*_ = multiplyCoefficient
  ; -_ = negateCoefficient
  ; 0# = zeroCoefficient
  ; 1# = oneCoefficient
  }

realLegacyRing : LegacyACR.AlmostCommutativeRing _ _
realLegacyRing = LegacyACR.fromCommutativeRing realCommutativeRing

coefficientMorphism :
  coefficientRawRing LegacyACR.-Raw-AlmostCommutative⟶ realLegacyRing
coefficientMorphism = record
  { ⟦_⟧ = interpretCoefficient
  ; +-homo = addCoefficientHomomorphic
  ; *-homo = multiplyCoefficientHomomorphic
  ; -‿homo = negateCoefficientHomomorphic
  ; 0-homo = zeroCoefficientHomomorphic
  ; 1-homo = oneCoefficientHomomorphic
  }

private
  leftDifferenceShift :
    ∀ p n m →
    natCoefficient p +R (-R natCoefficient n)
      ≡
    (natCoefficient p +R natCoefficient m)
      +R (-R (natCoefficient n +R natCoefficient m))
  leftDifferenceShift p n m =
    SmallSolver.solve
      (natCoefficient p ∷ natCoefficient n ∷ natCoefficient m ∷ [])
      realSolverRing

  rightDifferenceShift :
    ∀ q n m →
    (natCoefficient q +R natCoefficient n)
      +R (-R (natCoefficient n +R natCoefficient m))
      ≡
    natCoefficient q +R (-R natCoefficient m)
  rightDifferenceShift q n m =
    SmallSolver.solve
      (natCoefficient q ∷ natCoefficient n ∷ natCoefficient m ∷ [])
      realSolverRing

crossEqualityImpliesCoefficientEquality :
  ∀ {p n q m} →
  p Nat.+ m ≡ q Nat.+ n →
  interpretCoefficient (coefficient p n)
    ≡ interpretCoefficient (coefficient q m)
crossEqualityImpliesCoefficientEquality {p} {n} {q} {m} cross =
  trans
    (leftDifferenceShift p n m)
    (trans
      (cong
        (λ total →
          total +R (-R (natCoefficient n +R natCoefficient m)))
        (trans
          (sym (natCoefficientAdd p m))
          (trans
            (cong natCoefficient cross)
            (natCoefficientAdd q n))))
      (rightDifferenceShift q n m))

coefficientWeakEquality :
  WeaklyDecidable
    (LegacyACR.Induced-equivalence coefficientMorphism)
coefficientWeakEquality (coefficient p n) (coefficient q m)
  with NatP._≟_ (p Nat.+ m) (q Nat.+ n)
... | yes cross = just (crossEqualityImpliesCoefficientEquality cross)
... | no _ = nothing

module RealPolynomialSolver =
  LegacyRingSolver
    coefficientRawRing
    realLegacyRing
    coefficientMorphism
    coefficientWeakEquality
