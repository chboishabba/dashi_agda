module DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver where

------------------------------------------------------------------------
-- Polynomial solver for an axiomatic real carrier.
--
-- The reflective tactic uses the target carrier as its coefficient carrier.
-- That leaves coefficient arithmetic opaque for DASHI's postulated real
-- operations. Here the legacy solver is instantiated with a separate,
-- computable coefficient carrier: a formal difference of natural numbers.
--
-- All coefficient-morphism laws below are proved from the commutative-ring
-- interface itself. No second solver is trusted inside this socket.
--
-- The exported solver uses a canonical interpretation for formal 0 and 1.
-- Those two coefficients map definitionally to zeroR and oneR; every other
-- coefficient is transported through the original proved interpretation.  This
-- keeps every caller on one Polynomial type and removes the elaboration-only
-- mismatch that previously appeared when helper syntax and solveComputed used
-- different solver modules.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Bundles.Raw using (RawRing)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base as Nat using (_+_; _*_)
import Data.Nat.Properties as NatP
open import Relation.Binary.Definitions using (WeaklyDecidable)
open import Relation.Binary.PropositionalEquality as Eq using
  (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning
open import Relation.Nullary.Decidable.Core using (yes; no)

import Algebra.Properties.Semiring.Mult.TCOptimised as NaturalMultiplication
import Algebra.Properties.Ring as RingProperties
import Algebra.Solver.Ring as LegacyRingSolver
import Algebra.Solver.Ring.AlmostCommutativeRing as LegacyACR

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.BalabanRealPolynomialRing using
  ( _+R_
  ; _*R_
  ; -R_
  ; zeroR
  ; oneR
  ; realCommutativeRing
  )

private
  module RealRing = CommutativeRing realCommutativeRing
  module RealRingProperties = RingProperties RealRing.ring
  module Natural = NaturalMultiplication RealRing.semiring

open RealRing using
  ( +-assoc
  ; +-comm
  ; +-cong
  ; +-identityˡ
  ; +-identityʳ
  ; -‿inverseʳ
  ; distribˡ
  ; distribʳ
  )
open RealRingProperties using
  ( -0#≈0#
  ; -‿+-comm
  ; -‿involutive
  ; -‿distribˡ-*
  ; -‿distribʳ-*
  ; [-x][-y]≈xy
  )
open Natural using (_×_; ×-homo-+; ×1-homo-*)

natCoefficient : Nat → ℝ
natCoefficient n = n × oneR

natCoefficientZero : natCoefficient zero ≡ zeroR
natCoefficientZero = refl

natCoefficientOne : natCoefficient (suc zero) ≡ oneR
natCoefficientOne = refl

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

addInterchange :
  ∀ a b c d →
  (a +R b) +R (c +R d)
    ≡ (a +R c) +R (b +R d)
addInterchange a b c d = begin
  (a +R b) +R (c +R d)
    ≡⟨ +-assoc a b (c +R d) ⟩
  a +R (b +R (c +R d))
    ≡⟨ cong (a +R_) (sym (+-assoc b c d)) ⟩
  a +R ((b +R c) +R d)
    ≡⟨ cong (λ middle → a +R (middle +R d)) (+-comm b c) ⟩
  a +R ((c +R b) +R d)
    ≡⟨ cong (a +R_) (+-assoc c b d) ⟩
  a +R (c +R (b +R d))
    ≡⟨ sym (+-assoc a c (b +R d)) ⟩
  (a +R c) +R (b +R d)
    ∎

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
  sym (begin
    (natCoefficient p +R (-R natCoefficient n))
      +R (natCoefficient q +R (-R natCoefficient m))
      ≡⟨ addInterchange
           (natCoefficient p) (-R natCoefficient n)
           (natCoefficient q) (-R natCoefficient m) ⟩
    (natCoefficient p +R natCoefficient q)
      +R ((-R natCoefficient n) +R (-R natCoefficient m))
      ≡⟨ cong
           ((natCoefficient p +R natCoefficient q) +R_)
           (-‿+-comm (natCoefficient n) (natCoefficient m)) ⟩
    (natCoefficient p +R natCoefficient q)
      +R (-R (natCoefficient n +R natCoefficient m))
      ∎)

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
  sym (begin
    (natCoefficient p +R (-R natCoefficient n))
      *R (natCoefficient q +R (-R natCoefficient m))
      ≡⟨ distribʳ
           (natCoefficient q +R (-R natCoefficient m))
           (natCoefficient p) (-R natCoefficient n) ⟩
    (natCoefficient p *R (natCoefficient q +R (-R natCoefficient m)))
      +R ((-R natCoefficient n)
        *R (natCoefficient q +R (-R natCoefficient m)))
      ≡⟨ +-cong
           (distribˡ
             (natCoefficient p) (natCoefficient q) (-R natCoefficient m))
           (distribˡ
             (-R natCoefficient n) (natCoefficient q) (-R natCoefficient m)) ⟩
    ((natCoefficient p *R natCoefficient q)
      +R (natCoefficient p *R (-R natCoefficient m)))
      +R (((-R natCoefficient n) *R natCoefficient q)
        +R ((-R natCoefficient n) *R (-R natCoefficient m)))
      ≡⟨ +-cong
           (cong
             ((natCoefficient p *R natCoefficient q) +R_)
             (sym (-‿distribʳ-*
               (natCoefficient p) (natCoefficient m))))
           (+-cong
             (sym (-‿distribˡ-*
               (natCoefficient n) (natCoefficient q)))
             ([-x][-y]≈xy
               (natCoefficient n) (natCoefficient m))) ⟩
    ((natCoefficient p *R natCoefficient q)
      +R (-R (natCoefficient p *R natCoefficient m)))
      +R ((-R (natCoefficient n *R natCoefficient q))
        +R (natCoefficient n *R natCoefficient m))
      ≡⟨ cong
           (((natCoefficient p *R natCoefficient q)
             +R (-R (natCoefficient p *R natCoefficient m))) +R_)
           (+-comm
             (-R (natCoefficient n *R natCoefficient q))
             (natCoefficient n *R natCoefficient m)) ⟩
    ((natCoefficient p *R natCoefficient q)
      +R (-R (natCoefficient p *R natCoefficient m)))
      +R ((natCoefficient n *R natCoefficient m)
        +R (-R (natCoefficient n *R natCoefficient q)))
      ≡⟨ addInterchange
           (natCoefficient p *R natCoefficient q)
           (-R (natCoefficient p *R natCoefficient m))
           (natCoefficient n *R natCoefficient m)
           (-R (natCoefficient n *R natCoefficient q)) ⟩
    ((natCoefficient p *R natCoefficient q)
      +R (natCoefficient n *R natCoefficient m))
      +R ((-R (natCoefficient p *R natCoefficient m))
        +R (-R (natCoefficient n *R natCoefficient q)))
      ≡⟨ cong
           (((natCoefficient p *R natCoefficient q)
             +R (natCoefficient n *R natCoefficient m)) +R_)
           (-‿+-comm
             (natCoefficient p *R natCoefficient m)
             (natCoefficient n *R natCoefficient q)) ⟩
    ((natCoefficient p *R natCoefficient q)
      +R (natCoefficient n *R natCoefficient m))
      +R (-R ((natCoefficient p *R natCoefficient m)
        +R (natCoefficient n *R natCoefficient q)))
      ∎)

negateCoefficientHomomorphic :
  ∀ x →
  interpretCoefficient (negateCoefficient x)
    ≡ -R interpretCoefficient x
negateCoefficientHomomorphic (coefficient p n) = begin
  natCoefficient n +R (-R natCoefficient p)
    ≡⟨ +-comm (natCoefficient n) (-R natCoefficient p) ⟩
  (-R natCoefficient p) +R natCoefficient n
    ≡⟨ cong
         ((-R natCoefficient p) +R_)
         (sym (-‿involutive (natCoefficient n))) ⟩
  (-R natCoefficient p) +R (-R (-R natCoefficient n))
    ≡⟨ -‿+-comm (natCoefficient p) (-R natCoefficient n) ⟩
  -R (natCoefficient p +R (-R natCoefficient n))
    ∎

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
    sym (begin
      (natCoefficient p +R natCoefficient m)
        +R (-R (natCoefficient n +R natCoefficient m))
        ≡⟨ cong
             ((natCoefficient p +R natCoefficient m) +R_)
             (sym (-‿+-comm
               (natCoefficient n) (natCoefficient m))) ⟩
      (natCoefficient p +R natCoefficient m)
        +R ((-R natCoefficient n) +R (-R natCoefficient m))
        ≡⟨ addInterchange
             (natCoefficient p) (natCoefficient m)
             (-R natCoefficient n) (-R natCoefficient m) ⟩
      (natCoefficient p +R (-R natCoefficient n))
        +R (natCoefficient m +R (-R natCoefficient m))
        ≡⟨ cong
             ((natCoefficient p +R (-R natCoefficient n)) +R_)
             (-‿inverseʳ (natCoefficient m)) ⟩
      (natCoefficient p +R (-R natCoefficient n)) +R zeroR
        ≡⟨ +-identityʳ
             (natCoefficient p +R (-R natCoefficient n)) ⟩
      natCoefficient p +R (-R natCoefficient n)
        ∎)

  rightDifferenceShift :
    ∀ q n m →
    (natCoefficient q +R natCoefficient n)
      +R (-R (natCoefficient n +R natCoefficient m))
      ≡
    natCoefficient q +R (-R natCoefficient m)
  rightDifferenceShift q n m = begin
    (natCoefficient q +R natCoefficient n)
      +R (-R (natCoefficient n +R natCoefficient m))
      ≡⟨ cong
           ((natCoefficient q +R natCoefficient n) +R_)
           (sym (-‿+-comm
             (natCoefficient n) (natCoefficient m))) ⟩
    (natCoefficient q +R natCoefficient n)
      +R ((-R natCoefficient n) +R (-R natCoefficient m))
      ≡⟨ cong
           ((natCoefficient q +R natCoefficient n) +R_)
           (+-comm (-R natCoefficient n) (-R natCoefficient m)) ⟩
    (natCoefficient q +R natCoefficient n)
      +R ((-R natCoefficient m) +R (-R natCoefficient n))
      ≡⟨ addInterchange
           (natCoefficient q) (natCoefficient n)
           (-R natCoefficient m) (-R natCoefficient n) ⟩
    (natCoefficient q +R (-R natCoefficient m))
      +R (natCoefficient n +R (-R natCoefficient n))
      ≡⟨ cong
           ((natCoefficient q +R (-R natCoefficient m)) +R_)
           (-‿inverseʳ (natCoefficient n)) ⟩
    (natCoefficient q +R (-R natCoefficient m)) +R zeroR
      ≡⟨ +-identityʳ
           (natCoefficient q +R (-R natCoefficient m)) ⟩
    natCoefficient q +R (-R natCoefficient m)
      ∎

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
... | yes cross = just
  (crossEqualityImpliesCoefficientEquality
    {p = p} {n = n} {q = q} {m = m} cross)
... | no _ = nothing

------------------------------------------------------------------------
-- Canonical interpretation used by the exported solver.
------------------------------------------------------------------------

canonicalInterpretCoefficient : IntegerCoefficient → ℝ
canonicalInterpretCoefficient (coefficient zero zero) = zeroR
canonicalInterpretCoefficient (coefficient zero (suc negative)) =
  interpretCoefficient (coefficient zero (suc negative))
canonicalInterpretCoefficient (coefficient (suc zero) zero) = oneR
canonicalInterpretCoefficient (coefficient (suc zero) (suc negative)) =
  interpretCoefficient (coefficient (suc zero) (suc negative))
canonicalInterpretCoefficient (coefficient (suc (suc positive)) zero) =
  interpretCoefficient (coefficient (suc (suc positive)) zero)
canonicalInterpretCoefficient
  (coefficient (suc (suc positive)) (suc negative)) =
  interpretCoefficient
    (coefficient (suc (suc positive)) (suc negative))

canonicalInterpretationCorrect :
  ∀ value → canonicalInterpretCoefficient value ≡ interpretCoefficient value
canonicalInterpretationCorrect (coefficient zero zero) =
  sym zeroCoefficientHomomorphic
canonicalInterpretationCorrect (coefficient zero (suc negative)) = refl
canonicalInterpretationCorrect (coefficient (suc zero) zero) =
  sym oneCoefficientHomomorphic
canonicalInterpretationCorrect (coefficient (suc zero) (suc negative)) = refl
canonicalInterpretationCorrect (coefficient (suc (suc positive)) zero) = refl
canonicalInterpretationCorrect
  (coefficient (suc (suc positive)) (suc negative)) = refl

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
