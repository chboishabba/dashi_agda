module DASHI.Physics.Closure.NSTriadKNLuoFiniteMobiusOrientationObstructionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Mathematical ingredient: the elementary monodromy obstruction for a real
-- line bundle with Möbius sign reversal around a closed loop.
-- Title: "Finite odd-monodromy orientation obstruction".
-- Author: DASHI repository contributors.
-- DOI: not applicable; this is a repository-original finite abstraction.
--
-- PURPOSE
-- Formalise the exact kernel of the proposed non-orientable-eigenline
-- mechanism without claiming that the physical Navier--Stokes angular strain
-- symbol has already been identified with it.  Parallel transport through an
-- odd number of sign reversals sends a section value a to -a.  If the section
-- is also globally closed around the loop, then a=-a and hence a=0.
--
-- Thus a nonzero globally oriented section cannot coexist with odd monodromy.
-- The missing physical theorem is the construction of the actual angular
-- eigenline bundle and proof of its transverse degeneracy/monodromy.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

half : ℚ
half = Int.+ 1 / 2

flipTransport : Nat → ℚ → ℚ
flipTransport zero value = value
flipTransport (suc count) value = - flipTransport count value

double : Nat → Nat
double zero = zero
double (suc count) = suc (suc (double count))

evenTransport :
  (count : Nat) →
  (value : ℚ) →
  flipTransport (double count) value ≡ value
evenTransport zero value = refl
evenTransport (suc count) value
  rewrite evenTransport count value =
  solve (value ∷ [])

oddTransport :
  (count : Nat) →
  (value : ℚ) →
  flipTransport (suc (double count)) value ≡ - value
oddTransport count value
  rewrite evenTransport count value = refl

valueEqualsNegativeImpliesZero :
  (value : ℚ) →
  value ≡ - value →
  value ≡ 0ℚ
valueEqualsNegativeImpliesZero value equalsNegative =
  let
    doubledZero : value + value ≡ 0ℚ
    doubledZero =
      trans
        (cong (λ right → value + right) equalsNegative)
        (solve (value ∷ []))
  in
  trans
    (solve (value ∷ []))
    (trans
      (cong (λ doubled → half * doubled) doubledZero)
      (solve []))

closedOddMonodromyForcesZero :
  (count : Nat) →
  (value : ℚ) →
  flipTransport (suc (double count)) value ≡ value →
  value ≡ 0ℚ
closedOddMonodromyForcesZero count value loopClosure =
  valueEqualsNegativeImpliesZero value
    (trans
      (sym loopClosure)
      (oddTransport count value))
