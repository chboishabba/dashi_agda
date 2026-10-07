module DASHI.NumberTheory.Collatz.SyracuseInv3Pow2Exact where

------------------------------------------------------------------------
-- AGDA-NATIVE INVERSE OF THREE MODULO 2^m
--
-- The recursive candidate is already fixed by
-- `SyracuseParityCylinderCandidateExact`:
--
--   a₁ = 1
--   a₂ = 3
--   aₘ₊₂ = 4 aₘ - 1.
--
-- We prove the stronger exact integer statement
--
--   3 aₘ = 1 + qₘ 2^m
--
-- for every m>0.  The modulo inverse law then follows only from standard
-- `Data.Nat.DivMod` periodicity.  This removes the cross-prover arithmetic
-- dependency: Lean #46 remains an independent mirror/check, not an axiom.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _-_)
open import Data.Nat.Base using (NonZero; nonZero)
open import Data.Nat.DivMod using (_%_; [m+kn]%n≡m%n; n%1≡0)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderCandidateExact as Candidate
import DASHI.NumberTheory.Collatz.SyracusePow2ArithmeticExact as Pow2

instance
  nonZeroFour : NonZero 4
  nonZeroFour = nonZero

------------------------------------------------------------------------
-- Positivity of every nonzero-level inverse candidate.
------------------------------------------------------------------------

oneLessThanFour : 1 < 4
oneLessThanFour = NatP.s≤s (NatP.s≤s NatP.z≤n)

inv3CandidatePositive :
  (m : Nat) →
  0 < Candidate.inv3Candidate (suc m)
inv3CandidatePositive zero = NatP.s≤s NatP.z≤n
inv3CandidatePositive (suc zero) = NatP.s≤s NatP.z≤n
inv3CandidatePositive (suc (suc m)) =
  let
    a = Candidate.inv3Candidate (suc m)

    oneLeA : 1 ≤ a
    oneLeA = inv3CandidatePositive m

    fourLeFourA : 4 ≤ 4 * a
    fourLeFourA = NatP.*-monoʳ-≤ 4 oneLeA

    oneLessFourA : 1 < 4 * a
    oneLessFourA = NatP.<-≤-trans oneLessThanFour fourLeFourA
  in
  NatP.m<n⇒0<n∸m oneLessFourA

------------------------------------------------------------------------
-- Strong exact quotient identity.
------------------------------------------------------------------------

inv3ExactQuotient :
  (m : Nat) →
  Σ Nat (λ q →
    3 * Candidate.inv3Candidate (suc m)
    ≡ 1 + q * Cylinder.pow2 (suc m))
inv3ExactQuotient zero = 1 , refl
inv3ExactQuotient (suc zero) = 2 , refl
inv3ExactQuotient (suc (suc m)) with inv3ExactQuotient m
... | q , induction =
  let
    a = Candidate.inv3Candidate (suc m)
    b = (4 * a) - 1
    oldModulus = Cylinder.pow2 (suc m)
    newModulus = Cylinder.pow2 (suc (suc (suc m)))

    oneLeA : 1 ≤ a
    oneLeA = inv3CandidatePositive m

    fourLeFourA : 4 ≤ 4 * a
    fourLeFourA = NatP.*-monoʳ-≤ 4 oneLeA

    oneLeFourA : 1 ≤ 4 * a
    oneLeFourA = NatP.≤-trans (NatP.s≤s NatP.z≤n) fourLeFourA

    predecessorRestores : b + 1 ≡ 4 * a
    predecessorRestores = NatP.m∸n+n≡m oneLeFourA

    leftExpanded : 3 * b + 3 ≡ 3 * (4 * a)
    leftExpanded =
      trans
        (solve 1
          (λ value →
            (con 3 :* value) :+ con 3
            :=
            con 3 :* (value :+ con 1))
          refl b)
        (cong (3 *_) predecessorRestores)

    reassociateThreeFour : 3 * (4 * a) ≡ 4 * (3 * a)
    reassociateThreeFour =
      solve 1
        (λ value →
          con 3 :* (con 4 :* value)
          :=
          con 4 :* (con 3 :* value))
        refl a

    scaleInduction :
      4 * (3 * a) ≡ 4 * (1 + q * oldModulus)
    scaleInduction = cong (4 *_) induction

    expandNewModulus :
      4 * (1 + q * oldModulus)
      ≡ (1 + q * newModulus) + 3
    expandNewModulus =
      solve 2
        (λ q M →
          con 4 :* (con 1 :+ q :* M)
          :=
          (con 1 :+ q :* (con 2 :* (con 2 :* M))) :+ con 3)
        refl q oldModulus

    withCommonThree :
      3 * b + 3 ≡ (1 + q * newModulus) + 3
    withCommonThree =
      trans leftExpanded
        (trans reassociateThreeFour
          (trans scaleInduction expandNewModulus))
  in
  q , NatP.+-cancelʳ-≡
        (3 * b)
        (1 + q * newModulus)
        3
        withCommonThree

------------------------------------------------------------------------
-- The exact source consumed by the parity-cylinder candidate.
------------------------------------------------------------------------

inverseLaw :
  (m : Nat) →
  (3 * Candidate.inv3Candidate m) % Cylinder.pow2 m
  ≡ 1 % Cylinder.pow2 m
inverseLaw zero =
  trans (n%1≡0 0) (sym (n%1≡0 1))
inverseLaw (suc m) with inv3ExactQuotient m
... | q , exact =
  let
    instance modulus-nonzero = Pow2.pow2NonZero (suc m)
    modulus = Cylinder.pow2 (suc m)
  in
  trans
    (cong (_% modulus) exact)
    ([m+kn]%n≡m%n 1 q modulus)

canonicalInv3Pow2Source : Candidate.Inv3Pow2Source
canonicalInv3Pow2Source = record
  { Candidate.inverseLaw = inverseLaw
  }

record Inv3AgdaBoundary : Set where
  constructor inv3AgdaBoundary
  field
    recursiveCandidateOwned : Nat
    exactQuotientIdentityOwned : Nat
    inverseModuloPow2Owned : Nat
    externalLeanRequiredForArithmetic : Nat

canonicalInv3AgdaBoundary : Inv3AgdaBoundary
canonicalInv3AgdaBoundary = inv3AgdaBoundary 1 1 1 0
