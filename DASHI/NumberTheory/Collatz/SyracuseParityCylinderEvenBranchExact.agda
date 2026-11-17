module DASHI.NumberTheory.Collatz.SyracuseParityCylinderEvenBranchExact where

------------------------------------------------------------------------
-- EXACT EVEN-BRANCH PARITY-CYLINDER TRANSPORT
--
-- This tranche consumes the literal Syracuse theorem
--
--   parity x = even  ->  2 * S(x) = x
--
-- and pays the generic power-of-two residue transport needed by the
-- parity-cylinder induction.  No inverse-of-three theorem is used here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (NonZero; nonZero)
open import Data.Nat.DivMod using
  (_%_; _/_; m≡m%n+[m/n]*n; [m+kn]%n≡m%n; m%n<n; m<n⇒m%n≡m; m*n%n≡0)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderCandidateExact as Candidate
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderOneStepBaseExact as Base
import DASHI.NumberTheory.Collatz.SyracusePow2ArithmeticExact as Pow2
import DASHI.NumberTheory.Collatz.SyracuseOneStepArithmeticExact as OneStep

instance
  nonZeroTwo : NonZero 2
  nonZeroTwo = nonZero

------------------------------------------------------------------------
-- Generic doubling law on the nested power-of-two cylinders.
------------------------------------------------------------------------

doubleModuloPow2 :
  (m y : Nat) →
  (2 * y) % Cylinder.pow2 (suc m)
  ≡ 2 * (y % Cylinder.pow2 m)
doubleModuloPow2 m y =
  let
    instance level-nonzero = Pow2.pow2NonZero m
    instance next-nonzero = Pow2.pow2NonZero (suc m)

    modulus = Cylinder.pow2 m
    remainder = y % modulus
    quotient = y / modulus

    decomposition : y ≡ remainder + quotient * modulus
    decomposition = m≡m%n+[m/n]*n y modulus

    doubledDecomposition :
      2 * y
      ≡ 2 * remainder + quotient * Cylinder.pow2 (suc m)
    doubledDecomposition =
      trans
        (cong (2 *_) decomposition)
        (solve 3
          (λ r q M →
            con 2 :* (r :+ q :* M)
            :=
            (con 2 :* r) :+ q :* (con 2 :* M))
          refl)

    periodic :
      (2 * remainder + quotient * Cylinder.pow2 (suc m))
        % Cylinder.pow2 (suc m)
      ≡ (2 * remainder) % Cylinder.pow2 (suc m)
    periodic =
      [m+kn]%n≡m%n
        (2 * remainder)
        quotient
        (Cylinder.pow2 (suc m))

    doubledRemainderBelow :
      2 * remainder < Cylinder.pow2 (suc m)
    doubledRemainderBelow =
      NatP.*-monoʳ-< 2 (m%n<n y modulus)
  in
  trans
    (cong (_% Cylinder.pow2 (suc m)) doubledDecomposition)
    (trans periodic (m<n⇒m%n≡m doubledRemainderBelow))

candidateLessPow2 :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  Candidate.residueCandidate word < Cylinder.pow2 m
candidateLessPow2 {m} word =
  let
    instance level-nonzero = Pow2.pow2NonZero m
  in
  subst
    (λ value → value < Cylinder.pow2 m)
    (Base.candidateBoundedPaid word)
    (m%n<n (Candidate.residueCandidate word) (Cylinder.pow2 m))

bit0CandidateUnreduced :
  {m : Nat} →
  (tail : Binary.BinaryWord m) →
  Candidate.residueCandidate (Binary.bit0 tail)
  ≡ 2 * Candidate.residueCandidate tail
bit0CandidateUnreduced {m} tail =
  let
    instance next-nonzero = Pow2.pow2NonZero (suc m)
    scaledBelow :
      2 * Candidate.residueCandidate tail < Cylinder.pow2 (suc m)
    scaledBelow = NatP.*-monoʳ-< 2 (candidateLessPow2 tail)
  in
  m<n⇒m%n≡m scaledBelow

------------------------------------------------------------------------
-- Parity recovery from a power-of-two residue known to be even.
------------------------------------------------------------------------

modTwoZeroImpliesParityFalse :
  (x : Syracuse.PositiveNat) →
  Syracuse.toNat x % 2 ≡ 0 →
  Itinerary.parity x ≡ false
modTwoZeroImpliesParityFalse (Syracuse.positiveNat n) remainderZero
  with suc n % 2
... | zero = refl
... | suc r with remainderZero
... | ()

pow2ResidueEvenImpliesModTwoZero :
  {m r : Nat} →
  (x : Syracuse.PositiveNat) →
  Syracuse.toNat x % Cylinder.pow2 (suc m) ≡ 2 * r →
  Syracuse.toNat x % 2 ≡ 0
pow2ResidueEvenImpliesModTwoZero {m} {r} x residue =
  let
    instance next-nonzero = Pow2.pow2NonZero (suc m)

    modulus = Cylinder.pow2 (suc m)
    quotient = Syracuse.toNat x / modulus

    decomposition :
      Syracuse.toNat x
      ≡ Syracuse.toNat x % modulus + quotient * modulus
    decomposition = m≡m%n+[m/n]*n (Syracuse.toNat x) modulus

    replaceResidue :
      Syracuse.toNat x % modulus + quotient * modulus
      ≡ 2 * r + quotient * modulus
    replaceResidue = cong (λ value → value + quotient * modulus) residue

    factorTwo :
      2 * r + quotient * modulus
      ≡ (r + quotient * Cylinder.pow2 m) * 2
    factorTwo =
      solve 3
        (λ r q M →
          (con 2 :* r) :+ q :* (con 2 :* M)
          :=
          (r :+ q :* M) :* con 2)
        refl
  in
  trans
    (cong (_% 2) decomposition)
    (trans
      (cong (_% 2) replaceResidue)
      (trans
        (cong (_% 2) factorTwo)
        (m*n%n≡0 (r + quotient * Cylinder.pow2 m) 2)))

------------------------------------------------------------------------
-- The two even one-step fields required by the generic cylinder compiler.
------------------------------------------------------------------------

bit0ForwardPaid :
  {m : Nat} →
  (tail : Binary.BinaryWord m) →
  (x : Syracuse.PositiveNat) →
  Itinerary.parityWord (suc m) x ≡ Binary.bit0 tail →
  Syracuse.toNat (Syracuse.shortcutSyracuse x) % Cylinder.pow2 m
    ≡ Candidate.residueCandidate tail →
  Syracuse.toNat x % Cylinder.pow2 (suc m)
    ≡ Candidate.residueCandidate (Binary.bit0 tail)
bit0ForwardPaid {m} tail x whole tailResidue with Itinerary.parity x
... | true with whole
... | ()
... | false =
  let
    stepExact = OneStep.evenStepExact x refl
    doubled = doubleModuloPow2 m (Syracuse.toNat (Syracuse.shortcutSyracuse x))
  in
  trans
    (cong (_% Cylinder.pow2 (suc m)) (sym stepExact))
    (trans
      doubled
      (trans
        (cong (2 *_) tailResidue)
        (sym (bit0CandidateUnreduced tail))))

bit0ReversePaid :
  {m : Nat} →
  (tail : Binary.BinaryWord m) →
  (x : Syracuse.PositiveNat) →
  Syracuse.toNat x % Cylinder.pow2 (suc m)
    ≡ Candidate.residueCandidate (Binary.bit0 tail) →
  (Itinerary.parity x ≡ false)
  ×
  (Syracuse.toNat (Syracuse.shortcutSyracuse x) % Cylinder.pow2 m
    ≡ Candidate.residueCandidate tail)
bit0ReversePaid {m} tail x residue =
  let
    residueEven :
      Syracuse.toNat x % Cylinder.pow2 (suc m)
      ≡ 2 * Candidate.residueCandidate tail
    residueEven = trans residue (bit0CandidateUnreduced tail)

    parityFalse : Itinerary.parity x ≡ false
    parityFalse =
      modTwoZeroImpliesParityFalse x
        (pow2ResidueEvenImpliesModTwoZero x residueEven)

    stepExact = OneStep.evenStepExact x parityFalse
    doubled = doubleModuloPow2 m (Syracuse.toNat (Syracuse.shortcutSyracuse x))

    scaledTailEquality :
      2 * (Syracuse.toNat (Syracuse.shortcutSyracuse x) % Cylinder.pow2 m)
      ≡ 2 * Candidate.residueCandidate tail
    scaledTailEquality =
      trans
        (sym doubled)
        (trans
          (cong (_% Cylinder.pow2 (suc m)) stepExact)
          residueEven)

    tailEquality :
      Syracuse.toNat (Syracuse.shortcutSyracuse x) % Cylinder.pow2 m
      ≡ Candidate.residueCandidate tail
    tailEquality =
      NatP.*-cancelˡ-≡
        (Syracuse.toNat (Syracuse.shortcutSyracuse x) % Cylinder.pow2 m)
        (Candidate.residueCandidate tail)
        2
        scaledTailEquality
  in
  parityFalse , tailEquality

record EvenBranchBoundary : Set where
  constructor evenBranchBoundary
  field
    literalEvenStepOwned : Nat
    doubleResidueTransportOwned : Nat
    evenForwardCylinderOwned : Nat
    evenReverseCylinderOwned : Nat
    inverseThreeUsed : Nat

canonicalEvenBranchBoundary : EvenBranchBoundary
canonicalEvenBranchBoundary = evenBranchBoundary 1 1 1 1 0
