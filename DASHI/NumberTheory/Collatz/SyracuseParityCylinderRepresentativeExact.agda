module DASHI.NumberTheory.Collatz.SyracuseParityCylinderRepresentativeExact where

------------------------------------------------------------------------
-- POSITIVE REPRESENTATIVES AND DERIVED RESIDUE-CODE INJECTIVITY
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.DivMod using (_%_; n%n≡0)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderCandidateExact as Candidate
import DASHI.NumberTheory.Collatz.SyracusePow2ArithmeticExact as Pow2

positiveRepresentative :
  {m : Nat} →
  (r : Nat) →
  r % Cylinder.pow2 m ≡ r →
  Syracuse.PositiveNat
positiveRepresentative {m} zero bounded with Pow2.pow2IsSuccessor m
... | predecessor , modulusShape = Syracuse.positiveNat predecessor
positiveRepresentative (suc r) bounded = Syracuse.positiveNat r

positiveRepresentativeResidue :
  {m : Nat} →
  (r : Nat) →
  (bounded : r % Cylinder.pow2 m ≡ r) →
  Syracuse.toNat (positiveRepresentative r bounded) % Cylinder.pow2 m ≡ r
positiveRepresentativeResidue {m} zero bounded with Pow2.pow2IsSuccessor m
... | predecessor , modulusShape =
  let
    instance modulus-nonzero = Pow2.pow2NonZero m
  in
  trans
    (subst
      (λ modulus → modulus % Cylinder.pow2 m ≡ zero)
      modulusShape
      (n%n≡0 (Cylinder.pow2 m)))
    refl
positiveRepresentativeResidue (suc r) bounded = bounded

candidateInjectiveFromReverse :
  (candidateBounded :
    {m : Nat} →
    (word : Binary.BinaryWord m) →
    Candidate.residueCandidate word % Cylinder.pow2 m
      ≡ Candidate.residueCandidate word) →
  (reverseClassification :
    {m : Nat} →
    (word : Binary.BinaryWord m) →
    (x : Syracuse.PositiveNat) →
    Syracuse.toNat x % Cylinder.pow2 m
      ≡ Candidate.residueCandidate word →
    Itinerary.parityWord m x ≡ word) →
  {m : Nat} →
  (left right : Binary.BinaryWord m) →
  Candidate.residueCandidate left ≡ Candidate.residueCandidate right →
  left ≡ right
candidateInjectiveFromReverse candidateBounded reverseClassification {m} left right candidatesEqual =
  let
    boundedLeft = candidateBounded left
    x = positiveRepresentative (Candidate.residueCandidate left) boundedLeft
    xResidueLeft = positiveRepresentativeResidue
      (Candidate.residueCandidate left) boundedLeft

    xResidueRight :
      Syracuse.toNat x % Cylinder.pow2 m
      ≡ Candidate.residueCandidate right
    xResidueRight = trans xResidueLeft candidatesEqual

    leftWord = reverseClassification left x xResidueLeft
    rightWord = reverseClassification right x xResidueRight
  in
  trans (sym leftWord) rightWord

record RepresentativeBoundary : Set where
  constructor representativeBoundary
  field
    zeroResidueGetsPositiveRepresentative : Nat
    nonzeroResidueGetsLiteralRepresentative : Nat
    reverseClassificationImpliesCodeInjective : Nat
    independentRecursiveInjectivityRequired : Nat

canonicalRepresentativeBoundary : RepresentativeBoundary
canonicalRepresentativeBoundary = representativeBoundary 1 1 1 0
