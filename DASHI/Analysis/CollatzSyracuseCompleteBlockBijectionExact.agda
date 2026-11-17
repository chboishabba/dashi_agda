module DASHI.Analysis.CollatzSyracuseCompleteBlockBijectionExact where

------------------------------------------------------------------------
-- CANONICAL COMPLETE INTEGER BLOCK <-> PARITY WORD BIJECTION
--
-- `Fin (2^m)` is interpreted as a residue coordinate.  Residue 0 is represented
-- by the positive start 2^m; every nonzero residue r is represented by r.
-- Thus the literal start set is exactly {1,...,2^m}, only cyclically ordered by
-- residue.  The inverse word index is the proved parity-cylinder residue.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin; fromℕ<; toℕ)
import Data.Fin.Properties as FinP
open import Data.Nat.DivMod using (_%_; m<n⇒m%n≡m)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.Core.FiniteUniformBijectionTransportExact as Uniform
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderCandidateExact as Candidate
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderEvenBranchExact as Even
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderRepresentativeExact as Representative
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderOddBranchExact as Odd
import DASHI.NumberTheory.Collatz.SyracusePow2ArithmeticExact as Pow2

indexResidueBounded :
  {m : Nat} →
  (index : Fin (Cylinder.pow2 m)) →
  toℕ index % Cylinder.pow2 m ≡ toℕ index
indexResidueBounded {m} index =
  let instance modulus-nonzero = Pow2.pow2NonZero m
  in m<n⇒m%n≡m (FinP.toℕ<n index)

blockStart :
  {m : Nat} →
  Fin (Cylinder.pow2 m) →
  Syracuse.PositiveNat
blockStart index =
  Representative.positiveRepresentative
    (toℕ index)
    (indexResidueBounded index)

blockStartResidue :
  {m : Nat} →
  (index : Fin (Cylinder.pow2 m)) →
  Syracuse.toNat (blockStart index) % Cylinder.pow2 m ≡ toℕ index
blockStartResidue index =
  Representative.positiveRepresentativeResidue
    (toℕ index)
    (indexResidueBounded index)

blockWord :
  {m : Nat} →
  Fin (Cylinder.pow2 m) →
  Binary.BinaryWord m
blockWord {m} index = Itinerary.parityWord m (blockStart index)

inverseWordIndex :
  {m : Nat} →
  Binary.BinaryWord m →
  Fin (Cylinder.pow2 m)
inverseWordIndex word = fromℕ< (Even.candidateLessPow2 word)

inverseWordIndexToNat :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  toℕ (inverseWordIndex word) ≡ Candidate.residueCandidate word
inverseWordIndexToNat word = FinP.toℕ-fromℕ< (Even.candidateLessPow2 word)

inverseWordRoundTrip :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  blockWord (inverseWordIndex word) ≡ word
inverseWordRoundTrip {m} word =
  let
    index = inverseWordIndex word

    residue :
      Syracuse.toNat (blockStart index) % Cylinder.pow2 m
      ≡ Candidate.residueCandidate word
    residue =
      trans
        (blockStartResidue index)
        (inverseWordIndexToNat word)
  in
  Cylinder.residueImpliesParityWord
    Odd.canonicalParityCylinderSource
    word
    (blockStart index)
    residue

indexRoundTrip :
  {m : Nat} →
  (index : Fin (Cylinder.pow2 m)) →
  inverseWordIndex (blockWord index) ≡ index
indexRoundTrip {m} index =
  FinP.toℕ-injective toNatEquality
  where
  source = Odd.canonicalParityCylinderSource

  forward :
    Syracuse.toNat (blockStart index) % Cylinder.pow2 m
    ≡ Candidate.residueCandidate (blockWord index)
  forward =
    Cylinder.parityWordImpliesResidue
      source
      (blockWord index)
      (blockStart index)
      refl

  candidateIsIndex :
    Candidate.residueCandidate (blockWord index) ≡ toℕ index
  candidateIsIndex =
    trans (sym forward) (blockStartResidue index)

  toNatEquality :
    toℕ (inverseWordIndex (blockWord index)) ≡ toℕ index
  toNatEquality =
    trans
      (inverseWordIndexToNat (blockWord index))
      candidateIsIndex

record CompleteBlockWordIndexSource (m : Nat) : Set₁ where
  field
    wordIndex : Binary.BinaryWord m → Fin (Cylinder.pow2 m)
    indexWordIndex :
      (index : Fin (Cylinder.pow2 m)) →
      wordIndex (blockWord index) ≡ index
    wordIndexWord :
      (word : Binary.BinaryWord m) →
      blockWord (wordIndex word) ≡ word

open CompleteBlockWordIndexSource public

canonicalCompleteBlockSource :
  (m : Nat) →
  CompleteBlockWordIndexSource m
canonicalCompleteBlockSource m = record
  { wordIndex = inverseWordIndex
  ; indexWordIndex = indexRoundTrip
  ; wordIndexWord = inverseWordRoundTrip
  }

completeBlockWordBijection :
  {m : Nat} →
  CompleteBlockWordIndexSource m →
  Uniform.ExplicitBijection
    (Fin (Cylinder.pow2 m))
    (Binary.BinaryWord m)
completeBlockWordBijection source = record
  { Uniform.to = blockWord
  ; Uniform.from = wordIndex source
  ; Uniform.fromTo = indexWordIndex source
  ; Uniform.toFrom = wordIndexWord source
  }

completeBlockUniformWordMass :
  {m : Nat} →
  CompleteBlockWordIndexSource m →
  Uniform.UniformNatMass (Binary.BinaryWord m)
completeBlockUniformWordMass source =
  Uniform.transportUnitMass (completeBlockWordBijection source)

canonicalCompleteBlockUniformWordMass :
  (m : Nat) →
  Uniform.UniformNatMass (Binary.BinaryWord m)
canonicalCompleteBlockUniformWordMass m =
  completeBlockUniformWordMass (canonicalCompleteBlockSource m)

record CompleteBlockBijectionBoundary : Set where
  constructor completeBlockBijectionBoundary
  field
    literalStartsOneThroughPow2 : Nat
    residueOrderedBlock : Nat
    forwardWordMapOwned : Nat
    inverseIndexOwned : Nat
    twoRoundTripsOwned : Nat
    exactUniformTransportGeneric : Nat
    spectralMixingRequired : Nat

canonicalCompleteBlockBijectionBoundary : CompleteBlockBijectionBoundary
canonicalCompleteBlockBijectionBoundary =
  completeBlockBijectionBoundary 1 1 1 1 1 1 0
