module DASHI.NumberTheory.Collatz.SyracuseParityCylinderOddBranchExact where

------------------------------------------------------------------------
-- EXACT ODD-BRANCH PARITY-CYLINDER TRANSPORT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _-_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (_≤_; _<_; z≤n; s≤s)
open import Data.Nat.Base using (NonZero; nonZero)
open import Data.Nat.DivMod using (_%_; [m+n]%n≡m%n; m*n%n≡0; n%n≡0)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderExact as Cylinder
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderCandidateExact as Candidate
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderOneStepBaseExact as Base
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderEvenBranchExact as Even
import DASHI.NumberTheory.Collatz.SyracusePow2ArithmeticExact as Pow2
import DASHI.NumberTheory.Collatz.SyracuseOneStepArithmeticExact as OneStep
import DASHI.NumberTheory.Collatz.SyracuseInv3Pow2Exact as Inv3
import DASHI.NumberTheory.Collatz.SyracuseNatModCongruenceExact as Mod
import DASHI.NumberTheory.Collatz.SyracuseParityCylinderOddResidualExact as Residual

instance
  nonZeroTwo : NonZero 2
  nonZeroTwo = nonZero

------------------------------------------------------------------------
-- Generic helpers at level m+1.
------------------------------------------------------------------------

inverseThreeLeft :
  (m : Nat) →
  let modulus = Cylinder.pow2 (suc m)
      inverse = Candidate.inv3Candidate (suc m)
  in
  (3 * inverse) Mod.≈[ modulus ] 1
inverseThreeLeft m = Inv3.inverseLaw (suc m)

inverseThreeRight :
  (m : Nat) →
  let modulus = Cylinder.pow2 (suc m)
      inverse = Candidate.inv3Candidate (suc m)
  in
  (inverse * 3) Mod.≈[ modulus ] 1
inverseThreeRight m =
  let
    modulus = Cylinder.pow2 (suc m)
    inverse = Candidate.inv3Candidate (suc m)
  in
  Mod.modTrans
    (Mod.fromEquality (NatP.*-comm inverse 3))
    (inverseThreeLeft m)

oneHasAdditiveInverse :
  (m : Nat) →
  let modulus = Cylinder.pow2 (suc m)
  in
  (1 + (modulus - 1)) Mod.≈[ modulus ] 0
oneHasAdditiveInverse m =
  let
    instance modulus-nonzero = Pow2.pow2NonZero (suc m)
    modulus = Cylinder.pow2 (suc m)

    oneLeModulus : 1 ≤ modulus
    oneLeModulus = Pow2.pow2Positive (suc m)

    restores : 1 + (modulus - 1) ≡ modulus
    restores = NatP.m+[n∸m]≡n oneLeModulus
  in
  Mod.modTrans
    (Mod.fromEquality restores)
    (trans (n%n≡0 modulus) refl)

cancelPlusOne :
  {m left right : Nat} →
  (left + 1) Mod.≈[ Cylinder.pow2 (suc m) ] (right + 1) →
  left Mod.≈[ Cylinder.pow2 (suc m) ] right
cancelPlusOne {m} relation =
  let instance modulus-nonzero = Pow2.pow2NonZero (suc m)
  in Mod.addCancelRightWithInverse (oneHasAdditiveInverse m) relation

cancelTimesThree :
  {m left right : Nat} →
  (3 * left) Mod.≈[ Cylinder.pow2 (suc m) ] (3 * right) →
  left Mod.≈[ Cylinder.pow2 (suc m) ] right
cancelTimesThree {m} relation =
  let instance modulus-nonzero = Pow2.pow2NonZero (suc m)
  in Mod.unitCancelLeft (inverseThreeRight m) relation

projectCylinderCongruenceToModTwo :
  {m left right : Nat} →
  left Mod.≈[ Cylinder.pow2 (suc m) ] right →
  left Mod.≈[ 2 ] right
projectCylinderCongruenceToModTwo {m} {left} {right} relation =
  trans
    (sym (Pow2.pow2RemainderPreservesModTwo m left))
    (trans
      (cong (_% 2) relation)
      (Pow2.pow2RemainderPreservesModTwo m right))

------------------------------------------------------------------------
-- The recursive odd residue candidate satisfies 3c+1 = 2r modulo 2^(m+1).
------------------------------------------------------------------------

oddCandidateEquation :
  {m : Nat} →
  (tail : Binary.BinaryWord m) →
  let modulus = Cylinder.pow2 (suc m)
      r = Candidate.residueCandidate tail
      c = Candidate.residueCandidate (Binary.bit1 tail)
  in
  (3 * c + 1) Mod.≈[ modulus ] (2 * r)
oddCandidateEquation {m} tail =
  let
    instance modulus-nonzero = Pow2.pow2NonZero (suc m)
    modulus = Cylinder.pow2 (suc m)
    inverse = Candidate.inv3Candidate (suc m)
    r = Candidate.residueCandidate tail
    rawPredecessor = (2 * r + modulus) - 1
    raw = inverse * rawPredecessor
    c = Candidate.residueCandidate (Binary.bit1 tail)

    cIsRawModulo : c Mod.≈[ modulus ] raw
    cIsRawModulo = Base.candidateBoundedPaid (Binary.bit1 tail)

    threeCToThreeRaw :
      (3 * c) Mod.≈[ modulus ] (3 * raw)
    threeCToThreeRaw = Mod.mulLeftCongruence cIsRawModulo

    reassociate :
      (3 * raw) Mod.≈[ modulus ] ((3 * inverse) * rawPredecessor)
    reassociate =
      Mod.fromEquality (NatP.*-assoc 3 inverse rawPredecessor)

    cancelInverse :
      ((3 * inverse) * rawPredecessor)
      Mod.≈[ modulus ]
      rawPredecessor
    cancelInverse =
      Mod.modTrans
        (Mod.mulCongruence (inverseThreeLeft m) Mod.modRefl)
        (Mod.fromEquality (NatP.*-identityˡ rawPredecessor))

    threeCToPredecessor :
      (3 * c) Mod.≈[ modulus ] rawPredecessor
    threeCToPredecessor =
      Mod.modTrans threeCToThreeRaw
        (Mod.modTrans reassociate cancelInverse)

    addOne :
      (3 * c + 1) Mod.≈[ modulus ] (rawPredecessor + 1)
    addOne = Mod.addRightCongruence threeCToPredecessor

    totalPositive : 1 ≤ 2 * r + modulus
    totalPositive =
      NatP.≤-trans
        (Pow2.pow2Positive (suc m))
        (NatP.n≤m+n modulus (2 * r))

    predecessorRestores : rawPredecessor + 1 ≡ 2 * r + modulus
    predecessorRestores = NatP.m∸n+n≡m totalPositive

    removeModulus :
      (2 * r + modulus) Mod.≈[ modulus ] (2 * r)
    removeModulus = [m+n]%n≡m%n (2 * r) modulus
  in
  Mod.modTrans addOne
    (Mod.modTrans (Mod.fromEquality predecessorRestores) removeModulus)

------------------------------------------------------------------------
-- Tail residues lift by doubling from 2^m to 2^(m+1).
------------------------------------------------------------------------

doubledTailCongruence :
  {m : Nat} →
  (tail : Binary.BinaryWord m) →
  (y : Nat) →
  y % Cylinder.pow2 m ≡ Candidate.residueCandidate tail →
  (2 * y) Mod.≈[ Cylinder.pow2 (suc m) ]
    (2 * Candidate.residueCandidate tail)
doubledTailCongruence {m} tail y tailResidue =
  trans
    (Even.doubleModuloPow2 m y)
    (trans
      (cong (2 *_) tailResidue)
      (sym (Even.bit0CandidateUnreduced tail)))

------------------------------------------------------------------------
-- Odd forward transport.
------------------------------------------------------------------------

bit1ForwardPaid :
  {m : Nat} →
  (tail : Binary.BinaryWord m) →
  (x : Syracuse.PositiveNat) →
  Itinerary.parityWord (suc m) x ≡ Binary.bit1 tail →
  Syracuse.toNat (Syracuse.shortcutSyracuse x) % Cylinder.pow2 m
    ≡ Candidate.residueCandidate tail →
  Syracuse.toNat x % Cylinder.pow2 (suc m)
    ≡ Candidate.residueCandidate (Binary.bit1 tail)
bit1ForwardPaid {m} tail x whole tailResidue with Itinerary.parity x
... | false with whole
... | ()
... | true =
  let
    instance modulus-nonzero = Pow2.pow2NonZero (suc m)
    y = Syracuse.toNat (Syracuse.shortcutSyracuse x)
    r = Candidate.residueCandidate tail
    c = Candidate.residueCandidate (Binary.bit1 tail)

    branchEquation :
      (3 * Syracuse.toNat x + 1)
      Mod.≈[ Cylinder.pow2 (suc m) ]
      (2 * y)
    branchEquation = Mod.fromEquality (sym (OneStep.oddStepExact x refl))

    actualEquation :
      (3 * Syracuse.toNat x + 1)
      Mod.≈[ Cylinder.pow2 (suc m) ]
      (2 * r)
    actualEquation =
      Mod.modTrans branchEquation
        (doubledTailCongruence tail y tailResidue)

    sameTranslatedThree :
      (3 * Syracuse.toNat x + 1)
      Mod.≈[ Cylinder.pow2 (suc m) ]
      (3 * c + 1)
    sameTranslatedThree =
      Mod.modTrans actualEquation (Mod.modSym (oddCandidateEquation tail))

    sameThree :
      (3 * Syracuse.toNat x)
      Mod.≈[ Cylinder.pow2 (suc m) ]
      (3 * c)
    sameThree = cancelPlusOne sameTranslatedThree

    sameResidue :
      Syracuse.toNat x Mod.≈[ Cylinder.pow2 (suc m) ] c
    sameResidue = cancelTimesThree sameThree
  in
  trans sameResidue (Base.candidateBoundedPaid (Binary.bit1 tail))

------------------------------------------------------------------------
-- Reverse parity recovery and tail transport.
------------------------------------------------------------------------

parityMustBeTrueFromOddEquation :
  {m : Nat} →
  (x : Syracuse.PositiveNat) →
  (r : Nat) →
  (3 * Syracuse.toNat x + 1)
    Mod.≈[ Cylinder.pow2 (suc m) ]
    (2 * r) →
  Itinerary.parity x ≡ true
parityMustBeTrueFromOddEquation {m} x r equation with Itinerary.parity x
... | true = refl
... | false =
  let
    xEven : Syracuse.toNat x Mod.≈[ 2 ] 0
    xEven = OneStep.parityFalseModTwo x refl

    threeXEven :
      (3 * Syracuse.toNat x) Mod.≈[ 2 ] 0
    threeXEven = Mod.mulLeftCongruence xEven

    translatedIsOne :
      (3 * Syracuse.toNat x + 1) Mod.≈[ 2 ] 1
    translatedIsOne =
      Mod.modTrans
        (Mod.addRightCongruence threeXEven)
        (Mod.fromEquality refl)

    projectedEquation :
      (3 * Syracuse.toNat x + 1) Mod.≈[ 2 ] (2 * r)
    projectedEquation = projectCylinderCongruenceToModTwo equation

    rightIsZero : (2 * r) Mod.≈[ 2 ] 0
    rightIsZero =
      Mod.modTrans
        (Mod.fromEquality (NatP.*-comm 2 r))
        (trans (m*n%n≡0 r 2) refl)

    oneEqualsZero : 1 % 2 ≡ 0 % 2
    oneEqualsZero =
      Mod.modTrans
        (Mod.modSym translatedIsOne)
        (Mod.modTrans projectedEquation rightIsZero)
  in
  ⊥-elim (λ () → oneEqualsZero)

bit1ReversePaid :
  {m : Nat} →
  (tail : Binary.BinaryWord m) →
  (x : Syracuse.PositiveNat) →
  Syracuse.toNat x % Cylinder.pow2 (suc m)
    ≡ Candidate.residueCandidate (Binary.bit1 tail) →
  (Itinerary.parity x ≡ true)
  ×
  (Syracuse.toNat (Syracuse.shortcutSyracuse x) % Cylinder.pow2 m
    ≡ Candidate.residueCandidate tail)
bit1ReversePaid {m} tail x residue =
  let
    instance modulus-nonzero = Pow2.pow2NonZero (suc m)
    c = Candidate.residueCandidate (Binary.bit1 tail)
    r = Candidate.residueCandidate tail
    y = Syracuse.toNat (Syracuse.shortcutSyracuse x)

    xToCandidate :
      Syracuse.toNat x Mod.≈[ Cylinder.pow2 (suc m) ] c
    xToCandidate =
      trans residue (sym (Base.candidateBoundedPaid (Binary.bit1 tail)))

    threeRelation :
      (3 * Syracuse.toNat x)
      Mod.≈[ Cylinder.pow2 (suc m) ]
      (3 * c)
    threeRelation = Mod.mulLeftCongruence xToCandidate

    translatedRelation :
      (3 * Syracuse.toNat x + 1)
      Mod.≈[ Cylinder.pow2 (suc m) ]
      (3 * c + 1)
    translatedRelation = Mod.addRightCongruence threeRelation

    actualEquation :
      (3 * Syracuse.toNat x + 1)
      Mod.≈[ Cylinder.pow2 (suc m) ]
      (2 * r)
    actualEquation =
      Mod.modTrans translatedRelation (oddCandidateEquation tail)

    parityTrue : Itinerary.parity x ≡ true
    parityTrue = parityMustBeTrueFromOddEquation x r actualEquation

    branchEquation :
      (2 * y) Mod.≈[ Cylinder.pow2 (suc m) ]
      (3 * Syracuse.toNat x + 1)
    branchEquation = Mod.fromEquality (OneStep.oddStepExact x parityTrue)

    doubledTail :
      (2 * y) Mod.≈[ Cylinder.pow2 (suc m) ] (2 * r)
    doubledTail = Mod.modTrans branchEquation actualEquation

    leftDouble :
      (2 * y) % Cylinder.pow2 (suc m)
      ≡ 2 * (y % Cylinder.pow2 m)
    leftDouble = Even.doubleModuloPow2 m y

    rightDouble :
      (2 * r) % Cylinder.pow2 (suc m) ≡ 2 * r
    rightDouble = Even.bit0CandidateUnreduced tail

    scaledTailEquality :
      2 * (y % Cylinder.pow2 m) ≡ 2 * r
    scaledTailEquality =
      trans (sym leftDouble)
        (trans doubledTail rightDouble)

    tailResidue :
      y % Cylinder.pow2 m ≡ r
    tailResidue =
      NatP.*-cancelˡ-≡
        (y % Cylinder.pow2 m)
        r
        2
        scaledTailEquality
  in
  parityTrue , tailResidue

canonicalOddCylinderResidual : Residual.OddCylinderResidual
canonicalOddCylinderResidual = record
  { Residual.bit1Forward = bit1ForwardPaid
  ; Residual.bit1Reverse = bit1ReversePaid
  }

canonicalParityCylinderSource : Cylinder.ParityCylinderSource
canonicalParityCylinderSource =
  Residual.compileParityCylinderSource canonicalOddCylinderResidual

record OddBranchBoundary : Set where
  constructor oddBranchBoundary
  field
    oddCandidateEquationOwned : Nat
    oddForwardOwned : Nat
    oddReverseOwned : Nat
    parityRecoveredFromSameEquation : Nat
    fullParityCylinderSourceConstructed : Nat

canonicalOddBranchBoundary : OddBranchBoundary
canonicalOddBranchBoundary = oddBranchBoundary 1 1 1 1 1
