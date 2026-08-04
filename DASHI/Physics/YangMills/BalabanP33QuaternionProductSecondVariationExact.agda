module DASHI.Physics.YangMills.BalabanP33QuaternionProductSecondVariationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Prove the noncommutative product-rule expansion required by the literal
-- four-link Wilson plaquette Hessian on DASHI's concrete quaternion carrier.
-- For each link we retain its value, first variation and second variation.
-- The recursive second derivative of an ordered product is exactly the sum of
--
--   n diagonal second-variation terms
--     + n(n-1) ordered first/first terms.
--
-- For n=4 this gives 4+12=16 concrete quaternion atoms.  The equality is not
-- a count-only receipt: finite-list induction, quaternion distributivity and
-- the ordered product rule prove that the sum of the generated atoms equals
-- the recursively differentiated quaternion product.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map; _++_; length)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver using
  (module RealPolynomialSolver)
open import DASHI.Physics.YangMills.BalabanComputedPolynomialSolver using
  (solveComputed; computed)
open RealPolynomialSolver using
  (Polynomial; _:=_; _:+_; _:*_; :-_)
open import DASHI.Physics.YangMills.BalabanQuaternionPolynomialIdentities using
  (q0P; q1P; q2P; q3P)
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier using
  ( Quaternion; quat; q0; q1; q2; q3
  ; zeroQ; oneQ; _+q_; _*q_; quaternionExt
  ; quaternionMultiplyAssociative
  )

------------------------------------------------------------------------
-- Concrete quaternion additive/distributive laws.
------------------------------------------------------------------------

realAddAssociative : ∀ a b c →
  DASHI.Physics.YangMills.BalabanRealPolynomialRing._+R_
    (DASHI.Physics.YangMills.BalabanRealPolynomialRing._+R_ a b) c
  ≡ DASHI.Physics.YangMills.BalabanRealPolynomialRing._+R_
      a (DASHI.Physics.YangMills.BalabanRealPolynomialRing._+R_ b c)
realAddAssociative =
  solveComputed 3
    (λ a b c → (a :+ b) :+ c := a :+ (b :+ c))
    computed

realAddCommutative : ∀ a b →
  DASHI.Physics.YangMills.BalabanRealPolynomialRing._+R_ a b
  ≡ DASHI.Physics.YangMills.BalabanRealPolynomialRing._+R_ b a
realAddCommutative =
  solveComputed 2 (λ a b → a :+ b := b :+ a) computed

quaternionAddAssociative : ∀ a b c →
  (a +q b) +q c ≡ a +q (b +q c)
quaternionAddAssociative
    (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) (quat c0 c1 c2 c3) =
  quaternionExt
    (realAddAssociative a0 b0 c0)
    (realAddAssociative a1 b1 c1)
    (realAddAssociative a2 b2 c2)
    (realAddAssociative a3 b3 c3)

quaternionAddCommutative : ∀ a b → a +q b ≡ b +q a
quaternionAddCommutative
    (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) =
  quaternionExt
    (realAddCommutative a0 b0)
    (realAddCommutative a1 b1)
    (realAddCommutative a2 b2)
    (realAddCommutative a3 b3)

quaternionAddZeroLeft : ∀ a → zeroQ +q a ≡ a
quaternionAddZeroLeft (quat a0 a1 a2 a3) =
  quaternionExt
    (solveComputed 1 (λ a → a := a) computed a0)
    (solveComputed 1 (λ a → a := a) computed a1)
    (solveComputed 1 (λ a → a := a) computed a2)
    (solveComputed 1 (λ a → a := a) computed a3)

quaternionAddZeroRight : ∀ a → a +q zeroQ ≡ a
quaternionAddZeroRight a =
  trans (quaternionAddCommutative a zeroQ) (quaternionAddZeroLeft a)

leftDistributes0 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q0P a0 a1 a2 a3
    (b0 :+ c0) (b1 :+ c1) (b2 :+ c2) (b3 :+ c3)
  ≡ q0P a0 a1 a2 a3 b0 b1 b2 b3
      DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.:+
     q0P a0 a1 a2 a3 c0 c1 c2 c3
leftDistributes0 =
  solveComputed 12
    (λ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
      q0P a0 a1 a2 a3
        (b0 :+ c0) (b1 :+ c1) (b2 :+ c2) (b3 :+ c3)
      := q0P a0 a1 a2 a3 b0 b1 b2 b3
          :+ q0P a0 a1 a2 a3 c0 c1 c2 c3)
    computed

leftDistributes1 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q1P a0 a1 a2 a3
    (b0 :+ c0) (b1 :+ c1) (b2 :+ c2) (b3 :+ c3)
  ≡ q1P a0 a1 a2 a3 b0 b1 b2 b3
      DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.:+
     q1P a0 a1 a2 a3 c0 c1 c2 c3
leftDistributes1 =
  solveComputed 12
    (λ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
      q1P a0 a1 a2 a3
        (b0 :+ c0) (b1 :+ c1) (b2 :+ c2) (b3 :+ c3)
      := q1P a0 a1 a2 a3 b0 b1 b2 b3
          :+ q1P a0 a1 a2 a3 c0 c1 c2 c3)
    computed

leftDistributes2 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q2P a0 a1 a2 a3
    (b0 :+ c0) (b1 :+ c1) (b2 :+ c2) (b3 :+ c3)
  ≡ q2P a0 a1 a2 a3 b0 b1 b2 b3
      DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.:+
     q2P a0 a1 a2 a3 c0 c1 c2 c3
leftDistributes2 =
  solveComputed 12
    (λ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
      q2P a0 a1 a2 a3
        (b0 :+ c0) (b1 :+ c1) (b2 :+ c2) (b3 :+ c3)
      := q2P a0 a1 a2 a3 b0 b1 b2 b3
          :+ q2P a0 a1 a2 a3 c0 c1 c2 c3)
    computed

leftDistributes3 : ∀ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
  q3P a0 a1 a2 a3
    (b0 :+ c0) (b1 :+ c1) (b2 :+ c2) (b3 :+ c3)
  ≡ q3P a0 a1 a2 a3 b0 b1 b2 b3
      DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.:+
     q3P a0 a1 a2 a3 c0 c1 c2 c3
leftDistributes3 =
  solveComputed 12
    (λ a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 →
      q3P a0 a1 a2 a3
        (b0 :+ c0) (b1 :+ c1) (b2 :+ c2) (b3 :+ c3)
      := q3P a0 a1 a2 a3 b0 b1 b2 b3
          :+ q3P a0 a1 a2 a3 c0 c1 c2 c3)
    computed

quaternionMultiplyDistributesLeft : ∀ a b c →
  a *q (b +q c) ≡ (a *q b) +q (a *q c)
quaternionMultiplyDistributesLeft
    (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) (quat c0 c1 c2 c3) =
  quaternionExt
    (leftDistributes0 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3)
    (leftDistributes1 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3)
    (leftDistributes2 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3)
    (leftDistributes3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3)

quaternionMultiplyZeroRight : ∀ a → a *q zeroQ ≡ zeroQ
quaternionMultiplyZeroRight (quat a0 a1 a2 a3) =
  quaternionExt
    (solveComputed 4 (λ a0 a1 a2 a3 →
      q0P a0 a1 a2 a3
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
      := DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
      computed a0 a1 a2 a3)
    (solveComputed 4 (λ a0 a1 a2 a3 →
      q1P a0 a1 a2 a3
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
      := DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
      computed a0 a1 a2 a3)
    (solveComputed 4 (λ a0 a1 a2 a3 →
      q2P a0 a1 a2 a3
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
      := DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
      computed a0 a1 a2 a3)
    (solveComputed 4 (λ a0 a1 a2 a3 →
      q3P a0 a1 a2 a3
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
        (DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
      := DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.RealPolynomialSolver.con
          DASHI.Physics.YangMills.BalabanAxiomaticRealPolynomialSolver.zeroCoefficient)
      computed a0 a1 a2 a3)

------------------------------------------------------------------------
-- Ordered second-jet products and literal atom generation.
------------------------------------------------------------------------

record QuaternionFactorJet : Set where
  constructor factorJet
  field
    factorValue factorFirst factorSecond : Quaternion

open QuaternionFactorJet public

orderedValueProduct : List QuaternionFactorJet → Quaternion
orderedValueProduct [] = oneQ
orderedValueProduct (factor ∷ factors) =
  factorValue factor *q orderedValueProduct factors

orderedFirstProduct : List QuaternionFactorJet → Quaternion
orderedFirstProduct [] = zeroQ
orderedFirstProduct (factor ∷ factors) =
  (factorFirst factor *q orderedValueProduct factors)
  +q (factorValue factor *q orderedFirstProduct factors)

orderedSecondProduct : List QuaternionFactorJet → Quaternion
orderedSecondProduct [] = zeroQ
orderedSecondProduct (factor ∷ factors) =
  (factorSecond factor *q orderedValueProduct factors)
  +q (((factorFirst factor *q orderedFirstProduct factors)
      +q (factorFirst factor *q orderedFirstProduct factors))
    +q (factorValue factor *q orderedSecondProduct factors))

firstVariationTerms : List QuaternionFactorJet → List Quaternion
firstVariationTerms [] = []
firstVariationTerms (factor ∷ factors) =
  (factorFirst factor *q orderedValueProduct factors)
  ∷ map (factorValue factor *q_) (firstVariationTerms factors)

secondVariationTerms : List QuaternionFactorJet → List Quaternion
secondVariationTerms [] = []
secondVariationTerms (factor ∷ factors) =
  (factorSecond factor *q orderedValueProduct factors)
  ∷ (map (factorFirst factor *q_) (firstVariationTerms factors)
    ++ (map (factorFirst factor *q_) (firstVariationTerms factors)
      ++ map (factorValue factor *q_) (secondVariationTerms factors)))

sumQuaternion : List Quaternion → Quaternion
sumQuaternion [] = zeroQ
sumQuaternion (value ∷ values) = value +q sumQuaternion values

sumQuaternionAppend : ∀ left right →
  sumQuaternion (left ++ right)
  ≡ sumQuaternion left +q sumQuaternion right
sumQuaternionAppend [] right = sym (quaternionAddZeroLeft (sumQuaternion right))
sumQuaternionAppend (value ∷ values) right =
  trans
    (cong (value +q_) (sumQuaternionAppend values right))
    (sym
      (quaternionAddAssociative
        value (sumQuaternion values) (sumQuaternion right)))

sumQuaternionMapLeftMultiply : ∀ multiplier values →
  sumQuaternion (map (multiplier *q_) values)
  ≡ multiplier *q sumQuaternion values
sumQuaternionMapLeftMultiply multiplier [] =
  sym (quaternionMultiplyZeroRight multiplier)
sumQuaternionMapLeftMultiply multiplier (value ∷ values) =
  trans
    (cong
      (multiplier *q value +q_)
      (sumQuaternionMapLeftMultiply multiplier values))
    (sym
      (quaternionMultiplyDistributesLeft
        multiplier value (sumQuaternion values)))

sumFirstVariationTermsExact : ∀ factors →
  sumQuaternion (firstVariationTerms factors)
  ≡ orderedFirstProduct factors
sumFirstVariationTermsExact [] = refl
sumFirstVariationTermsExact (factor ∷ factors) =
  trans
    (cong
      (factorFirst factor *q orderedValueProduct factors +q_)
      (sumQuaternionMapLeftMultiply
        (factorValue factor) (firstVariationTerms factors)))
    (cong
      (factorFirst factor *q orderedValueProduct factors +q_)
      (cong (factorValue factor *q_)
        (sumFirstVariationTermsExact factors)))

sumSecondVariationTermsExact : ∀ factors →
  sumQuaternion (secondVariationTerms factors)
  ≡ orderedSecondProduct factors
sumSecondVariationTermsExact [] = refl
sumSecondVariationTermsExact (factor ∷ factors) =
  trans
    (cong
      (factorSecond factor *q orderedValueProduct factors +q_)
      (sumQuaternionAppend
        (map (factorFirst factor *q_) (firstVariationTerms factors))
        (map (factorFirst factor *q_) (firstVariationTerms factors)
          ++ map (factorValue factor *q_) (secondVariationTerms factors))))
    (trans
      (cong
        (factorSecond factor *q orderedValueProduct factors +q_)
        (cong₂ _+q_
          (sumQuaternionMapLeftMultiply
            (factorFirst factor) (firstVariationTerms factors))
          (trans
            (sumQuaternionAppend
              (map (factorFirst factor *q_) (firstVariationTerms factors))
              (map (factorValue factor *q_) (secondVariationTerms factors)))
            (cong₂ _+q_
              (sumQuaternionMapLeftMultiply
                (factorFirst factor) (firstVariationTerms factors))
              (sumQuaternionMapLeftMultiply
                (factorValue factor) (secondVariationTerms factors))))))
      (cong
        (factorSecond factor *q orderedValueProduct factors +q_)
        (cong₂ _+q_
          (cong (factorFirst factor *q_)
            (sumFirstVariationTermsExact factors))
          (cong₂ _+q_
            (cong (factorFirst factor *q_)
              (sumFirstVariationTermsExact factors))
            (cong (factorValue factor *q_)
              (sumSecondVariationTermsExact factors)))))))

fourFactorJets :
  QuaternionFactorJet → QuaternionFactorJet →
  QuaternionFactorJet → QuaternionFactorJet →
  List QuaternionFactorJet
fourFactorJets first second third fourth =
  first ∷ second ∷ third ∷ fourth ∷ []

fourFactorSecondVariationAtomCountExact :
  ∀ first second third fourth →
  length (secondVariationTerms
    (fourFactorJets first second third fourth)) ≡ 16
fourFactorSecondVariationAtomCountExact first second third fourth = refl

fourFactorSecondVariationIsSixteenAtomSum :
  ∀ first second third fourth →
  sumQuaternion
    (secondVariationTerms
      (fourFactorJets first second third fourth))
  ≡ orderedSecondProduct
      (fourFactorJets first second third fourth)
fourFactorSecondVariationIsSixteenAtomSum first second third fourth =
  sumSecondVariationTermsExact
    (fourFactorJets first second third fourth)

quaternionAdditiveDistributiveLevel : ProofLevel
quaternionAdditiveDistributiveLevel = machineChecked

orderedQuaternionSecondVariationExpansionLevel : ProofLevel
orderedQuaternionSecondVariationExpansionLevel = machineChecked

fourLinkWilsonSixteenQuaternionAtomLevel : ProofLevel
fourLinkWilsonSixteenQuaternionAtomLevel = machineChecked
