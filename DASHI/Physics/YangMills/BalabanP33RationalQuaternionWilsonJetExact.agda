module DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonJetExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map; _++_; length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionCoreExact public
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionAlgebraLawsExact public

record QuaternionFactorJet : Set where
  constructor factorJet
  field
    factorValue factorFirst factorSecond : RationalQuaternion

open QuaternionFactorJet public

orderedValueProduct : List QuaternionFactorJet → RationalQuaternion
orderedValueProduct [] = oneQ
orderedValueProduct (factor ∷ factors) =
  factorValue factor *q orderedValueProduct factors

orderedFirstProduct : List QuaternionFactorJet → RationalQuaternion
orderedFirstProduct [] = zeroQ
orderedFirstProduct (factor ∷ factors) =
  (factorFirst factor *q orderedValueProduct factors)
  +q (factorValue factor *q orderedFirstProduct factors)

orderedSecondProduct : List QuaternionFactorJet → RationalQuaternion
orderedSecondProduct [] = zeroQ
orderedSecondProduct (factor ∷ factors) =
  (factorSecond factor *q orderedValueProduct factors)
  +q (((factorFirst factor *q orderedFirstProduct factors)
      +q (factorFirst factor *q orderedFirstProduct factors))
    +q (factorValue factor *q orderedSecondProduct factors))

firstVariationTerms : List QuaternionFactorJet → List RationalQuaternion
firstVariationTerms [] = []
firstVariationTerms (factor ∷ factors) =
  (factorFirst factor *q orderedValueProduct factors)
  ∷ map (factorValue factor *q_) (firstVariationTerms factors)

secondVariationTerms : List QuaternionFactorJet → List RationalQuaternion
secondVariationTerms [] = []
secondVariationTerms (factor ∷ factors) =
  (factorSecond factor *q orderedValueProduct factors)
  ∷ (map (factorFirst factor *q_) (firstVariationTerms factors)
    ++ (map (factorFirst factor *q_) (firstVariationTerms factors)
      ++ map (factorValue factor *q_) (secondVariationTerms factors)))

sumQuaternion : List RationalQuaternion → RationalQuaternion
sumQuaternion [] = zeroQ
sumQuaternion (value ∷ values) = value +q sumQuaternion values

sumQuaternionAppend : ∀ left right →
  sumQuaternion (left ++ right)
  ≡ sumQuaternion left +q sumQuaternion right
sumQuaternionAppend [] right = sym (quaternionAddZeroLeft (sumQuaternion right))
sumQuaternionAppend (value ∷ values) right =
  trans
    (cong (value +q_) (sumQuaternionAppend values right))
    (sym (quaternionAddAssociative
      value (sumQuaternion values) (sumQuaternion right)))

sumQuaternionMapLeftMultiply : ∀ multiplier values →
  sumQuaternion (map (multiplier *q_) values)
  ≡ multiplier *q sumQuaternion values
sumQuaternionMapLeftMultiply multiplier [] =
  sym (quaternionMultiplyZeroRight multiplier)
sumQuaternionMapLeftMultiply multiplier (value ∷ values) =
  trans
    (cong ((multiplier *q value) +q_)
      (sumQuaternionMapLeftMultiply multiplier values))
    (sym (quaternionMultiplyDistributesLeft
      multiplier value (sumQuaternion values)))

sumFirstVariationTermsExact : ∀ factors →
  sumQuaternion (firstVariationTerms factors)
  ≡ orderedFirstProduct factors
sumFirstVariationTermsExact [] = refl
sumFirstVariationTermsExact (factor ∷ factors) =
  trans
    (cong
      ((factorFirst factor *q orderedValueProduct factors) +q_)
      (sumQuaternionMapLeftMultiply
        (factorValue factor) (firstVariationTerms factors)))
    (cong
      ((factorFirst factor *q orderedValueProduct factors) +q_)
      (cong (factorValue factor *q_)
        (sumFirstVariationTermsExact factors)))

sumSecondVariationTermsExact : ∀ factors →
  sumQuaternion (secondVariationTerms factors)
  ≡ orderedSecondProduct factors
sumSecondVariationTermsExact [] = refl
sumSecondVariationTermsExact (factor ∷ factors) =
  let
    diagonal = factorSecond factor *q orderedValueProduct factors
    firstTerm = factorFirst factor *q orderedFirstProduct factors
    inherited = factorValue factor *q orderedSecondProduct factors
  in
  trans
    (cong
      (diagonal +q_)
      (sumQuaternionAppend
        (map (factorFirst factor *q_) (firstVariationTerms factors))
        (map (factorFirst factor *q_) (firstVariationTerms factors)
          ++ map (factorValue factor *q_)
              (secondVariationTerms factors))))
    (trans
      (cong
        (diagonal +q_)
        (cong₂ _+q_
          (trans
            (sumQuaternionMapLeftMultiply
              (factorFirst factor) (firstVariationTerms factors))
            (cong (factorFirst factor *q_)
              (sumFirstVariationTermsExact factors)))
          (trans
            (sumQuaternionAppend
              (map (factorFirst factor *q_) (firstVariationTerms factors))
              (map (factorValue factor *q_)
                (secondVariationTerms factors)))
            (cong₂ _+q_
              (trans
                (sumQuaternionMapLeftMultiply
                  (factorFirst factor) (firstVariationTerms factors))
                (cong (factorFirst factor *q_)
                  (sumFirstVariationTermsExact factors)))
              (trans
                (sumQuaternionMapLeftMultiply
                  (factorValue factor) (secondVariationTerms factors))
                (cong (factorValue factor *q_)
                  (sumSecondVariationTermsExact factors)))))))
      (cong (diagonal +q_)
        (sym (quaternionAddAssociative firstTerm firstTerm inherited))))

fourFactorJets :
  QuaternionFactorJet → QuaternionFactorJet →
  QuaternionFactorJet → QuaternionFactorJet → List QuaternionFactorJet
fourFactorJets first second third fourth =
  first ∷ second ∷ third ∷ fourth ∷ []

fourFactorSecondVariationAtomCountExact :
  ∀ first second third fourth →
  length (secondVariationTerms
    (fourFactorJets first second third fourth)) ≡ 16
fourFactorSecondVariationAtomCountExact first second third fourth = refl

fourFactorSecondVariationIsSixteenAtomSum :
  ∀ first second third fourth →
  sumQuaternion (secondVariationTerms
    (fourFactorJets first second third fourth))
  ≡ orderedSecondProduct (fourFactorJets first second third fourth)
fourFactorSecondVariationIsSixteenAtomSum first second third fourth =
  sumSecondVariationTermsExact (fourFactorJets first second third fourth)

sumRational : List ℚ → ℚ
sumRational [] = 0ℚ
sumRational (value ∷ values) = value + sumRational values

scalarPartSumQuaternion : ∀ values →
  q0 (sumQuaternion values) ≡ sumRational (map q0 values)
scalarPartSumQuaternion [] = refl
scalarPartSumQuaternion (value ∷ values) =
  cong (q0 value +_) (scalarPartSumQuaternion values)

negativeAdd : ∀ x y → - (x + y) ≡ (- x) + (- y)
negativeAdd = ℚRing.solve-∀

negativeFiniteSum : ∀ values →
  - sumRational values ≡ sumRational (map -_ values)
negativeFiniteSum [] = refl
negativeFiniteSum (value ∷ values) =
  trans
    (negativeAdd value (sumRational values))
    (cong ((- value) +_) (negativeFiniteSum values))

wilsonAtomContribution : RationalQuaternion → ℚ
wilsonAtomContribution atom = - q0 atom

mapNegatedScalarParts : ∀ values →
  map -_ (map q0 values) ≡ map wilsonAtomContribution values
mapNegatedScalarParts [] = refl
mapNegatedScalarParts (value ∷ values) =
  cong ((- q0 value) ∷_) (mapNegatedScalarParts values)

wilsonSecondVariationNumerator : List QuaternionFactorJet → ℚ
wilsonSecondVariationNumerator factors = - q0 (orderedSecondProduct factors)

wilsonSecondVariationAtomSum : List QuaternionFactorJet → ℚ
wilsonSecondVariationAtomSum factors =
  sumRational (map wilsonAtomContribution (secondVariationTerms factors))

wilsonSecondVariationIsAtomSum : ∀ factors →
  wilsonSecondVariationNumerator factors ≡ wilsonSecondVariationAtomSum factors
wilsonSecondVariationIsAtomSum factors =
  trans
    (cong (λ q → - q0 q) (sym (sumSecondVariationTermsExact factors)))
    (trans
      (cong -_ (scalarPartSumQuaternion (secondVariationTerms factors)))
      (trans
        (negativeFiniteSum (map q0 (secondVariationTerms factors)))
        (cong sumRational
          (mapNegatedScalarParts (secondVariationTerms factors)))))

fourLinkWilsonSecondVariationIsSixteenScalarAtoms :
  ∀ first second third fourth →
  wilsonSecondVariationNumerator (fourFactorJets first second third fourth)
  ≡ wilsonSecondVariationAtomSum (fourFactorJets first second third fourth)
fourLinkWilsonSecondVariationIsSixteenScalarAtoms first second third fourth =
  wilsonSecondVariationIsAtomSum
    (fourFactorJets first second third fourth)
