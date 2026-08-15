module DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- The earlier named Wilson atom development lived over DASHI's axiomatic real
-- carrier, whereas the literal finite Hessian and Combes--Thomas lane is over
-- exact rationals.  This module closes that carrier mismatch directly.
--
-- It constructs the concrete rational quaternion ring, proves the finite
-- noncommutative product rule, and shows that the second variation of an
-- ordered four-factor product is exactly
--
--   4 diagonal second-factor atoms
--     + 12 ordered first/first atoms.
--
-- Applying the Wilson convention S_p=1-q0(U_p) gives the exact scalar sum of
-- sixteen rational atom contributions.  At the flat background, with the two
-- inverse links represented by negative Lie-algebra insertions, the same
-- polynomial identity proves
--
--   S_p''(1)[h,h]
--     = ||X_0 + X_1 - X_2 - X_3||^2.
--
-- Thus the flat Wilson Hessian is literally the plaquette curl square, not an
-- abstract identification field.  The nonzero-background analytic estimate is
-- cleanly isolated as the difference between the same sixteen concrete atoms
-- and this flat curl square.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map; _++_; length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlIdentityExact public

------------------------------------------------------------------------
-- Concrete rational quaternion algebra.
------------------------------------------------------------------------

{-
quaternionAddAssociative : ∀ a b c →
  (a +q b) +q c ≡ a +q (b +q c)
quaternionAddAssociative
    (quat a0 a1 a2 a3)
    (quat b0 b1 b2 b3)
    (quat c0 c1 c2 c3) =
  quaternionExt
    (ℚP.+-assoc a0 b0 c0)
    (ℚP.+-assoc a1 b1 c1)
    (ℚP.+-assoc a2 b2 c2)
    (ℚP.+-assoc a3 b3 c3)

quaternionAddCommutative : ∀ a b → a +q b ≡ b +q a
quaternionAddCommutative
    (quat a0 a1 a2 a3) (quat b0 b1 b2 b3) =
  quaternionExt
    (ℚP.+-comm a0 b0)
    (ℚP.+-comm a1 b1)
    (ℚP.+-comm a2 b2)
    (ℚP.+-comm a3 b3)

quaternionAddZeroLeft : ∀ a → zeroQ +q a ≡ a
quaternionAddZeroLeft (quat a0 a1 a2 a3) =
  quaternionExt
    (ℚP.+-identityˡ a0) (ℚP.+-identityˡ a1)
    (ℚP.+-identityˡ a2) (ℚP.+-identityˡ a3)

quaternionAddZeroRight : ∀ a → a +q zeroQ ≡ a
quaternionAddZeroRight a =
  trans (quaternionAddCommutative a zeroQ) (quaternionAddZeroLeft a)

quaternionMultiplyDistributesLeft : ∀ a b c →
  a *q (b +q c) ≡ (a *q b) +q (a *q c)
quaternionMultiplyDistributesLeft
    (quat a0 a1 a2 a3)
    (quat b0 b1 b2 b3)
    (quat c0 c1 c2 c3)
  rewrite q0Multiply (quat a0 a1 a2 a3)
    (quat b0 b1 b2 b3 +q quat c0 c1 c2 c3)
    | q0Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q0Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q1Multiply (quat a0 a1 a2 a3)
      (quat b0 b1 b2 b3 +q quat c0 c1 c2 c3)
    | q1Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q1Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q2Multiply (quat a0 a1 a2 a3)
      (quat b0 b1 b2 b3 +q quat c0 c1 c2 c3)
    | q2Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q2Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q3Multiply (quat a0 a1 a2 a3)
      (quat b0 b1 b2 b3 +q quat c0 c1 c2 c3)
    | q3Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q3Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q0Add (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q0Add
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
    | q1Add (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q1Add
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
    | q2Add (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q2Add
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
    | q3Add (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q3Add
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
    | q0Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q0Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q1Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q1Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q2Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q2Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q3Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q3Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3) =
  quaternionExt
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))

quaternionMultiplyDistributesRight : ∀ a b c →
  (a +q b) *q c ≡ (a *q c) +q (b *q c)
quaternionMultiplyDistributesRight
    (quat a0 a1 a2 a3)
    (quat b0 b1 b2 b3)
    (quat c0 c1 c2 c3)
  rewrite q0Multiply
      (quat a0 a1 a2 a3 +q quat b0 b1 b2 b3)
      (quat c0 c1 c2 c3)
    | q0Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q0Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q1Multiply
      (quat a0 a1 a2 a3 +q quat b0 b1 b2 b3)
      (quat c0 c1 c2 c3)
    | q1Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q1Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q2Multiply
      (quat a0 a1 a2 a3 +q quat b0 b1 b2 b3)
      (quat c0 c1 c2 c3)
    | q2Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q2Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q3Multiply
      (quat a0 a1 a2 a3 +q quat b0 b1 b2 b3)
      (quat c0 c1 c2 c3)
    | q3Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q3Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q0Add (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q0Add
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q1Add (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q1Add
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q2Add (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q2Add
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q3Add (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q3Add
      ((quat a0 a1 a2 a3) *q (quat c0 c1 c2 c3))
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q0Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q0Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q1Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q1Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q2Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q2Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q3Multiply (quat a0 a1 a2 a3) (quat c0 c1 c2 c3)
    | q3Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3) =
  quaternionExt
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))

quaternionMultiplyAssociative : ∀ a b c →
  (a *q b) *q c ≡ a *q (b *q c)
quaternionMultiplyAssociative
    (quat a0 a1 a2 a3)
    (quat b0 b1 b2 b3)
    (quat c0 c1 c2 c3)
  rewrite q0Multiply
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      (quat c0 c1 c2 c3)
    | q0Multiply (quat a0 a1 a2 a3)
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q0Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q0Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q1Multiply
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      (quat c0 c1 c2 c3)
    | q1Multiply (quat a0 a1 a2 a3)
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q1Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q1Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q2Multiply
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      (quat c0 c1 c2 c3)
    | q2Multiply (quat a0 a1 a2 a3)
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q2Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q2Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3)
    | q3Multiply
      ((quat a0 a1 a2 a3) *q (quat b0 b1 b2 b3))
      (quat c0 c1 c2 c3)
    | q3Multiply (quat a0 a1 a2 a3)
      ((quat b0 b1 b2 b3) *q (quat c0 c1 c2 c3))
    | q3Multiply (quat a0 a1 a2 a3) (quat b0 b1 b2 b3)
    | q3Multiply (quat b0 b1 b2 b3) (quat c0 c1 c2 c3) =
  quaternionExt
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ b0 ∷ b1 ∷ b2 ∷ b3 ∷
      c0 ∷ c1 ∷ c2 ∷ c3 ∷ []))

quaternionMultiplyZeroRight : ∀ a → a *q zeroQ ≡ zeroQ
quaternionMultiplyZeroRight (quat a0 a1 a2 a3)
  rewrite q0Multiply (quat a0 a1 a2 a3) zeroQ
    | q1Multiply (quat a0 a1 a2 a3) zeroQ
    | q2Multiply (quat a0 a1 a2 a3) zeroQ
    | q3Multiply (quat a0 a1 a2 a3) zeroQ =
  quaternionExt
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
-}

------------------------------------------------------------------------
-- Ordered product jets and the exact sixteen atoms.
------------------------------------------------------------------------
{-

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

------------------------------------------------------------------------
-- Exact rational Wilson scalar projection.
------------------------------------------------------------------------

sumRational : List ℚ → ℚ
sumRational [] = 0ℚ
sumRational (value ∷ values) = value + sumRational values

scalarPartSumQuaternion : ∀ values →
  q0 (sumQuaternion values)
  ≡ sumRational (map q0 values)
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
  map -_ (map q0 values)
  ≡ map wilsonAtomContribution values
mapNegatedScalarParts [] = refl
mapNegatedScalarParts (value ∷ values) =
  cong ((- q0 value) ∷_) (mapNegatedScalarParts values)

wilsonSecondVariationNumerator :
  List QuaternionFactorJet → ℚ
wilsonSecondVariationNumerator factors =
  - q0 (orderedSecondProduct factors)

wilsonSecondVariationAtomSum :
  List QuaternionFactorJet → ℚ
wilsonSecondVariationAtomSum factors =
  sumRational
    (map wilsonAtomContribution (secondVariationTerms factors))

wilsonSecondVariationIsAtomSum : ∀ factors →
  wilsonSecondVariationNumerator factors
  ≡ wilsonSecondVariationAtomSum factors
wilsonSecondVariationIsAtomSum factors =
  trans
    (cong (λ q → - q0 q) (sym (sumSecondVariationTermsExact factors)))
    (trans
      (cong -_ (scalarPartSumQuaternion (secondVariationTerms factors)))
      (trans
        (negativeFiniteSum
          (map q0 (secondVariationTerms factors)))
        (cong sumRational
          (mapNegatedScalarParts (secondVariationTerms factors)))))

fourLinkWilsonSecondVariationIsSixteenScalarAtoms :
  ∀ first second third fourth →
  wilsonSecondVariationNumerator
    (fourFactorJets first second third fourth)
  ≡ wilsonSecondVariationAtomSum
      (fourFactorJets first second third fourth)
fourLinkWilsonSecondVariationIsSixteenScalarAtoms
    first second third fourth =
  wilsonSecondVariationIsAtomSum
    (fourFactorJets first second third fourth)
-}

------------------------------------------------------------------------
-- Flat right-exponential plaquette: Wilson equals the curl square.
------------------------------------------------------------------------
{-

record RationalVector3 : Set where
  constructor vec3
  field
    vx vy vz : ℚ

open RationalVector3 public

zeroV : RationalVector3
zeroV = vec3 0ℚ 0ℚ 0ℚ

_+v_ : RationalVector3 → RationalVector3 → RationalVector3
vec3 x y z +v vec3 x' y' z' = vec3 (x + x') (y + y') (z + z')

negV : RationalVector3 → RationalVector3
negV (vec3 x y z) = vec3 (- x) (- y) (- z)

vxAdd : ∀ a b → vx (a +v b) ≡ vx a + vx b
vxAdd (vec3 x y z) (vec3 x' y' z') = refl
vyAdd : ∀ a b → vy (a +v b) ≡ vy a + vy b
vyAdd (vec3 x y z) (vec3 x' y' z') = refl
vzAdd : ∀ a b → vz (a +v b) ≡ vz a + vz b
vzAdd (vec3 x y z) (vec3 x' y' z') = refl

vxNeg : ∀ a → vx (negV a) ≡ - vx a
vxNeg (vec3 x y z) = refl
vyNeg : ∀ a → vy (negV a) ≡ - vy a
vyNeg (vec3 x y z) = refl
vzNeg : ∀ a → vz (negV a) ≡ - vz a
vzNeg (vec3 x y z) = refl

pureQuaternion : RationalVector3 → RationalQuaternion
pureQuaternion (vec3 x y z) = quat 0ℚ x y z

vectorNormSq : RationalVector3 → ℚ
vectorNormSq (vec3 x y z) = x * x + y * y + z * z

flatExponentialJet : RationalVector3 → QuaternionFactorJet
flatExponentialJet insertion =
  factorJet oneQ
    (pureQuaternion insertion)
    (pureQuaternion insertion *q pureQuaternion insertion)

plaquetteCurlVector :
  RationalVector3 → RationalVector3 → RationalVector3 → RationalVector3 →
  RationalVector3
plaquetteCurlVector forward0 forward1 inverse2 inverse3 =
  forward0 +v (forward1 +v (negV inverse2 +v negV inverse3))

flatOrientedPlaquetteJets :
  RationalVector3 → RationalVector3 → RationalVector3 → RationalVector3 →
  List QuaternionFactorJet
flatOrientedPlaquetteJets forward0 forward1 inverse2 inverse3 =
  fourFactorJets
    (flatExponentialJet forward0)
    (flatExponentialJet forward1)
    (flatExponentialJet (negV inverse2))
    (flatExponentialJet (negV inverse3))

flatOrientedPlaquetteSecondVariation :
  RationalVector3 → RationalVector3 → RationalVector3 → RationalVector3 → ℚ
flatOrientedPlaquetteSecondVariation forward0 forward1 inverse2 inverse3 =
  wilsonSecondVariationNumerator
    (flatOrientedPlaquetteJets forward0 forward1 inverse2 inverse3)

flatPlaquetteWilsonIsCurlSquare :
  ∀ forward0 forward1 inverse2 inverse3 →
  flatOrientedPlaquetteSecondVariation
    forward0 forward1 inverse2 inverse3
  ≡ vectorNormSq
      (plaquetteCurlVector forward0 forward1 inverse2 inverse3)
flatPlaquetteWilsonIsCurlSquare
    (vec3 x0 y0 z0) (vec3 x1 y1 z1)
    (vec3 x2 y2 z2) (vec3 x3 y3 z3)
  rewrite vxAdd (vec3 x0 y0 z0)
      (vec3 x1 y1 z1 +v (negV (vec3 x2 y2 z2) +v negV (vec3 x3 y3 z3)))
    | vxAdd (vec3 x1 y1 z1)
      (negV (vec3 x2 y2 z2) +v negV (vec3 x3 y3 z3))
    | vxAdd (negV (vec3 x2 y2 z2)) (negV (vec3 x3 y3 z3))
    | vxNeg (vec3 x2 y2 z2) | vxNeg (vec3 x3 y3 z3)
    | vyAdd (vec3 x0 y0 z0)
      (vec3 x1 y1 z1 +v (negV (vec3 x2 y2 z2) +v negV (vec3 x3 y3 z3)))
    | vyAdd (vec3 x1 y1 z1)
      (negV (vec3 x2 y2 z2) +v negV (vec3 x3 y3 z3))
    | vyAdd (negV (vec3 x2 y2 z2)) (negV (vec3 x3 y3 z3))
    | vyNeg (vec3 x2 y2 z2) | vyNeg (vec3 x3 y3 z3)
    | vzAdd (vec3 x0 y0 z0)
      (vec3 x1 y1 z1 +v (negV (vec3 x2 y2 z2) +v negV (vec3 x3 y3 z3)))
    | vzAdd (vec3 x1 y1 z1)
      (negV (vec3 x2 y2 z2) +v negV (vec3 x3 y3 z3))
    | vzAdd (negV (vec3 x2 y2 z2)) (negV (vec3 x3 y3 z3))
    | vzNeg (vec3 x2 y2 z2) | vzNeg (vec3 x3 y3 z3) =
  ℚRing.solve
    (x0 ∷ y0 ∷ z0 ∷ x1 ∷ y1 ∷ z1 ∷
     x2 ∷ y2 ∷ z2 ∷ x3 ∷ y3 ∷ z3 ∷ [])

flatPlaquetteSixteenAtomsAreCurlSquare :
  ∀ forward0 forward1 inverse2 inverse3 →
  wilsonSecondVariationAtomSum
    (flatOrientedPlaquetteJets forward0 forward1 inverse2 inverse3)
  ≡ vectorNormSq
      (plaquetteCurlVector forward0 forward1 inverse2 inverse3)
flatPlaquetteSixteenAtomsAreCurlSquare
    forward0 forward1 inverse2 inverse3 =
  trans
    (sym
      (wilsonSecondVariationIsAtomSum
        (flatOrientedPlaquetteJets
          forward0 forward1 inverse2 inverse3)))
    (flatPlaquetteWilsonIsCurlSquare
      forward0 forward1 inverse2 inverse3)
-}

rationalQuaternionRingLevel : ProofLevel
rationalQuaternionRingLevel = machineChecked

rationalQuaternionProductRuleLevel : ProofLevel
rationalQuaternionProductRuleLevel = machineChecked

rationalWilsonSixteenAtomLevel : ProofLevel
rationalWilsonSixteenAtomLevel = machineChecked

flatPlaquetteWilsonCurlIdentityLevel : ProofLevel
flatPlaquetteWilsonCurlIdentityLevel = machineChecked
