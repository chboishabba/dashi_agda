module DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlScalarExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
-- Scalar-first quaternion identities used by the flat Wilson-Hessian proof.
-- Ring normalization is deliberately kept local: pair identities expose at
-- most six vector coordinates and one-quaternion identities expose four.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map; _++_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlGeometryExact public

vectorDot : RationalVector3 → RationalVector3 → ℚ
vectorDot (vec3 ax ay az) (vec3 bx by bz) =
  ax * bx + ay * by + az * bz

vectorDotSelfIsNormSq : ∀ a → vectorDot a a ≡ vectorNormSq a
vectorDotSelfIsNormSq (vec3 ax ay az) = refl

pureProductScalar : ∀ a b →
  - q0 (pureQuaternion a *q pureQuaternion b) ≡ vectorDot a b
pureProductScalar (vec3 ax ay az) (vec3 bx by bz) =
  ℚRing.solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])

pureSquareScalar : ∀ a →
  - q0 (pureQuaternion a *q pureQuaternion a) ≡ vectorDot a a
pureSquareScalar a = pureProductScalar a a

vectorDotNegRight : ∀ a b →
  vectorDot a (negV b) ≡ - vectorDot a b
vectorDotNegRight (vec3 ax ay az) (vec3 bx by bz) =
  ℚRing.solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])

vectorDotNegLeft : ∀ a b →
  vectorDot (negV a) b ≡ - vectorDot a b
vectorDotNegLeft (vec3 ax ay az) (vec3 bx by bz) =
  ℚRing.solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])

vectorDotNegBoth : ∀ a b →
  vectorDot (negV a) (negV b) ≡ vectorDot a b
vectorDotNegBoth (vec3 ax ay az) (vec3 bx by bz) =
  ℚRing.solve (ax ∷ ay ∷ az ∷ bx ∷ by ∷ bz ∷ [])

pureNegRightScalar : ∀ a b →
  - q0 (pureQuaternion a *q pureQuaternion (negV b))
  ≡ - vectorDot a b
pureNegRightScalar a b =
  trans (pureProductScalar a (negV b)) (vectorDotNegRight a b)

pureNegLeftScalar : ∀ a b →
  - q0 (pureQuaternion (negV a) *q pureQuaternion b)
  ≡ - vectorDot a b
pureNegLeftScalar a b =
  trans (pureProductScalar (negV a) b) (vectorDotNegLeft a b)

pureNegBothScalar : ∀ a b →
  - q0 (pureQuaternion (negV a) *q pureQuaternion (negV b))
  ≡ vectorDot a b
pureNegBothScalar a b =
  trans (pureProductScalar (negV a) (negV b)) (vectorDotNegBoth a b)

oneQMultiplyLeft : ∀ value → oneQ *q value ≡ value
oneQMultiplyLeft (quat a0 a1 a2 a3) =
  quaternionExt
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))

oneQMultiplyRight : ∀ value → value *q oneQ ≡ value
oneQMultiplyRight (quat a0 a1 a2 a3) =
  quaternionExt
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))
    (ℚRing.solve (a0 ∷ a1 ∷ a2 ∷ a3 ∷ []))

q0AddScalar : ∀ left right →
  q0 (left +q right) ≡ q0 left + q0 right
q0AddScalar = q0Add

flatTailValueOne : ∀ a →
  orderedValueProduct (flatExponentialJet a ∷ []) ≡ oneQ
flatTailValueOne a = oneQMultiplyLeft oneQ

flatTailValueTwo : ∀ a b →
  orderedValueProduct (flatExponentialJet a ∷ flatExponentialJet b ∷ [])
  ≡ oneQ
flatTailValueTwo a b =
  trans
    (cong (oneQ *q_) (flatTailValueOne b))
    (oneQMultiplyLeft oneQ)

flatTailValueThree : ∀ a b c →
  orderedValueProduct
    (flatExponentialJet a ∷ flatExponentialJet b ∷
      flatExponentialJet c ∷ [])
  ≡ oneQ
flatTailValueThree a b c =
  trans
    (cong (oneQ *q_) (flatTailValueTwo b c))
    (oneQMultiplyLeft oneQ)

scalarAtomSum : List RationalQuaternion → ℚ
scalarAtomSum values = sumRational (map wilsonAtomContribution values)

scalarAtomSumAppend : ∀ left right →
  scalarAtomSum (left ++ right)
  ≡ scalarAtomSum left + scalarAtomSum right
scalarAtomSumAppend [] right = sym (ℚP.+-identityˡ (scalarAtomSum right))
scalarAtomSumAppend (value ∷ values) right =
  cong (wilsonAtomContribution value +_)
    (scalarAtomSumAppend values right)

scalarAtomSumMapOneLeft : ∀ values →
  scalarAtomSum (map (oneQ *q_) values) ≡ scalarAtomSum values
scalarAtomSumMapOneLeft [] = refl
scalarAtomSumMapOneLeft (value ∷ values) =
  trans
    (cong
      (λ selected → wilsonAtomContribution selected
        + scalarAtomSum (map (oneQ *q_) values))
      (oneQMultiplyLeft value))
    (cong (wilsonAtomContribution value +_)
      (scalarAtomSumMapOneLeft values))

scalarAtomSumMapThroughOneLeft : ∀ multiplier values →
  scalarAtomSum (map (multiplier *q_) (map (oneQ *q_) values))
  ≡ scalarAtomSum (map (multiplier *q_) values)
scalarAtomSumMapThroughOneLeft multiplier [] = refl
scalarAtomSumMapThroughOneLeft multiplier (value ∷ values) =
  trans
    (cong
      (λ selected → wilsonAtomContribution selected
        + scalarAtomSum
          (map (multiplier *q_) (map (oneQ *q_) values)))
      (cong (multiplier *q_) (oneQMultiplyLeft value)))
    (cong (wilsonAtomContribution (multiplier *q value) +_)
      (scalarAtomSumMapThroughOneLeft multiplier values))

pairAtomSum : RationalQuaternion → List QuaternionFactorJet → ℚ
pairAtomSum multiplier factors =
  scalarAtomSum (map (multiplier *q_) (firstVariationTerms factors))

pairAtomSumFlatCons : ∀ multiplier first second factors →
  pairAtomSum multiplier (factorJet oneQ first second ∷ factors)
  ≡ wilsonAtomContribution
      (multiplier *q (first *q orderedValueProduct factors))
    + pairAtomSum multiplier factors
pairAtomSumFlatCons multiplier first second factors =
  cong
    (wilsonAtomContribution
      (multiplier *q (first *q orderedValueProduct factors)) +_)
    (scalarAtomSumMapThroughOneLeft multiplier (firstVariationTerms factors))

flatSecondAtomRecurrence : ∀ first second factors →
  wilsonSecondVariationAtomSum (factorJet oneQ first second ∷ factors)
  ≡ wilsonAtomContribution (second *q orderedValueProduct factors)
    + (pairAtomSum first factors
      + (pairAtomSum first factors
        + wilsonSecondVariationAtomSum factors))
flatSecondAtomRecurrence first second factors =
  let
    pairs = map (first *q_) (firstVariationTerms factors)
    inherited = map (oneQ *q_) (secondVariationTerms factors)
  in
  trans
    (cong
      (wilsonAtomContribution (second *q orderedValueProduct factors) +_)
      (scalarAtomSumAppend pairs (pairs ++ inherited)))
    (trans
      (cong
        (λ selected →
          wilsonAtomContribution (second *q orderedValueProduct factors)
          + (pairAtomSum first factors + selected))
        (scalarAtomSumAppend pairs inherited))
      (cong
        (λ selected →
          wilsonAtomContribution (second *q orderedValueProduct factors)
          + (pairAtomSum first factors
            + (pairAtomSum first factors + selected)))
        (scalarAtomSumMapOneLeft (secondVariationTerms factors))))
