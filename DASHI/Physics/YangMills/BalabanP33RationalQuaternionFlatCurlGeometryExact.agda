module DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlGeometryExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_)

open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionCoreExact public
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonJetExact public

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
