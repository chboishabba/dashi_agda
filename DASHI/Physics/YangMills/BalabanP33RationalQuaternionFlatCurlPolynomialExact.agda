module DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlPolynomialExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionFlatCurlGeometryExact public

flatPlaquetteWilsonIsCurlSquare :
  ∀ forward0 forward1 inverse2 inverse3 →
  flatOrientedPlaquetteSecondVariation forward0 forward1 inverse2 inverse3
  ≡ vectorNormSq (plaquetteCurlVector forward0 forward1 inverse2 inverse3)
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
