module DASHI.Moonshine.JInvariantLambdaCyclotomicParityExact where

-- Reuse the original cyclotomic rational carrier and Base369 orbit tags.
-- Classical Eisenstein norm and dihedral action; no analytic lambda claim.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C
import DASHI.Moonshine.JInvariantLambdaOrbitBase369BridgeExact as L

rotate reflect : C.Cyclotomic3 → C.Cyclotomic3
rotate x = C.multiply C.zeta x
reflect x = C.multiply C.zeta (C.conjugate x)

rotateNorm : (x : C.Cyclotomic3) → C.norm (rotate x) ≡ C.norm x
rotateNorm (C.cyclotomic3 a b) = solve (a ∷ b ∷ [])

reflectNorm : (x : C.Cyclotomic3) → C.norm (reflect x) ≡ C.norm x
reflectNorm (C.cyclotomic3 a b) = solve (a ∷ b ∷ [])

rotateCubed : (x : C.Cyclotomic3) → rotate (rotate (rotate x)) ≡ x
rotateCubed (C.cyclotomic3 a b) =
  C.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

reflectSquared : (x : C.Cyclotomic3) → reflect (reflect x) ≡ x
reflectSquared (C.cyclotomic3 a b) =
  C.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

dihedralRelation : (x : C.Cyclotomic3) →
  reflect (rotate (reflect x)) ≡ rotate (rotate x)
dihedralRelation (C.cyclotomic3 a b) =
  C.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

-- The raw homogeneous representatives differ from the genuine
-- dihedral action by signs. On projective lambda these signs disappear.
raw : L.LambdaOrbitTag → C.Cyclotomic3 → C.Cyclotomic3
raw L.lambdaIdentity x = x
raw L.lambdaOneOverOneMinus (C.cyclotomic3 a b) = C.cyclotomic3 b (b - a)
raw L.lambdaMinusOneOverLambda (C.cyclotomic3 a b) = C.cyclotomic3 (a - b) a
raw L.lambdaReciprocal (C.cyclotomic3 a b) = C.cyclotomic3 b a
raw L.lambdaOverLambdaMinusOne (C.cyclotomic3 a b) = C.cyclotomic3 a (a - b)
raw L.lambdaOneMinus (C.cyclotomic3 a b) = C.cyclotomic3 (b - a) b

negate : C.Cyclotomic3 → C.Cyclotomic3
negate (C.cyclotomic3 a b) = C.cyclotomic3 (- a) (- b)

normalised : L.LambdaOrbitTag → C.Cyclotomic3 → C.Cyclotomic3
normalised L.lambdaIdentity x = x
normalised L.lambdaOneOverOneMinus x = rotate x
normalised L.lambdaMinusOneOverLambda x = rotate (rotate x)
normalised L.lambdaReciprocal x = reflect x
normalised L.lambdaOverLambdaMinusOne x = rotate (reflect x)
normalised L.lambdaOneMinus x = rotate (rotate (reflect x))

signedRaw : L.LambdaOrbitTag → C.Cyclotomic3 → C.Cyclotomic3
signedRaw L.lambdaIdentity x = raw L.lambdaIdentity x
signedRaw L.lambdaOneOverOneMinus x = negate (raw L.lambdaOneOverOneMinus x)
signedRaw L.lambdaMinusOneOverLambda x = negate (raw L.lambdaMinusOneOverLambda x)
signedRaw L.lambdaReciprocal x = raw L.lambdaReciprocal x
signedRaw L.lambdaOverLambdaMinusOne x = negate (raw L.lambdaOverLambdaMinusOne x)
signedRaw L.lambdaOneMinus x = negate (raw L.lambdaOneMinus x)

sameProjectiveRepresentative : (t : L.LambdaOrbitTag) (x : C.Cyclotomic3) →
  normalised t x ≡ signedRaw t x
sameProjectiveRepresentative L.lambdaIdentity (C.cyclotomic3 a b) =
  C.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))
sameProjectiveRepresentative L.lambdaOneOverOneMinus (C.cyclotomic3 a b) =
  C.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))
sameProjectiveRepresentative L.lambdaMinusOneOverLambda (C.cyclotomic3 a b) =
  C.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))
sameProjectiveRepresentative L.lambdaReciprocal (C.cyclotomic3 a b) =
  C.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))
sameProjectiveRepresentative L.lambdaOverLambdaMinusOne (C.cyclotomic3 a b) =
  C.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))
sameProjectiveRepresentative L.lambdaOneMinus (C.cyclotomic3 a b) =
  C.cyclotomic3Ext (solve (a ∷ b ∷ [])) (solve (a ∷ b ∷ []))

-- Cubic alternating discriminant root, corresponding to Vandermonde.
vandermonde : C.Cyclotomic3 → ℚ
vandermonde (C.cyclotomic3 a b) = a * b * (b - a)

rotateEven : (x : C.Cyclotomic3) → vandermonde (rotate x) ≡ vandermonde x
rotateEven (C.cyclotomic3 a b) = solve (a ∷ b ∷ [])

reflectOdd : (x : C.Cyclotomic3) → vandermonde (reflect x) ≡ - vandermonde x
reflectOdd (C.cyclotomic3 a b) = solve (a ∷ b ∷ [])

-- Q is the original C.norm; D is the square of this alternating cubic.
-- Source-written proof candidates, pinned kernel acceptance pending.
