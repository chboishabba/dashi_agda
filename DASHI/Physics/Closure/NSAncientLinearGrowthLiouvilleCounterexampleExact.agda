module DASHI.Physics.Closure.NSAncientLinearGrowthLiouvilleCounterexampleExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Authors: Zhen Lei; Qi S. Zhang; Na Zhao.
-- Title: "Improved Liouville theorems for axially symmetric Navier-Stokes
--         equations".
-- DOI: 10.1360/N012016-00149.
-- arXiv: 1701.00868.
--
-- SHARPNESS MECHANISM
-- The paper gives stationary linear-growth counterexamples showing that the
-- sublinear-growth hypothesis in its Liouville theorems is sharp.  We encode
-- the basic 3-D extension
--
--   u(x,y,z) = (x,-y,0),
--   p(x,y,z) = -(x^2+y^2)/2.
--
-- It is divergence-free, curl-free and harmonic; nevertheless it is
-- nonconstant.  Its convective acceleration (x,y,0) is cancelled exactly by
-- grad p = (-x,-y,0).  Hence bounded/zero vorticity plus at-most-linear
-- velocity growth cannot by itself be a general ancient Liouville criterion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; -_; _<_)
import Data.Rational.Properties as ℚP
open ℚP using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Nullary.Negation.Core using (¬_)

Point3 : Set
Point3 = ℚ × (ℚ × ℚ)

Vector3 : Set
Vector3 = ℚ × (ℚ × ℚ)

velocity : Point3 → Vector3
velocity (x , (y , z)) = x , ((- y) , 0ℚ)

divergence : Point3 → ℚ
divergence _ = 1ℚ + ((- 1ℚ) + 0ℚ)

vorticity : Point3 → Vector3
vorticity _ = 0ℚ , (0ℚ , 0ℚ)

laplacianVelocity : Point3 → Vector3
laplacianVelocity _ = 0ℚ , (0ℚ , 0ℚ)

convectiveAcceleration : Point3 → Vector3
convectiveAcceleration (x , (y , z)) = x , (y , 0ℚ)

pressureGradient : Point3 → Vector3
pressureGradient (x , (y , z)) = (- x) , ((- y) , 0ℚ)

vectorAdd : Vector3 → Vector3 → Vector3
vectorAdd (a , (b , c)) (x , (y , z)) =
  (a + x) , ((b + y) , (c + z))

incompressible : (q : Point3) → divergence q ≡ 0ℚ
incompressible q = solve []

curlFree : (q : Point3) → vorticity q ≡ (0ℚ , (0ℚ , 0ℚ))
curlFree q = refl

harmonicVelocity : (q : Point3) →
  laplacianVelocity q ≡ (0ℚ , (0ℚ , 0ℚ))
harmonicVelocity q = refl

stationaryMomentumBalance : (q : Point3) →
  vectorAdd (convectiveAcceleration q) (pressureGradient q)
  ≡ laplacianVelocity q
stationaryMomentumBalance (x , (y , z)) =
  cong₂ _,_
    (solve (x ∷ []))
    (cong₂ _,_
      (solve (y ∷ []))
      (solve []))

origin : Point3
origin = 0ℚ , (0ℚ , 0ℚ)

xUnit : Point3
xUnit = 1ℚ , (0ℚ , 0ℚ)

velocityAtOrigin : velocity origin ≡ (0ℚ , (0ℚ , 0ℚ))
velocityAtOrigin = refl

velocityAtXUnit : velocity xUnit ≡ (1ℚ , (0ℚ , 0ℚ))
velocityAtXUnit = refl

SpatiallyConstant : (Point3 → Vector3) → Set
SpatiallyConstant u = (a b : Point3) → u a ≡ u b

zeroLessOne : 0ℚ < 1ℚ
zeroLessOne = toWitness {a? = 0ℚ <? 1ℚ} _

zeroNotOne : ¬ (0ℚ ≡ 1ℚ)
zeroNotOne zeroEqualsOne =
  let
    zeroLessZero : 0ℚ < 0ℚ
    zeroLessZero =
      subst (λ right → 0ℚ < right) (sym zeroEqualsOne) zeroLessOne
  in
  ℚP.<-irrefl 0ℚ zeroLessZero

linearGrowthWitnessIsNonconstant : ¬ SpatiallyConstant velocity
linearGrowthWitnessIsNonconstant constant =
  zeroNotOne
    (cong proj₁
      (constant origin xUnit))
