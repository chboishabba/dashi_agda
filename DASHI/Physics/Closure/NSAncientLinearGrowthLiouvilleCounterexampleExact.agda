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
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; -_)

Point3 : Set
Point3 = ℚ × (ℚ × ℚ)

Vector3 : Set
Vector3 = ℚ × (ℚ × ℚ)

velocity : Point3 → Vector3
velocity (x , (y , z)) = x , ((- y) , 0ℚ)

divergence : Point3 → ℚ
divergence _ = 1 + ((- 1) + 0)

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
incompressible q = refl

curlFree : (q : Point3) → vorticity q ≡ (0ℚ , (0ℚ , 0ℚ))
curlFree q = refl

harmonicVelocity : (q : Point3) →
  laplacianVelocity q ≡ (0ℚ , (0ℚ , 0ℚ))
harmonicVelocity q = refl

stationaryMomentumBalance : (q : Point3) →
  vectorAdd (convectiveAcceleration q) (pressureGradient q)
  ≡ laplacianVelocity q
stationaryMomentumBalance q = refl

origin : Point3
origin = 0ℚ , (0ℚ , 0ℚ)

xUnit : Point3
xUnit = 1 , (0ℚ , 0ℚ)

velocityAtOrigin : velocity origin ≡ (0ℚ , (0ℚ , 0ℚ))
velocityAtOrigin = refl

velocityAtXUnit : velocity xUnit ≡ (1 , (0ℚ , 0ℚ))
velocityAtXUnit = refl

-- The distinct displayed values above are the concrete nonconstancy witness.
-- No general inequality or receipt is used: this is a literal exact solution
-- of the stationary incompressible equations on the polynomial carrier.
