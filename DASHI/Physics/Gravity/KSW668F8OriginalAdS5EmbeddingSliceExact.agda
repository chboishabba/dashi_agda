module DASHI.Physics.Gravity.KSW668F8OriginalAdS5EmbeddingSliceExact where

------------------------------------------------------------------------
-- Max-cut XXIX: original a=t AdS5 Poincare-coordinate moving brane.
-- The SAME background used by the KSW668 F8 moving solver:
-- g5 = z^-2 diag(-1,1,1,1,1), z(t)=1/t,
-- T'(t)=sqrt(1+t^2)/t^2, induced h=-dt^2+t^2 dx^2.
--
-- This module proves an exact rational t=4/3 embedding/proper-time
-- slice and background scalar-curvature algebra. The all-component
-- general real Levi-Civita/Riemann/Weyl derivation has been checked
-- independently in SymPy, NOT in Agda. Nor does the VANISHING Weyl
-- of the *background* prove the linearized sourced TT Weyl formula.
--
-- Reuses existing original-source KSW geometry rather than an invented
-- independent brane. Caldwell--Langlois physical attribution retained.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668AdS5IsraelOriginalRationalSliceExact as Israel

sliceTime : ℚ
sliceTime = (+ 4) / 3

sliceBulkZ : ℚ
sliceBulkZ = (+ 3) / 4

sliceBulkTdot : ℚ
sliceBulkTdot = (+ 15) / 16

sliceBulkZdot : ℚ
sliceBulkZdot = - ((+ 9) / 16)

inverseZSquared : ℚ
inverseZSquared = (+ 16) / 9

-- The induced temporal metric is z^-2(-Tdot^2+zdot^2) = -1.
sameOriginalInducedProperTime :
  inverseZSquared *
    (- (sliceBulkTdot * sliceBulkTdot)
      + sliceBulkZdot * sliceBulkZdot)
    ≡ - 1ℚ
sameOriginalInducedProperTime = solve []

sameOriginalSpatialScale :
  inverseZSquared ≡ sliceTime * sliceTime
sameOriginalSpatialScale = solve []

sliceMatchesOriginalIsraelTime :
  sliceTime ≡ Israel.originalTime
sliceMatchesOriginalIsraelTime = solve []

-- On AdS5 of curvature radius one, Ricci_AB=-4 g_AB and R=-20.
-- This is an exact finite trace *consequence* of constant curvature;
-- NOT an Agda derivation of the connection or curvature tensor.
backgroundRicciTraceAlgebra :
  ((+ 5) / 1) * (- ((+ 4) / 1))
    ≡ - ((+ 20) / 1)
backgroundRicciTraceAlgebra = solve []

-- Explicit unresolved geometric promotions are not constructed here.
data OriginalF8GeometricPromotionHole : Set where
  connectionFromOriginalPoincareMetric :
    OriginalF8GeometricPromotionHole
  completeRiemannFromConnection :
    OriginalF8GeometricPromotionHole
  linearisedTTWeylNotBackgroundWeyl :
    OriginalF8GeometricPromotionHole
  electricProjectionAtMovingBrane :
    OriginalF8GeometricPromotionHole
