module DASHI.Physics.Gravity.KSW668F8FullTensorAngularNormExact where

------------------------------------------------------------------------
-- Maximum-cut XXXIII: ACTUAL full original F8 3x3 tensor TT norm.
-- REUSE: KSW668F8TTSymbolDiscreteCompatibilityExact.agda owns
-- T(k) = P(k) Q P(k) - (1/2)P(k) tr(P(k)Q),
-- Q=diag(0,1,-1), P=|k|^2 I - k k^T.
--
-- IMPORTANT: Frobenius norm is not axisymmetric pointwise because
-- Q breaks rotation symmetry in the yz plane. Its AZIMUTHAL AVERAGE
-- is axisymmetric, and equals twice the original axisymmetric yy
-- symbol when |k|=1. The average is a Fourier-space angular
-- calculation, NOT the physical real-space tensor energy Gram
-- of independently evolved scalar H_l components.
--
-- No claim of original tensor-to-radial FV discrete isometry,
-- full moving SAT stability, or experimental graviton observation.
-- Attribution to the original KSW tensor generator retained.
-- Pinned Agda kernel NOT RUN.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.Gravity.KSW668F8TTSymbolDiscreteCompatibilityExact as TT
import DASHI.Physics.Gravity.KSW668AdS5TTMultipoleAngularRationalExact as Angular

two half quarter eighth : ℚ
two = (+ 2) / 1
half = (+ 1) / 2
quarter = (+ 1) / 4
eighth = (+ 1) / 8

sq : ℚ → ℚ
sq q = q * q

kSquared : ℚ → ℚ → ℚ → ℚ
kSquared x y z = sq x + sq y + sq z

-- Full 3x3 Frobenius contraction counts off-diagonal entries twice.
ttFrobeniusSquared : ℚ → ℚ → ℚ → ℚ
ttFrobeniusSquared x y z =
  sq (TT.ttXX x y z) + sq (TT.ttYY x y z)
  + sq (TT.ttZZ x y z)
  + two * (sq (TT.ttXY x y z) + sq (TT.ttXZ x y z)
         + sq (TT.ttYZ x y z))

-- This is exactly the original tensor, not a generic TT surrogate.
originalFullTTNormFactorization :
  (x y z : ℚ) →
  ttFrobeniusSquared x y z
  ≡ half * sq (kSquared x y z)
       * (sq (two * sq x + sq y + sq z)
          + - (((+ 4) / 1) * sq y * sq z))
originalFullTTNormFactorization x y z = solve []

-- For a unit wavevector, write mu=kx, transverse squared length
-- s=1-mu². The azimuthal average of ky² kz² is s²/8.
-- Here the exact rational moment 1/8 is included as a separate
-- finite angular identity; promotion to an integral uses the
-- conventional uniform dphi/(2pi) measure.
azimuthFourthMoment : (s : ℚ) →
  quarter * ((+ 1) / 2) * sq s ≡ eighth * sq s
azimuthFourthMoment s = solve []

azimuthAveragedFullTTNorm : ℚ → ℚ
azimuthAveragedFullTTNorm mu =
  half * (sq (1ℚ + sq mu)
          + - (half * sq (1ℚ + - sq mu)))

originalTensorAzimuthAverage :
  (mu : ℚ) →
  azimuthAveragedFullTTNorm mu
  ≡ quarter * (sq (sq mu) + ((+ 6) / 1) * sq mu + 1ℚ)
originalTensorAzimuthAverage mu = solve []

-- SURPRISING EXACT RELATION. This is a scalar angular
-- pointwise-in-mu identity AFTER azimuthal averaging, not an
-- unqualified full tensor equality to two times one component.
originalAverageIsTwiceYYAngular :
  (mu : ℚ) →
  azimuthAveragedFullTTNorm mu
    ≡ two * Angular.originalTTYYAngular mu
originalAverageIsTwiceYYAngular mu = solve []

originalAverageLegendreExpansion :
  (mu : ℚ) →
  azimuthAveragedFullTTNorm mu
    ≡ ((+ 4) / 5) * Angular.p0 mu
       + ((+ 8) / 7) * Angular.p2 mu
       + ((+ 2) / 35) * Angular.p4 mu
originalAverageLegendreExpansion mu = solve []

-- Integral in dmu over [-1,1], omitting the global 2pi factor:
-- 1/4*(2/9+6*2/3+2)=8/5.
originalFullTTAzimuthIntegratedNorm :
  quarter * (((+ 2) / 9) + ((+ 6) / 1) * ((+ 2) / 3)
      + ((+ 2) / 1))
    ≡ (+ 8) / 5
originalFullTTAzimuthIntegratedNorm = solve []
