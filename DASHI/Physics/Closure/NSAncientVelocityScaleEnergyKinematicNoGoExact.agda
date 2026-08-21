module DASHI.Physics.Closure.NSAncientVelocityScaleEnergyKinematicNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Luis Caffarelli; Robert Kohn; Louis Nirenberg.
-- Title: "Partial regularity of suitable weak solutions of the
--         Navier-Stokes equations".
-- DOI: 10.1002/cpa.3160350604.
--
-- Authors: Gabriel Koch; Nikolai Nadirashvili; Gregory A. Seregin;
--          Vladimir Sverak.
-- Title: "Liouville theorems for the Navier-Stokes equations and applications".
-- DOI: 10.1007/s11511-009-0039-6.
--
-- ROUND65 / R1 SCALE-MATCHING FALSIFIER
--
-- The revised ancient-solution route asks whether a first singularity forces
-- a constant-excluding defect at the KNSŠ velocity scale r ~ 1/M, where M is
-- the velocity amplitude.  This file proves that the global L2 energy scale
-- and kinematics alone cannot force that conclusion.
--
-- Take a one-parameter concentration profile with
--
--   amplitude       M   = n^3,
--   spatial width   rho = n^(-2),
--   probe radius    r   = M^(-1) = n^(-3),
--   gradient scale  G   = M/rho = n^5.
--
-- Writing q = n^(-1), the exact scale products are
--
--   M^2 rho^3               = 1,
--   (r^2 G)                 = q,       -- normalized derivative
--   r^4 G^2                 = q^2,     -- spacetime Q_grad scale in 3D
--   (G r) / M               = q.       -- relative oscillation at r
--
-- Thus one may keep the energy scale fixed while both the normalized
-- derivative and the velocity-scale critical gradient defect become
-- arbitrarily small as q -> 0.  No Navier-Stokes trajectory is asserted here;
-- the theorem is the sharper negative statement that ENERGY + SCALING alone
-- cannot prove SingularScaleVelocityScaleMatching.  Any positive R1 theorem
-- must consume genuinely dynamical/singularity information.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _*_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

pow2 : ℚ → ℚ
pow2 x = x * x

pow3 : ℚ → ℚ
pow3 x = x * pow2 x

pow5 : ℚ → ℚ
pow5 x = x * (x * (x * (x * x)))

pow6 : ℚ → ℚ
pow6 x = pow3 x * pow3 x

amplitude : ℚ → ℚ
amplitude n = pow3 n

width : ℚ → ℚ
width q = pow2 q

velocityProbeRadius : ℚ → ℚ
velocityProbeRadius q = pow3 q

gradientScale : ℚ → ℚ
gradientScale n = pow5 n

energyScale : ℚ → ℚ → ℚ
energyScale n q =
  pow2 (amplitude n) * pow3 (width q)

normalizedDerivativeScale : ℚ → ℚ → ℚ
normalizedDerivativeScale n q =
  pow2 (velocityProbeRadius q) * gradientScale n

criticalGradientCylinderScale : ℚ → ℚ → ℚ
criticalGradientCylinderScale n q =
  pow2 (pow2 (velocityProbeRadius q)) * pow2 (gradientScale n)

relativeVelocityScaleOscillation : ℚ → ℚ → ℚ
relativeVelocityScaleOscillation n q =
  gradientScale n * velocityProbeRadius q * velocityProbeRadius q

energyRegroup :
  (n q : ℚ) →
  energyScale n q ≡ pow6 (q * n)
energyRegroup n q = solve (n ∷ q ∷ [])

normalizedDerivativeRegroup :
  (n q : ℚ) →
  normalizedDerivativeScale n q ≡ q * pow5 (q * n)
normalizedDerivativeRegroup n q = solve (n ∷ q ∷ [])

criticalGradientRegroup :
  (n q : ℚ) →
  criticalGradientCylinderScale n q ≡ pow2 q * pow5 (pow2 (q * n))
criticalGradientRegroup n q = solve (n ∷ q ∷ [])

relativeOscillationRegroup :
  (n q : ℚ) →
  relativeVelocityScaleOscillation n q ≡ q * pow5 (q * n)
relativeOscillationRegroup n q = solve (n ∷ q ∷ [])

pow5One : pow5 1ℚ ≡ 1ℚ
pow5One = solve []

pow6One : pow6 1ℚ ≡ 1ℚ
pow6One = solve []

pow2One : pow2 1ℚ ≡ 1ℚ
pow2One = solve []

fixedEnergyDespiteGrowingAmplitude :
  (n q : ℚ) →
  q * n ≡ 1ℚ →
  energyScale n q ≡ 1ℚ
fixedEnergyDespiteGrowingAmplitude n q reciprocal =
  trans
    (energyRegroup n q)
    (trans (cong pow6 reciprocal) pow6One)

normalizedDerivativeIsInverseScale :
  (n q : ℚ) →
  q * n ≡ 1ℚ →
  normalizedDerivativeScale n q ≡ q
normalizedDerivativeIsInverseScale n q reciprocal =
  trans
    (normalizedDerivativeRegroup n q)
    (trans
      (cong (λ z → q * pow5 z) reciprocal)
      (trans (cong (q *_) pow5One) (ℚP.*-identityʳ q)))

criticalGradientCylinderIsInverseSquare :
  (n q : ℚ) →
  q * n ≡ 1ℚ →
  criticalGradientCylinderScale n q ≡ pow2 q
criticalGradientCylinderIsInverseSquare n q reciprocal =
  trans
    (criticalGradientRegroup n q)
    (trans
      (cong (λ z → pow2 q * pow5 (pow2 z)) reciprocal)
      (solve (q ∷ [])))

relativeOscillationIsInverseScale :
  (n q : ℚ) →
  q * n ≡ 1ℚ →
  relativeVelocityScaleOscillation n q ≡ q
relativeOscillationIsInverseScale n q reciprocal =
  trans
    (relativeOscillationRegroup n q)
    (trans
      (cong (λ z → q * pow5 z) reciprocal)
      (trans (cong (q *_) pow5One) (ℚP.*-identityʳ q)))

-- Exact combined witness: on the n^3 / n^(-2) concentration scaling,
-- fixed energy coexists with inverse-scale normalized derivative,
-- inverse-square critical cylinder defect, and inverse-scale relative
-- oscillation.  The Archimedean step q -> 0 belongs to the analytic carrier.
energyAloneLeavesVelocityScaleDefectUnfunded :
  (n q : ℚ) →
  q * n ≡ 1ℚ →
  (energyScale n q ≡ 1ℚ)
  × (normalizedDerivativeScale n q ≡ q)
  × (criticalGradientCylinderScale n q ≡ pow2 q)
  × (relativeVelocityScaleOscillation n q ≡ q)
energyAloneLeavesVelocityScaleDefectUnfunded n q reciprocal =
  fixedEnergyDespiteGrowingAmplitude n q reciprocal ,
  normalizedDerivativeIsInverseScale n q reciprocal ,
  criticalGradientCylinderIsInverseSquare n q reciprocal ,
  relativeOscillationIsInverseScale n q reciprocal
  where
    open import Data.Product using (_×_; _,_)
