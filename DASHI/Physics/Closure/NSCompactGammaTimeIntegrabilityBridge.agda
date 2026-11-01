module DASHI.Physics.Closure.NSCompactGammaTimeIntegrabilityBridge where

open import Agda.Primitive using (Level; _⊔_; lsuc)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption

------------------------------------------------------------------------
-- Pointwise-to-time-integrated control.
--
-- This is the exact bridge needed after a continuum D log E modulus has been
-- obtained.  It does not assert that the chosen envelope is integrable or that
-- it dominates vorticity; those are the analytic/BKM-facing leaves.  Given
-- those facts, monotonicity of the time integral yields the required finite
-- expenditure bound without another proof seam.
------------------------------------------------------------------------

record MonotoneTimeIntegral
    {t : Level}
    (Time : Set t)
    (A : AbsorptionArithmetic) : Set (lsuc t) where
  field
    integrate : (Time → Scalar A) → Scalar A

    integrateMonotone :
      {left right : Time → Scalar A} →
      ((time : Time) → _≤_ A (left time) (right time)) →
      _≤_ A (integrate left) (integrate right)

open MonotoneTimeIntegral public

record PointwiseIntegralEnvelope
    {t : Level}
    {Time : Set t}
    (A : AbsorptionArithmetic)
    (J : MonotoneTimeIntegral Time A) : Set (lsuc t) where
  field
    response : Time → Scalar A
    envelope : Time → Scalar A

    pointwiseResponseBelowEnvelope :
      (time : Time) →
      _≤_ A (response time) (envelope time)

open PointwiseIntegralEnvelope public

integratePointwiseEnvelope :
  ∀ {t}
    {Time : Set t}
    (A : AbsorptionArithmetic)
    (J : MonotoneTimeIntegral Time A) →
  (E : PointwiseIntegralEnvelope A J) →
  _≤_ A
    (integrate J (response E))
    (integrate J (envelope E))
integratePointwiseEnvelope A J E =
  integrateMonotone J (pointwiseResponseBelowEnvelope E)

record FiniteEnvelopeExpenditure
    {t : Level}
    {Time : Set t}
    (A : AbsorptionArithmetic)
    (J : MonotoneTimeIntegral Time A) : Set (lsuc t) where
  field
    envelopeInputs : PointwiseIntegralEnvelope A J
    expenditureBudget : Scalar A

    envelopeIntegralBelowBudget :
      _≤_ A
        (integrate J (envelope envelopeInputs))
        expenditureBudget

open FiniteEnvelopeExpenditure public

finiteEnvelopeBoundsIntegratedResponse :
  ∀ {t}
    {Time : Set t}
    (A : AbsorptionArithmetic)
    (J : MonotoneTimeIntegral Time A) →
  (E : FiniteEnvelopeExpenditure A J) →
  _≤_ A
    (integrate J (response (envelopeInputs E)))
    (expenditureBudget E)
finiteEnvelopeBoundsIntegratedResponse A J E =
  ≤-trans A
    (integratePointwiseEnvelope A J (envelopeInputs E))
    (envelopeIntegralBelowBudget E)

------------------------------------------------------------------------
-- Named BKM-facing specialization.  `vorticityNorm` is deliberately abstract:
-- the PDE layer must identify the actual L-infinity vorticity norm and prove
-- its domination by the compact-Gamma-derived envelope.
------------------------------------------------------------------------

record BKMEnvelopeInputs
    {t : Level}
    {Time : Set t}
    (A : AbsorptionArithmetic)
    (J : MonotoneTimeIntegral Time A) : Set (lsuc t) where
  field
    vorticityNorm : Time → Scalar A
    compactGammaEnvelope : Time → Scalar A
    bkmBudget : Scalar A

    vorticityBelowCompactGammaEnvelope :
      (time : Time) →
      _≤_ A
        (vorticityNorm time)
        (compactGammaEnvelope time)

    compactGammaEnvelopeIntegrable :
      _≤_ A
        (integrate J compactGammaEnvelope)
        bkmBudget

open BKMEnvelopeInputs public

compactGammaEnvelopeBoundsBKMIntegral :
  ∀ {t}
    {Time : Set t}
    (A : AbsorptionArithmetic)
    (J : MonotoneTimeIntegral Time A) →
  (B : BKMEnvelopeInputs A J) →
  _≤_ A
    (integrate J (vorticityNorm B))
    (bkmBudget B)
compactGammaEnvelopeBoundsBKMIntegral A J B =
  ≤-trans A
    (integrateMonotone J
      (vorticityBelowCompactGammaEnvelope B))
    (compactGammaEnvelopeIntegrable B)
