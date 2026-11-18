module DASHI.Physics.QuantumSensors.DiamondMCGSchurInformationIncrementExact where

------------------------------------------------------------------------
-- Phase P1/W1: covariance-block information accounting for one extra sensor.
-- Mathematical origin: classical Schur complement / GLS block inversion.
-- Reuses detector objective of DiamondMCGArrayInformationWeldExact,
-- existing covariance GLS and finite complex Cauchy-Schwarz owners.
--
-- IMPORTANT: the exact block inversion and positivity need a separately
-- supplied covariance certificate. This module proves the conditional
-- information monotonicity, not physical covariance calibration and not
-- arbitrary covariance invertibility by fiat.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)

record SchurIncrementCertificate {ℓ : Level} (Scalar : Set ℓ) :
    Set (lsuc ℓ) where
  field
    _+_ : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set ℓ
    oldInformation : Scalar
    newInformation : Scalar
    conditionalInnovation : Scalar
    conditionalVariance : Scalar
    conditionalGain : Scalar

    -- The same-array covariance block law supplies the exact numerical
    -- identity gain = innovation² / variance. Invertibility, units,
    -- calibration and positive variance are evidence-specific obligations.
    gainFromInnovation :
      conditionalGain ≡ conditionalInnovation
    -- The 'conditionalInnovation' here is a precomputed nonnegative
    -- *information gain*, not a raw signed magnetic innovation; the
    -- calibration owner must establish the squared/variance expression.
    schurBlockIdentity :
      newInformation ≡ oldInformation + conditionalGain
    nonnegativeGain : oldInformation ≤ oldInformation + conditionalGain
open SchurIncrementCertificate public

schurAdditionDoesNotDecreaseInformation :
  ∀ {ℓ} {Scalar : Set ℓ}
    (certificate : SchurIncrementCertificate Scalar) →
    _≤_ certificate
      (oldInformation certificate)
      (newInformation certificate)
schurAdditionDoesNotDecreaseInformation certificate
  rewrite schurBlockIdentity certificate =
    nonnegativeGain certificate

-- The innovation-zero case is explicitly a *score* equality, not an
-- assertion of independent readout or increased physical sensitivity.
record ZeroInnovationCertificate {ℓ : Level} (Scalar : Set ℓ) :
    Set (lsuc ℓ) where
  field
    parent : SchurIncrementCertificate Scalar
    zero : Scalar
    gainIsZero : conditionalGain parent ≡ zero
    rightIdentity : oldInformation parent + zero ≡ oldInformation parent
  open SchurIncrementCertificate parent using (_+_)
open ZeroInnovationCertificate public

redundantSensorAddsNoInformation :
  ∀ {ℓ} {Scalar : Set ℓ}
    (certificate : ZeroInnovationCertificate Scalar) →
    newInformation (parent certificate) ≡ oldInformation (parent certificate)
redundantSensorAddsNoInformation certificate
  rewrite schurBlockIdentity (parent certificate)
        | gainIsZero certificate =
    rightIdentity certificate
