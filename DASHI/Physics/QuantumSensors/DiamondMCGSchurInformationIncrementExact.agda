module DASHI.Physics.QuantumSensors.DiamondMCGSchurInformationIncrementExact where

------------------------------------------------------------------------
-- P1/W1 conditional Schur information addition.
-- Classical mathematical prior art: Schur complement / block inverse.
-- Explicit certificate boundary: the owning covariance model must produce
-- the Schur identity and positive conditional variance independently.
-- Neither anatomy, NV hardware, nor experiment is certified here.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)

record SchurIncrementCertificate {ℓ : Level} (Scalar : Set ℓ) :
    Set (lsuc ℓ) where
  field
    add : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set ℓ
    oldInformation : Scalar
    newInformation : Scalar
    conditionalGain : Scalar
    innovationSquaredOverVariance : Scalar
    gainEqualsSchurQuotient :
      conditionalGain ≡ innovationSquaredOverVariance
    schurBlockIdentity :
      newInformation ≡ add oldInformation conditionalGain
    nonnegativeGain :
      oldInformation ≤ add oldInformation conditionalGain
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

record ZeroInnovationCertificate {ℓ : Level} (Scalar : Set ℓ) :
    Set (lsuc ℓ) where
  field
    parent : SchurIncrementCertificate Scalar
    zero : Scalar
    gainIsZero : conditionalGain parent ≡ zero
    rightIdentity :
      add parent (oldInformation parent) zero ≡ oldInformation parent
open ZeroInnovationCertificate public

redundantSensorAddsNoInformation :
  ∀ {ℓ} {Scalar : Set ℓ}
    (certificate : ZeroInnovationCertificate Scalar) →
    newInformation (parent certificate) ≡ oldInformation (parent certificate)
redundantSensorAddsNoInformation certificate
  rewrite schurBlockIdentity (parent certificate)
        | gainIsZero certificate =
    rightIdentity certificate
