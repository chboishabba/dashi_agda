module DASHI.Physics.Closure.NSPeriodicComplementaryBoundaryCoincidence where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Coincidence of complementary packet and off-packet boundary faces.
--
-- If rho + eta = 1 for the state and rho* + eta* = 1 for the thresholds,
-- then rho = rho* iff eta = eta*.  Additive cancellation proves this without
-- division.  Combined with the quotient-numerator duality theorem, the two
-- normalized faces share one location and one inward-sign estimate.
------------------------------------------------------------------------

record ComplementaryBoundaryInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    packetFraction offPacketFraction totalFraction : Scalar A
    packetThreshold offPacketThreshold : Scalar A

    cancelLeftEquality : ∀ {a b c} →
      _+_ A a b ≡ _+_ A a c → b ≡ c

    cancelRightEquality : ∀ {a b c} →
      _+_ A a c ≡ _+_ A b c → a ≡ b

    statePartition :
      _+_ A packetFraction offPacketFraction ≡ totalFraction

    thresholdPartition :
      _+_ A packetThreshold offPacketThreshold ≡ totalFraction

open ComplementaryBoundaryInputs public

packetBoundaryImpliesOffPacketBoundary :
  ∀ {A : AbsorptionArithmetic} →
  (C : ComplementaryBoundaryInputs A) →
  packetFraction C ≡ packetThreshold C →
  offPacketFraction C ≡ offPacketThreshold C
packetBoundaryImpliesOffPacketBoundary {A = A} C packetFace =
  cancelLeftEquality C aligned
  where
  aligned :
    _+_ A (packetThreshold C) (offPacketFraction C)
    ≡
    _+_ A (packetThreshold C) (offPacketThreshold C)
  aligned =
    trans
      (cong
        (λ packet → _+_ A packet (offPacketFraction C))
        (sym packetFace))
      (trans
        (statePartition C)
        (sym (thresholdPartition C)))

offPacketBoundaryImpliesPacketBoundary :
  ∀ {A : AbsorptionArithmetic} →
  (C : ComplementaryBoundaryInputs A) →
  offPacketFraction C ≡ offPacketThreshold C →
  packetFraction C ≡ packetThreshold C
offPacketBoundaryImpliesPacketBoundary {A = A} C offFace =
  cancelRightEquality C aligned
  where
  aligned :
    _+_ A (packetFraction C) (offPacketThreshold C)
    ≡
    _+_ A (packetThreshold C) (offPacketThreshold C)
  aligned =
    trans
      (cong
        (λ off → _+_ A (packetFraction C) off)
        (sym offFace))
      (trans
        (statePartition C)
        (sym (thresholdPartition C)))

packetAndOffPacketFacesCoincide :
  ∀ {A : AbsorptionArithmetic} →
  (C : ComplementaryBoundaryInputs A) →
  (packetFraction C ≡ packetThreshold C →
    offPacketFraction C ≡ offPacketThreshold C)
  ×
  (offPacketFraction C ≡ offPacketThreshold C →
    packetFraction C ≡ packetThreshold C)
packetAndOffPacketFacesCoincide C =
  packetBoundaryImpliesOffPacketBoundary C ,
  offPacketBoundaryImpliesPacketBoundary C

------------------------------------------------------------------------
-- Status: complementary normalized faces are proved identical.  For the exact
-- 64/100 and 36/100 tuple, the boundary PDE program requires one packet/off
-- quotient-numerator sign, not two independent face estimates.
------------------------------------------------------------------------

complementaryBoundaryCoincidenceLevel : ProofLevel
complementaryBoundaryCoincidenceLevel = machineChecked
