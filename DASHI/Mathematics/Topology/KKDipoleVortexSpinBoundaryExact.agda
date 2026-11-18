module DASHI.Mathematics.Topology.KKDipoleVortexSpinBoundaryExact where

-- This is a deliberately small logical boundary, not a 5D KK solution.
-- It says: adding two fields with zero azimuthal component cannot produce
-- an azimuthal component. A collinear static point dipole and an imposed
-- uniform axial field both have this property away from the point source.
-- The physical identification of field components with a coordinate
-- representation is an EXTERNAL prerequisite, not proven here.
--
-- The module also makes explicit that the sign of a quantum state under
-- a full rotation is additional data; integer topological winding alone
-- does not constitute a proof of fermionic spin or exchange statistics.

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)

record AdditiveAzimuth {ℓ : Level} : Set (lsuc ℓ) where
  field
    Carrier : Set ℓ
    zero : Carrier
    _⊕_ : Carrier → Carrier → Carrier
    zeroPlusZero : (zero ⊕ zero) ≡ zero

module NoCompulsorySpiral {ℓ : Level} (A : AdditiveAzimuth {ℓ}) where
  open AdditiveAzimuth A

  record AxisymmetricPair : Set ℓ where
    field
      dipolePhi : Carrier
      imposedPhi : Carrier
      dipolePhiZero : dipolePhi ≡ zero
      imposedPhiZero : imposedPhi ≡ zero

  noInducedAzimuthFromZeroSummands :
    (p : AxisymmetricPair) →
    (AxisymmetricPair.dipolePhi p ⊕ AxisymmetricPair.imposedPhi p) ≡ zero
  noInducedAzimuthFromZeroSummands record
    { dipolePhi = .zero
    ; imposedPhi = .zero
    ; dipolePhiZero = refl
    ; imposedPhiZero = refl
    } = zeroPlusZero

-- Quantization needs a genuine rotation action on a physical configuration
-- space, not just an integer winding label. This data record deliberately
-- makes that additional evidence explicit and carries no existence claim.
record RotationQuantizationGate {ℓ : Level} : Set (lsuc ℓ) where
  field
    Configuration : Set ℓ
    State : Set ℓ
    rotate2Pi : State → State
    rotate4Pi : State → State
    negative : State → State
    spinorialRotation : (ψ : State) → rotate2Pi ψ ≡ negative ψ
    doubleRotationTrivial : (ψ : State) → rotate4Pi ψ ≡ ψ

-- Open physical gates not packed here: noncontractible 2π loop in actual
-- configuration space, unitary Hilbert representation, continuity,
-- physical angular-momentum generator, exchange path, spin/statistics,
-- original KK action and exact solution, nonlinear stability.
