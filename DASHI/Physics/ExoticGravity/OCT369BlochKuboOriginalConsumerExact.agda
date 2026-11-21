module DASHI.Physics.ExoticGravity.OCT369BlochKuboOriginalConsumerExact where

-- Source-owned existing producer interface, NOT a new Bloch/Kubo theorem.
-- CoTaSe2 3D Wannier response and topology owners are reused as conditional
-- algorithms, not as PtMn3 observations. OCT P0.18 supplies unfitted H(k).
-- Original Sato/Hayami 2026 full mixed kh-space octupole remains OPEN.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoWannier3DResponseExact as W
import DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoNonAbelianTopologyExact as T

nativeAnalyticWannierDerivative :
  W.analyticWannierDerivativeImplemented W.canonicalWannier3DResponseContract ≡ true
nativeAnalyticWannierDerivative = refl

nativeBerryKuboBandConsumer :
  W.berryCurvatureImplemented W.canonicalWannier3DResponseContract ≡ true
nativeBerryKuboBandConsumer = refl

nativeIsolatedSubspaceRequirement :
  T.selectedSubspaceMustBeIsolatedFromComplement T.canonicalNonAbelianTopologyContract ≡ true
nativeIsolatedSubspaceRequirement = refl

nativePolarWilsonTransport :
  T.wilsonLoopPolarTransportImplemented T.canonicalNonAbelianTopologyContract ≡ true
nativePolarWilsonTransport = refl

nativeMetallicKuboNotAutomaticallyHall :
  T.metallicHallConductivityImplementedHere T.canonicalNonAbelianTopologyContract ≡ false
nativeMetallicKuboNotAutomaticallyHall = refl

record OCT369BlochKuboSourcePayment : Set where
  constructor oct369-bloch-kubo-payment
  field
    nativeBandDerivativeConsumerExists : Bool
    nativeBerryBandConsumerExists : Bool
    nativeDegeneracySafeProjectorExists : Bool
    nativeWilsonLoopConsumerExists : Bool
    periodicP018TrialHamiltonianExists : Bool
    originalPtMn3LiteralWannierFitted : Bool
    satoHayamiFullMagneticOctupoleEq11Computed : Bool
    sourceCalibratedMechanicalOctupoleForce : Bool
    observedGravitationalAnomaly : Bool

canonicalOCT369BlochKuboPayment : OCT369BlochKuboSourcePayment
canonicalOCT369BlochKuboPayment =
  oct369-bloch-kubo-payment true true true true true false false false false
