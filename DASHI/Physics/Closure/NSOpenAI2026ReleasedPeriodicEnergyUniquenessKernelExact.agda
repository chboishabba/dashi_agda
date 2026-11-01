module DASHI.Physics.Closure.NSOpenAI2026ReleasedPeriodicEnergyUniquenessKernelExact where

------------------------------------------------------------------------
-- RELEASED D / PERIODIC DIFFERENCE-ENERGY UNIQUENESS KERNEL
--
-- This moves below candidate_no_solution_after_one.  The mathematical chain is
-- the released one:
--
--   periodic integration by parts
--   -> transport/pressure cancellation
--   -> viscous dissipation
--   -> difference-energy balance
--   -> coupling <= B E
--   -> Gronwall from E(0)=0
--   -> pre-singular agreement.
--
-- The theorem below is the exact composition.  The remaining native producers
-- are now the integration-by-parts identities and the Gronwall theorem, rather
-- than an opaque "periodic uniqueness" leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record PeriodicDifferenceEnergySurface : Set₁ where
  field
    Time : Set
    State : Set
    Energy : Time → Set
    Dissipation : Time → Set
    Coupling : Time → Set
    Growth : Time → Set

    SameBeforeSingularTime : State → State → Set

open PeriodicDifferenceEnergySurface public

record PeriodicDifferenceEnergyRules
    (S : PeriodicDifferenceEnergySurface) : Set₁ where
  field
    candidate comparator : State S

    TransportCancellation : Set
    PressureCancellation : Set
    ViscousDissipationIdentity : Set
    DifferenceEnergyBalance : Set
    CouplingBound : Set
    ZeroInitialDifference : Set
    GronwallConclusion : Set

    periodicTransportCancellation : TransportCancellation
    periodicPressureCancellation : PressureCancellation
    periodicViscousDissipation : ViscousDissipationIdentity

    buildDifferenceEnergyBalance :
      TransportCancellation →
      PressureCancellation →
      ViscousDissipationIdentity →
      DifferenceEnergyBalance

    buildCouplingBound :
      CouplingBound

    zeroInitialDifference :
      ZeroInitialDifference

    gronwallZero :
      DifferenceEnergyBalance →
      CouplingBound →
      ZeroInitialDifference →
      GronwallConclusion

    gronwallImpliesPreSingularAgreement :
      GronwallConclusion →
      SameBeforeSingularTime S candidate comparator

open PeriodicDifferenceEnergyRules public

periodicPreSingularUniqueness :
  ∀ {S} →
  (R : PeriodicDifferenceEnergyRules S) →
  SameBeforeSingularTime S (candidate R) (comparator R)
periodicPreSingularUniqueness R =
  let
    balance =
      buildDifferenceEnergyBalance R
        (periodicTransportCancellation R)
        (periodicPressureCancellation R)
        (periodicViscousDissipation R)

    zeroByGronwall =
      gronwallZero R
        balance
        (buildCouplingBound R)
        (zeroInitialDifference R)
  in
  gronwallImpliesPreSingularAgreement R zeroByGronwall

periodicEnergyUniquenessCompositionClosed : Bool
periodicEnergyUniquenessCompositionClosed = true

periodicIBPTransportPressureViscosityStillAnalytic : Bool
periodicIBPTransportPressureViscosityStillAnalytic = true

periodicGronwallStillAnalytic : Bool
periodicGronwallStillAnalytic = true

clayPromotion : Bool
clayPromotion = false

periodicEnergyUniquenessCompositionClosedIsTrue :
  periodicEnergyUniquenessCompositionClosed ≡ true
periodicEnergyUniquenessCompositionClosedIsTrue = refl
