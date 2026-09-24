module DASHI.Physics.Closure.NSPeriodicDifferenceEnergyProducerExact where

------------------------------------------------------------------------
-- RELEASED D / D7-D13 LEAVES -> PERIODIC DIFFERENCE-ENERGY RULES
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSOpenAI2026ReleasedPeriodicEnergyUniquenessKernelExact as D

record ActualPeriodicDifferenceEnergyLeaves
    (S : D.PeriodicDifferenceEnergySurface) : Set₁ where
  field
    candidate comparator : D.State S

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

    buildCouplingBound : CouplingBound
    zeroInitialDifference : ZeroInitialDifference

    gronwallZero :
      DifferenceEnergyBalance →
      CouplingBound →
      ZeroInitialDifference →
      GronwallConclusion

    gronwallImpliesPreSingularAgreement :
      GronwallConclusion →
      D.SameBeforeSingularTime S candidate comparator

open ActualPeriodicDifferenceEnergyLeaves public

actualPeriodicDifferenceEnergyRules :
  ∀ {S} →
  ActualPeriodicDifferenceEnergyLeaves S →
  D.PeriodicDifferenceEnergyRules S
actualPeriodicDifferenceEnergyRules L = record
  { D.candidate = candidate L
  ; D.comparator = comparator L
  ; D.TransportCancellation = TransportCancellation L
  ; D.PressureCancellation = PressureCancellation L
  ; D.ViscousDissipationIdentity = ViscousDissipationIdentity L
  ; D.DifferenceEnergyBalance = DifferenceEnergyBalance L
  ; D.CouplingBound = CouplingBound L
  ; D.ZeroInitialDifference = ZeroInitialDifference L
  ; D.GronwallConclusion = GronwallConclusion L
  ; D.periodicTransportCancellation = periodicTransportCancellation L
  ; D.periodicPressureCancellation = periodicPressureCancellation L
  ; D.periodicViscousDissipation = periodicViscousDissipation L
  ; D.buildDifferenceEnergyBalance = buildDifferenceEnergyBalance L
  ; D.buildCouplingBound = buildCouplingBound L
  ; D.zeroInitialDifference = zeroInitialDifference L
  ; D.gronwallZero = gronwallZero L
  ; D.gronwallImpliesPreSingularAgreement =
      gronwallImpliesPreSingularAgreement L
  }

actualPeriodicPreSingularUniqueness :
  ∀ {S} →
  (L : ActualPeriodicDifferenceEnergyLeaves S) →
  D.SameBeforeSingularTime S (candidate L) (comparator L)
actualPeriodicPreSingularUniqueness L =
  D.periodicPreSingularUniqueness (actualPeriodicDifferenceEnergyRules L)

periodicDifferenceEnergyProducerCompilerClosed : Bool
periodicDifferenceEnergyProducerCompilerClosed = true

periodicIBPAnalyticLeavesInhabitedHere : Bool
periodicIBPAnalyticLeavesInhabitedHere = false

periodicCouplingAnalyticLeafInhabitedHere : Bool
periodicCouplingAnalyticLeafInhabitedHere = false

periodicGronwallAnalyticLeafInhabitedHere : Bool
periodicGronwallAnalyticLeafInhabitedHere = false

periodicDifferenceEnergyProducerIntroducesPostulate : Bool
periodicDifferenceEnergyProducerIntroducesPostulate = false

clayPromotion : Bool
clayPromotion = false
