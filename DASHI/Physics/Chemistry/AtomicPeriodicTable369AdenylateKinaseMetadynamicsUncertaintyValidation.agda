module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseMetadynamicsUncertaintyValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseMetadynamicsUncertaintyExact as P

uncertaintyRegression :
  P.AdKMetadynamicsUncertaintyBoundary.freeEnergyErrorHalfKcalMolPaid
    P.canonicalAdKMetadynamicsUncertaintyBoundary
  ≡ true
  × P.AdKMetadynamicsUncertaintyBoundary.uncertaintyAppliesToMetadynamicsFreeEnergy
    P.canonicalAdKMetadynamicsUncertaintyBoundary
  ≡ true
uncertaintyRegression = refl , refl

firewallRegression :
  P.AdKMetadynamicsUncertaintyBoundary.uncertaintyCreatesMissingStateEnergy
    P.canonicalAdKMetadynamicsUncertaintyBoundary
  ≡ false
  × P.AdKMetadynamicsUncertaintyBoundary.errorBoundMakesVisualReadoutExact
    P.canonicalAdKMetadynamicsUncertaintyBoundary
  ≡ false
  × P.AdKMetadynamicsUncertaintyBoundary.relativeEnergyBecomesAbsoluteThermodynamics
    P.canonicalAdKMetadynamicsUncertaintyBoundary
  ≡ false
firewallRegression = refl , refl , refl
