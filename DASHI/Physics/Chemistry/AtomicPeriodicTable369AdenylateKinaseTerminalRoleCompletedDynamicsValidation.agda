module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseTerminalRoleCompletedDynamicsValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseTerminalRoleCompletedDynamicsExact as P

routeRegression :
  P.AdKTerminalRoleCompletedDynamicsBoundary.primaryRouteReachesTaggedTerminalRole
    P.canonicalAdKTerminalRoleCompletedDynamicsBoundary
  ≡ true
  × P.AdKTerminalRoleCompletedDynamicsBoundary.alternativeRouteReachesTaggedTerminalRole
    P.canonicalAdKTerminalRoleCompletedDynamicsBoundary
  ≡ true
  × P.AdKTerminalRoleCompletedDynamicsBoundary.terminalRoleRetainsFigureClosedRegion
    P.canonicalAdKTerminalRoleCompletedDynamicsBoundary
  ≡ true
routeRegression = refl , refl , refl

firewallRegression :
  P.AdKTerminalRoleCompletedDynamicsBoundary.equationXiDefinitionallyEqualsFigureZeta
    P.canonicalAdKTerminalRoleCompletedDynamicsBoundary
  ≡ false
  × P.AdKTerminalRoleCompletedDynamicsBoundary.equationXiAssignedPerStateDLn
    P.canonicalAdKTerminalRoleCompletedDynamicsBoundary
  ≡ false
  × P.AdKTerminalRoleCompletedDynamicsBoundary.roleCompletionEqualsExperimentalKineticMechanism
    P.canonicalAdKTerminalRoleCompletedDynamicsBoundary
  ≡ false
firewallRegression = refl , refl , refl
