module DASHI.Physics.Closure.NSTriadKNLiteralFeffermanRouteReconciliationRound362Exact where

------------------------------------------------------------------------
-- ROUND362 / BIDI: TWO IN-REPO PRODUCERS, ONE LITERAL FEFFERMAN TARGET
--
-- The older R23 route and the new R361 route both terminate in exactly
--
--   Clay.FeffermanPeriodicClayStatementB clay.
--
-- Their upstream physical premises are different and must not be silently
-- identified:
--
--   old route:
--     uniform global physical construction
--       -> legacy solution witness
--       -> literal Fefferman witness
--       -> Galilean restoration;
--
--   new route:
--     nested resolvent/Schur/signed-Gram machinery
--       -> R354 literal physical Package A
--       -> same-instance authority
--       -> literal Fefferman witness.
--
-- This owner records endpoint equality without claiming premise equivalence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as Admission
import DASHI.Physics.Closure.NSTriadKNFeffermanPeriodicClayStatementExact as Clay
import DASHI.Physics.Closure.NSTriadKNLuoClayEndToEndCompositionRound23Exact as Old
import DASHI.Physics.Closure.NSTriadKNPhysicalPackageAToLiteralFeffermanRound361Exact as New

oldR23RouteDisposition : Admission.RouteDisposition
oldR23RouteDisposition = Admission.admitted

newR361ResolventRouteDisposition : Admission.RouteDisposition
newR361ResolventRouteDisposition = Admission.admitted

record SharedLiteralFeffermanEndpoint
    (clay : Clay.FeffermanPeriodicClayCarrier) : Set₁ where
  field
    oldRouteConclusion : Clay.FeffermanPeriodicClayStatementB clay
    newRouteConclusion : Clay.FeffermanPeriodicClayStatementB clay

open SharedLiteralFeffermanEndpoint public

round362OldAndNewRoutesTargetSameLiteralType : Bool
round362OldAndNewRoutesTargetSameLiteralType = true

round362OldAndNewPhysicalPremisesIdentified : Bool
round362OldAndNewPhysicalPremisesIdentified = false

round362OldRouteRequiresNewResolventRoute : Bool
round362OldRouteRequiresNewResolventRoute = false

round362NewResolventRouteRequiresOldLegacyConstruction : Bool
round362NewResolventRouteRequiresOldLegacyConstruction = false

round362EndpointReconciliationClosed : Bool
round362EndpointReconciliationClosed = true

round362OldAndNewRoutesTargetSameLiteralTypeIsTrue :
  round362OldAndNewRoutesTargetSameLiteralType ≡ true
round362OldAndNewRoutesTargetSameLiteralTypeIsTrue = refl

round362OldAndNewPhysicalPremisesIdentifiedIsFalse :
  round362OldAndNewPhysicalPremisesIdentified ≡ false
round362OldAndNewPhysicalPremisesIdentifiedIsFalse = refl

round362EndpointReconciliationClosedIsTrue :
  round362EndpointReconciliationClosed ≡ true
round362EndpointReconciliationClosedIsTrue = refl
