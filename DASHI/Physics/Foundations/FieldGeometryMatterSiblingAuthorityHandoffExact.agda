module DASHI.Physics.Foundations.FieldGeometryMatterSiblingAuthorityHandoffExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- OPEN-SIBLING AUTHORITY HANDOFF
--
-- This owner records where already-existing open PRs own the next physical
-- frontier.  It intentionally imports no theorem/evidence authority from those
-- branches.  PR identity is a routing coordinate, not a proof or source claim.
------------------------------------------------------------------------

record SiblingAuthorityRoute : Set where
  constructor sibling-authority-route
  field
    prNumber : Nat
    programme : String
    ownedFrontier : String
    openSiblingObserved : Bool
    theoremAuthorityImportedHere : Bool
    empiricalAuthorityImportedHere : Bool

open SiblingAuthorityRoute public

magnoThermRoute : SiblingAuthorityRoute
magnoThermRoute = sibling-authority-route
  1158
  "MAGNOTHERM magnetocaloric / AMR vertical"
  "same-material constitutive calibration, loaded capacity/COP, field/flow map, lifetime and work recovery"
  true false false

fusionPropulsionRoute : SiblingAuthorityRoute
fusionPropulsionRoute = sibling-authority-route
  1126
  "FRC fusion reactor / propulsion literal max-cut"
  "same-shot FRC formation diagnostics, burn/channel calibration, nozzle exit distribution, coil reaction force, thrust and engineering-Q"
  true false false

rocketdyneRoute : SiblingAuthorityRoute
rocketdyneRoute = sibling-authority-route
  1116
  "Rocketdyne 1974 qualification / survivability max-cut"
  "local geometry, same-article constitutive laws, process/inspection history, calibrated thermo-structural model and qualification records"
  true false false

scientistAcquisitionRoute : SiblingAuthorityRoute
scientistAcquisitionRoute = sibling-authority-route
  929
  "twenty-scientist exact-key acquisition programme"
  "identity-bearing exact-object primary records and retained-person crossings; H2/H3 promotion remains separately gated"
  true false false

scientistCausalDiscriminatorRoute : SiblingAuthorityRoute
scientistCausalDiscriminatorRoute = sibling-authority-route
  915
  "missing/deceased scientist H0/H1/H2/H3 object-first discriminator"
  "same-programme object identity and pre-event operational/security evidence needed for H2/H3 promotion"
  true false false

record SiblingAuthorityHandoffBoundary : Set where
  constructor sibling-authority-handoff-boundary
  field
    openPRReferenceIsNotTheoremImport : Bool
    openPRReferenceIsNotEmpiricalImport : Bool
    siblingOwnershipAvoidsParallelOntology : Bool
    siblingMayBeDirectlyImportedOnlyAfterLandingOrExplicitRetarget : Bool
    scientistAdjacencyDoesNotPromoteCommonProgramme : Bool
    commonProgrammeDoesNotPromoteTargeting : Bool

open SiblingAuthorityHandoffBoundary public

canonicalSiblingAuthorityHandoffBoundary : SiblingAuthorityHandoffBoundary
canonicalSiblingAuthorityHandoffBoundary =
  sibling-authority-handoff-boundary true true true true true true
