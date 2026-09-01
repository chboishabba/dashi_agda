module DASHI.Moonshine.Monster3BFiniteSchrodingerIrreducibilityBidiCutExact where

------------------------------------------------------------------------
-- BIDI OR-CUT FOR THE CONCRETE SCHRODINGER IRREDUCIBILITY CONSUMER
--
-- Two ordinary finite-dimensional routes may close the same theorem:
--
--   A. finite delta synthesis after the Monster-specific delta orbit; or
--   B. invariant-subspace projector attachment, consumed by the already-proved
--      scalar commutant / zero-or-identity projector theorem.
--
-- Downstream consumers receive one normalized irreducibility authority and do
-- not depend on which proof route won the search.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as V
import DASHI.Moonshine.Monster3BFiniteSchrodingerDeltaExtractionExact as Extract
import DASHI.Moonshine.Monster3BFiniteSchrodingerIrreducibilityAssemblyExact as DeltaRoute
import DASHI.Moonshine.Monster3BFiniteSchrodingerProjectorIrreducibilityBidiExact as ProjectorRoute

record SchrodingerIrreducibilityAuthority : Set₁ where
  constructor schrodinger-irreducibility-authority
  field
    everyNonzeroInvariantSubspaceIsWhole :
      ∀ {Member}
        (inv : V.HeisenbergInvariantSubspace Member) →
        Extract.NonzeroInvariantVector inv →
        DeltaRoute.WholeSchrodingerSubspace Member
open SchrodingerIrreducibilityAuthority public

fromFiniteDeltaSynthesis :
  DeltaRoute.FiniteDeltaSynthesis → SchrodingerIrreducibilityAuthority
fromFiniteDeltaSynthesis finite =
  let receipt = DeltaRoute.assembleSchrodingerIrreducibility finite
  in schrodinger-irreducibility-authority
      (DeltaRoute.everyNonzeroInvariantSubspaceIsWhole receipt)

fromExistingProjectorMachinery :
  ProjectorRoute.ExistingFiniteProjectorMachinery →
  SchrodingerIrreducibilityAuthority
fromExistingProjectorMachinery machinery =
  let receipt = ProjectorRoute.assembleProjectorSchrodingerIrreducibility machinery
  in schrodinger-irreducibility-authority
      (ProjectorRoute.everyNonzeroInvariantSubspaceIsWhole receipt)

data IrreducibilityRoute : Set where
  finiteDeltaSynthesisRoute : IrreducibilityRoute
  commutingProjectorRoute : IrreducibilityRoute

data RouteState : Set where
  MonsterSpecificClosed ordinaryAttachmentOpen consumerBlocked : RouteState

routeState : IrreducibilityRoute → RouteState
routeState finiteDeltaSynthesisRoute = ordinaryAttachmentOpen
routeState commutingProjectorRoute = ordinaryAttachmentOpen

record IrreducibilityBidiCutBoundary : Set where
  constructor irreducibility-bidi-cut-boundary
  field
    MonsterSpecificDeltaExtractionClosed : Bool
    MonsterSpecificFullDeltaOrbitClosed : Bool
    finiteDeltaRouteAvailable : Bool
    projectorNoGoRouteAvailable : Bool
    downstreamConsumerRouteIndependent : Bool
    eitherOrdinaryAttachmentSilentlyAssumed : Bool
open IrreducibilityBidiCutBoundary public

canonicalIrreducibilityBidiCutBoundary : IrreducibilityBidiCutBoundary
canonicalIrreducibilityBidiCutBoundary =
  irreducibility-bidi-cut-boundary true true true true true false
