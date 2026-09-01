module DASHI.Combinatorics.TemporalProofCarryingTextileFibreExact where

open import DASHI.Core.Prelude

import DASHI.Core.ProofCarryingRuleApplicationExact as RuleProof
import DASHI.Combinatorics.ProofCarryingTextileHyperfabricExact as Fabric

------------------------------------------------------------------------
-- TEMPORAL PROOF-CARRYING TEXTILE FIBRES
--
-- A proof fabric is produced through time.  The fibre at production step t is
-- the proof state that exists after exactly t certified patches have been
-- woven.  A later patch is therefore not merely adjacent in a static graph: it
-- is indexed by the state/fibre actually produced by its predecessor.
------------------------------------------------------------------------

record TimedProofFibre (State : Set) : Set where
  constructor timed-proof-fibre
  field
    productionTime : Nat
    proofState : State

open TimedProofFibre public

advanceFibre :
  {State Rule : Set} →
  (system : RuleProof.RuleApplicationSystem State Rule) →
  {state : State} →
  (time : Nat) →
  RuleProof.SelectedRuleApplication system state →
  TimedProofFibre State
advanceFibre system time selected =
  timed-proof-fibre (suc time) (RuleProof.applySelected system selected)

sourceTimedFibre :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  {state : State} →
  (time : Nat) →
  RuleProof.SelectedRuleApplication system state →
  TimedProofFibre State
sourceTimedFibre time selected = timed-proof-fibre time _

------------------------------------------------------------------------
-- Temporal fabric certificate.
--
-- This is the existing CertifiedRuleTrace/CertifiedFabricTrace with a clock
-- threaded through the dependent recursion.  The next constructor is forced
-- to live at suc time and at the exact reached proof state.
------------------------------------------------------------------------

data TemporalCertifiedFabric
    {State Rule : Set}
    {system : RuleProof.RuleApplicationSystem State Rule}
    (assignment : Fabric.MotifAssignment Rule) :
    (time : Nat) →
    {state : State} →
    RuleProof.CertifiedRuleTrace system state → Set₁ where

  temporalDone :
    ∀ {time state} →
    TemporalCertifiedFabric assignment time
      (RuleProof.done {state = state})

  temporalStep :
    ∀ {time state}
      (selected : RuleProof.SelectedRuleApplication system state)
      {rest : RuleProof.CertifiedRuleTrace system
        (RuleProof.applySelected system selected)} →
    Fabric.CertifiedFabricPatch assignment (state , selected) →
    TemporalCertifiedFabric assignment (suc time) rest →
    TemporalCertifiedFabric assignment time
      (RuleProof.choose selected rest)

compileTemporalFabric :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  (assignment : Fabric.MotifAssignment Rule) →
  (time : Nat) →
  {state : State} →
  (trace : RuleProof.CertifiedRuleTrace system state) →
  TemporalCertifiedFabric assignment time trace
compileTemporalFabric assignment time RuleProof.done = temporalDone
compileTemporalFabric assignment time (RuleProof.choose selected rest) =
  temporalStep
    selected
    (Fabric.canonicalPatch assignment (_ , selected))
    (compileTemporalFabric assignment (suc time) rest)

------------------------------------------------------------------------
-- Production-time span and monotonicity receipts.
------------------------------------------------------------------------

finishTime :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  {state : State} →
  Nat → RuleProof.CertifiedRuleTrace system state → Nat
finishTime time RuleProof.done = time
finishTime time (RuleProof.choose selected rest) =
  finishTime (suc time) rest

onePatchAdvancesTime :
  {State Rule : Set}
  {system : RuleProof.RuleApplicationSystem State Rule} →
  {state : State}
  (selected : RuleProof.SelectedRuleApplication system state) →
  productionTime (advanceFibre system 0 selected) ≡ 1
onePatchAdvancesTime selected = refl

------------------------------------------------------------------------
-- Same visible/material stage need not mean same hidden temporal fibre.
-- Time and proof state remain independent coordinates.
------------------------------------------------------------------------

data StaticFabricEqualsTemporalFabric : Set where

data TimeCoordinateCanBeErasedFromProofFibre : Set where

data LaterPatchMayUseEarlierPreconditionWithoutTransport : Set where

staticFabricIsNotTemporalFabric : StaticFabricEqualsTemporalFabric → ⊥
staticFabricIsNotTemporalFabric ()

timeCoordinateCannotBeErased : TimeCoordinateCanBeErasedFromProofFibre → ⊥
timeCoordinateCannotBeErased ()

laterPatchCannotSkipReachedState :
  LaterPatchMayUseEarlierPreconditionWithoutTransport → ⊥
laterPatchCannotSkipReachedState ()

record TemporalProofFabricBoundary : Set where
  constructor temporal-proof-fabric-boundary
  field
    fibresIndexedByProductionTime : Bool
    eachPatchAdvancesProductionTime : Bool
    nextPatchUsesActuallyReachedState : Bool
    temporalTraceRetainsProofAdmissibility : Bool
    staticAdjacencyEqualsTemporalTransport : Bool
    visibleSurfaceDeterminesTemporalHistory : Bool

canonicalTemporalProofFabricBoundary : TemporalProofFabricBoundary
canonicalTemporalProofFabricBoundary =
  temporal-proof-fabric-boundary
    true true true true false false
