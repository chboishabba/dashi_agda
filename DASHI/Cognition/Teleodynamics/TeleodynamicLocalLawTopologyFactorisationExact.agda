module DASHI.Cognition.Teleodynamics.TeleodynamicLocalLawTopologyFactorisationExact where

------------------------------------------------------------------------
-- TELEODYNAMIC LOCAL-LAW / COUPLING-TOPOLOGY FACTORISATION
--
-- Productive cross-pollination from sibling IIT/phi PR #1148:
-- that branch now keeps recurrent gluing topology separate from the local
-- synthesis law, and its matched finite scan reports different system-phi
-- behaviour when XOR/OR/AND/triXor are placed on a fixed recurrent fabric.
--
-- This owner imports no sibling IIT theorem authority.  It pays the generic
-- structural statement needed by the Michels/LILA lane itself:
--
--     coupling topology != local state-update law != resulting future.
--
-- Hence architecture/coupling similarity cannot by itself determine a local
-- transition rule or future trace.  A model-facing comparison must declare all
-- three coordinates separately.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)

------------------------------------------------------------------------
-- 1. Minimal recurrent fabric used only as an exact counterexample.
------------------------------------------------------------------------

record BoolTriple : Set where
  constructor triple
  field
    a : Bool
    b : Bool
    c : Bool

open BoolTriple public

xorB : Bool → Bool → Bool
xorB false false = false
xorB false true = true
xorB true false = true
xorB true true = false

orB : Bool → Bool → Bool
orB false false = false
orB false true = true
orB true false = true
orB true true = true

-- Fixed recurrent wiring:
--   A[t+1] = C[t]
--   B[t+1] = A[t]
--   C[t+1] = mu(A[t],B[t]).
-- Only the local law mu varies.
recurrentStep : (Bool → Bool → Bool) → BoolTriple → BoolTriple
recurrentStep μ s = triple (c s) (a s) (μ (a s) (b s))

sameTopologyWitness : String
sameTopologyWitness = "A'=C; B'=A; C'=mu(A,B)"

counterexampleState : BoolTriple
counterexampleState = triple true true false

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

-- Same recurrent topology, different local law, different next state.
xorOrCounterexample :
  recurrentStep xorB counterexampleState ≡
  recurrentStep orB counterexampleState →
  ⊥
xorOrCounterexample h = falseNotTrue (cong c h)

xorOrSameTopologyDifferentFuture : Set
xorOrSameTopologyDifferentFuture =
  recurrentStep xorB counterexampleState ≡
  recurrentStep orB counterexampleState →
  ⊥

------------------------------------------------------------------------
-- 2. Generic model-facing factorisation.
------------------------------------------------------------------------

record TeleodynamicLocalLawTopologyFactorisation : Set where
  constructor teleodynamic-local-law-topology-factorisation
  field
    stateCarrierLabel : String
    couplingTopologyLabel : String
    localUpdateLawLabel : String
    interventionLabel : String
    observerOrConsumerLabel : String
    resultingFutureTraceLabel : String
    topologyReceipt : String
    localLawReceipt : String
    transitionReceipt : String

open TeleodynamicLocalLawTopologyFactorisation public

canonicalFactorisation : TeleodynamicLocalLawTopologyFactorisation
canonicalFactorisation =
  teleodynamic-local-law-topology-factorisation
    "declared learner/system state"
    "declared directed coupling/gluing graph"
    "declared local state-update/synthesis law"
    "declared intervention/query action"
    "declared decoder or future consumer"
    "held-out transition trace"
    "topology fixed independently of local law"
    "local law fixed independently of topology"
    "transition evaluated from both topology and local law"

------------------------------------------------------------------------
-- 3. Sibling IIT receipt and authority boundary.
------------------------------------------------------------------------

record MatchedGateSiblingReceipt : Set where
  constructor matched-gate-sibling-receipt
  field
    sourcePR : Nat
    fixedRecurrentFabricReported : Bool
    localGateVariedReported : Bool
    xorOrAndComparedReported : Bool
    ternaryTriXorComparedReported : Bool
    systemPhiChangesUnderFixedTopologyReported : Bool
    importedAsLocalKernelTheorem : Bool

open MatchedGateSiblingReceipt public

canonicalMatchedGateSiblingReceipt : MatchedGateSiblingReceipt
canonicalMatchedGateSiblingReceipt =
  matched-gate-sibling-receipt
    1148 true true true true true false

record LocalLawTopologyBoundary : Set where
  constructor local-law-topology-boundary
  field
    sameTopologyDifferentLocalLawCanChangeFuture : Bool
    topologyDeterminesLocalTransitionByDefinition : Bool
    localLawDeterminesCouplingTopologyByDefinition : Bool
    sameArchitectureSimilarityDeterminesLocalLaw : Bool
    sameArchitectureSimilarityDeterminesFutureTrace : Bool
    topologyAndLocalLawMustBeDeclaredSeparately : Bool
    observerConsumerMustBeDeclaredSeparately : Bool
    iitMatchedGateScanReportedInSibling : Bool
    siblingReceiptCreatesLocalIITTheorem : Bool
    localLawTopologyFactorisationCreatesPhenomenalIdentity : Bool

open LocalLawTopologyBoundary public

canonicalBoundary : LocalLawTopologyBoundary
canonicalBoundary =
  local-law-topology-boundary
    true
    false false false false
    true true
    true
    false false

------------------------------------------------------------------------
-- 4. Experiment consequence.
------------------------------------------------------------------------

record LocalLawTopologyMatchedExperiment : Set where
  constructor local-law-topology-matched-experiment
  field
    sameStateSet : Bool
    sameCouplingTopology : Bool
    sameParameterBudget : Bool
    sameInterventionFamily : Bool
    sameDeclaredConsumer : Bool
    varyOnlyLocalLaw : Bool
    reportTransitionDifference : Bool
    reportConsumerDifference : Bool
    optionallyReportIITDifference : Bool
    architectureScalarAloneCountsAsExplanation : Bool

open LocalLawTopologyMatchedExperiment public

canonicalMatchedExperiment : LocalLawTopologyMatchedExperiment
canonicalMatchedExperiment =
  local-law-topology-matched-experiment
    true true true true true true true true true false
