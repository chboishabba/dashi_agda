module DASHI.Biology.IITCausalPantsFibreGluingExact where

------------------------------------------------------------------------
-- CAUSAL PANTS / FIBRE GLUING / LOCAL GATE SEPARATION
--
-- The key owner boundary is:
--
--   gluing / transport g     is NOT     local synthesis algebra mu.
--
-- A local trivalent causal cell has two input fibres and one output fibre:
--
--      A_p ----\
--               mu_p ----> C_p
--      B_p ----/
--
-- A gluing map only routes/identifies a source output with one input socket of
-- a later cell:
--
--      C_p --g--> A_q        or        C_p --g--> B_q.
--
-- No Boolean or ternary operation occurs in g itself.  XOR / OR / AND /
-- triXor live only in mu.  This makes fabric topology and local algebra
-- independently variable coordinates for matched IIT experiments.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import Base369 as Base
import DASHI.Biology.StateDependentMultiplexTransducer as Multiplex

------------------------------------------------------------------------
-- 1. Path-indexed fibre family.
------------------------------------------------------------------------

record FibreFamily (Path : Set) : Set₁ where
  field
    Fibre : Path → Set
open FibreFamily public

data InputPort : Set where
  inputA : InputPort
  inputB : InputPort

------------------------------------------------------------------------
-- 2. Local 2 -> 1 synthesis algebra at one path/step.
------------------------------------------------------------------------

record LocalSynthesisCell
    {Path : Set}
    (family : FibreFamily Path)
    (step : Path) : Set₁ where
  field
    combine : Fibre family step → Fibre family step → Fibre family step
open LocalSynthesisCell public

evaluateLocal :
  ∀ {Path : Set}
    {family : FibreFamily Path}
    {step : Path} →
  LocalSynthesisCell family step →
  Fibre family step → Fibre family step → Fibre family step
evaluateLocal cell = combine cell

------------------------------------------------------------------------
-- 3. Output -> input gluing is pure transport plus a target socket.
------------------------------------------------------------------------

record OutputInputGluing
    {Path : Set}
    (family : FibreFamily Path)
    (source target : Path) : Set₁ where
  field
    targetPort : InputPort
    transport : Fibre family source → Fibre family target
open OutputInputGluing public

record RoutedInput
    {Path : Set}
    (family : FibreFamily Path)
    (step : Path) : Set where
  constructor routed-input
  field
    routedPort : InputPort
    routedValue : Fibre family step
open RoutedInput public

routeOutput :
  ∀ {Path : Set}
    {family : FibreFamily Path}
    {source target : Path} →
  OutputInputGluing family source target →
  Fibre family source →
  RoutedInput family target
routeOutput gluing value =
  routed-input (targetPort gluing) (transport gluing value)

------------------------------------------------------------------------
-- 4. Two predecessor outputs can fill A and B of a target cell; only then is
--    the local synthesis operation evaluated.
------------------------------------------------------------------------

record TwoSourceInputGluing
    {Path : Set}
    (family : FibreFamily Path)
    (leftSource rightSource target : Path) : Set₁ where
  field
    leftWire : OutputInputGluing family leftSource target
    rightWire : OutputInputGluing family rightSource target
    leftTargetsA : targetPort leftWire ≡ inputA
    rightTargetsB : targetPort rightWire ≡ inputB
open TwoSourceInputGluing public

evaluateGluedCell :
  ∀ {Path : Set}
    {family : FibreFamily Path}
    {leftSource rightSource target : Path} →
  TwoSourceInputGluing family leftSource rightSource target →
  LocalSynthesisCell family target →
  Fibre family leftSource →
  Fibre family rightSource →
  Fibre family target
evaluateGluedCell wiring cell leftOutput rightOutput =
  combine cell
    (transport (leftWire wiring) leftOutput)
    (transport (rightWire wiring) rightOutput)

------------------------------------------------------------------------
-- 5. Identity transport fixture: same topology, gate can be swapped.
------------------------------------------------------------------------

data OneStep : Set where
  oneStep : OneStep

constantBoolFamily : FibreFamily OneStep
constantBoolFamily = record { Fibre = λ _ → Bool }

identityWireA : OutputInputGluing constantBoolFamily oneStep oneStep
identityWireA = record
  { targetPort = inputA
  ; transport = λ x → x
  }

identityWireB : OutputInputGluing constantBoolFamily oneStep oneStep
identityWireB = record
  { targetPort = inputB
  ; transport = λ x → x
  }

sameBoolWiring : TwoSourceInputGluing constantBoolFamily oneStep oneStep oneStep
sameBoolWiring = record
  { leftWire = identityWireA
  ; rightWire = identityWireB
  ; leftTargetsA = refl
  ; rightTargetsB = refl
  }

boolOr : Bool → Bool → Bool
boolOr false false = false
boolOr false true = true
boolOr true false = true
boolOr true true = true

boolAnd : Bool → Bool → Bool
boolAnd false false = false
boolAnd false true = false
boolAnd true false = false
boolAnd true true = true

boolXorCell : LocalSynthesisCell constantBoolFamily oneStep
boolXorCell = record { combine = Multiplex.xor }

boolOrCell : LocalSynthesisCell constantBoolFamily oneStep
boolOrCell = record { combine = boolOr }

boolAndCell : LocalSynthesisCell constantBoolFamily oneStep
boolAndCell = record { combine = boolAnd }

sameWiringXorTrueTrueIsFalse :
  evaluateGluedCell sameBoolWiring boolXorCell true true ≡ false
sameWiringXorTrueTrueIsFalse = refl

sameWiringOrTrueTrueIsTrue :
  evaluateGluedCell sameBoolWiring boolOrCell true true ≡ true
sameWiringOrTrueTrueIsTrue = refl

sameWiringAndTrueTrueIsTrue :
  evaluateGluedCell sameBoolWiring boolAndCell true true ≡ true
sameWiringAndTrueTrueIsTrue = refl

sameFabricDifferentLocalAlgebraChangesOutput :
  evaluateGluedCell sameBoolWiring boolXorCell true true
  ≡ evaluateGluedCell sameBoolWiring boolOrCell true true →
  ⊥
sameFabricDifferentLocalAlgebraChangesOutput ()

------------------------------------------------------------------------
-- 6. Ternary / 369 instantiation on the SAME abstract gluing interface.
------------------------------------------------------------------------

constantTriFamily : FibreFamily OneStep
constantTriFamily = record { Fibre = λ _ → Base.TriTruth }

triIdentityWireA : OutputInputGluing constantTriFamily oneStep oneStep
triIdentityWireA = record
  { targetPort = inputA
  ; transport = λ x → x
  }

triIdentityWireB : OutputInputGluing constantTriFamily oneStep oneStep
triIdentityWireB = record
  { targetPort = inputB
  ; transport = λ x → x
  }

sameTriWiring : TwoSourceInputGluing constantTriFamily oneStep oneStep oneStep
sameTriWiring = record
  { leftWire = triIdentityWireA
  ; rightWire = triIdentityWireB
  ; leftTargetsA = refl
  ; rightTargetsB = refl
  }

triXorCell : LocalSynthesisCell constantTriFamily oneStep
triXorCell = record { combine = Base.triXor }

triXorOnSameFabric :
  Base.TriTruth → Base.TriTruth → Base.TriTruth
triXorOnSameFabric = evaluateGluedCell sameTriWiring triXorCell

------------------------------------------------------------------------
-- 7. Path/circuit semantics are a separate layer again.
--
-- A fabric edge carries one gluing map from a source cell output to a target
-- input port.  A recurrent fabric is witnessed by a closed sequence of these
-- edges; recurrence is therefore a property of the gluing graph, not of XOR.
------------------------------------------------------------------------

record FabricEdge
    {Path : Set}
    (family : FibreFamily Path) : Set₁ where
  field
    sourceStep : Path
    targetStep : Path
    edgeGluing : OutputInputGluing family sourceStep targetStep
open FabricEdge public

record ClosedTwoStepCircuit
    {Path : Set}
    (family : FibreFamily Path)
    (first second : Path) : Set₁ where
  field
    forward : OutputInputGluing family first second
    backward : OutputInputGluing family second first
open ClosedTwoStepCircuit public

------------------------------------------------------------------------
-- 8. IIT partition/noising boundary.
--
-- IIT directional partitions operate on causal connections.  On this carrier,
-- those connections are represented by gluing edges.  Replacing a cut edge by
-- independent noise changes the transport kernel; it does not mutate the local
-- synthesis law.  The concrete probability kernel remains owned by the finite
-- IIT repertoire modules.
------------------------------------------------------------------------

data GluingEdgeStatus : Set where
  intactEdge : GluingEdgeStatus
  noisedByDirectionalPartition : GluingEdgeStatus

record PartitionedFabricEdge
    {Path : Set}
    (family : FibreFamily Path) : Set₁ where
  field
    originalEdge : FabricEdge family
    edgeStatus : GluingEdgeStatus
open PartitionedFabricEdge public

------------------------------------------------------------------------
-- 9. Promotion / interpretation boundary.
------------------------------------------------------------------------

record IITCausalPantsFibreBoundary : Set where
  constructor iit-causal-pants-fibre-boundary
  field
    localCellHasTwoInputsOneOutput : Bool
    gluingCarriesOutputToNamedInputPort : Bool
    gluingIsLocalGateByDefinition : Bool
    sameWiringCanHostDifferentBooleanGates : Bool
    sameAbstractWiringCanHostTriXor : Bool
    recurrenceBelongsToGluingGraph : Bool
    directionalPartitionCutsGluingConnection : Bool
    cuttingConnectionMutatesLocalGateByDefinition : Bool
    gluingTopologyAloneDeterminesIITPhi : Bool
    localGateAloneDeterminesIITPhi : Bool

open IITCausalPantsFibreBoundary public

canonicalIITCausalPantsFibreBoundary : IITCausalPantsFibreBoundary
canonicalIITCausalPantsFibreBoundary =
  iit-causal-pants-fibre-boundary
    true true false true true true true false false false

gluingIsNotGate :
  gluingIsLocalGateByDefinition canonicalIITCausalPantsFibreBoundary ≡ false
gluingIsNotGate = refl

partitionDoesNotRewriteGate :
  cuttingConnectionMutatesLocalGateByDefinition canonicalIITCausalPantsFibreBoundary ≡ false
partitionDoesNotRewriteGate = refl

neitherAxisAloneIsPhi :
  gluingTopologyAloneDeterminesIITPhi canonicalIITCausalPantsFibreBoundary ≡ false
  × localGateAloneDeterminesIITPhi canonicalIITCausalPantsFibreBoundary ≡ false
neitherAxisAloneIsPhi = refl , refl
