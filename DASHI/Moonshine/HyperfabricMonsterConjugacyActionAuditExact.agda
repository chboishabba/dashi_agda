module DASHI.Moonshine.HyperfabricMonsterConjugacyActionAuditExact where

------------------------------------------------------------------------
-- HYPERFABRIC ACTION / MONSTER CONJUGACY AUDIT
--
-- The comparison object is the already-formalised action on the ternary
-- hypercube/hyperfabric carrier, not the numeral 369.  This owner packages
-- the exact action-level invariants that can legitimately be compared with
-- Monster conjugacy/character data, while keeping the Monster-module claim
-- explicitly open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Base369Ternary27StratifiedFibreHolonomyExact as Holonomy
import DASHI.Moonshine.Base369MonsterFineCarrierEquivarianceAuditExact as Fine
import DASHI.Moonshine.Monster3BCyclicFourierDyadicBridgeExact as ThreeB

------------------------------------------------------------------------
-- 1. Literal hyperfabric transformations already present in the repo.
------------------------------------------------------------------------

data FabricGenerator : Set where
  swapAxy : FabricGenerator
  flipAx  : FabricGenerator

applyFabricGenerator :
  FabricGenerator → Geometry.TernaryHyperformalPoint → Geometry.TernaryHyperformalPoint
applyFabricGenerator swapAxy = Holonomy.swapAppraisalAXY
applyFabricGenerator flipAx  = Holonomy.flipAppraisalAX

applyTwo :
  FabricGenerator → FabricGenerator →
  Geometry.TernaryHyperformalPoint → Geometry.TernaryHyperformalPoint
applyTwo first second p =
  applyFabricGenerator first (applyFabricGenerator second p)

------------------------------------------------------------------------
-- 2. The action is genuinely noncommutative on the literal carrier.
------------------------------------------------------------------------

noncommutingSeed : Geometry.TernaryHyperformalPoint
noncommutingSeed = Holonomy.fibreSeed

flipThenSwap : Geometry.TernaryHyperformalPoint
flipThenSwap = applyTwo swapAxy flipAx noncommutingSeed

swapThenFlip : Geometry.TernaryHyperformalPoint
swapThenFlip = applyTwo flipAx swapAxy noncommutingSeed

formalisedGeneratorsDoNotCommuteAtSeed :
  flipThenSwap ≡ swapThenFlip → ⊥
formalisedGeneratorsDoNotCommuteAtSeed = Holonomy.orderedFibreEndpointsDiffer

------------------------------------------------------------------------
-- 3. Action signatures are the correct conjugacy-facing observables.
--
-- A future finite closure of the generated action group can inhabit these
-- fields with exact element order, fixed-point count, cycle signature and
-- linearised trace.  They are intentionally not inferred from cardinalities.
------------------------------------------------------------------------

record FabricActionSignature : Set where
  constructor fabricActionSignature
  field
    elementOrder : Nat
    fixedPointCount : Nat
    cycleSignatureCode : Nat
    linearisedTraceCode : Nat
open FabricActionSignature public

record FabricConjugacyProbe (Element : Set) : Set₁ where
  constructor fabricConjugacyProbe
  field
    signature : Element → FabricActionSignature
    Conjugate : Element → Element → Set
    conjugatePreservesOrder :
      ∀ {g h} → Conjugate g h → elementOrder (signature g) ≡ elementOrder (signature h)
    conjugatePreservesFixedPoints :
      ∀ {g h} → Conjugate g h → fixedPointCount (signature g) ≡ fixedPointCount (signature h)
    conjugatePreservesCycleSignature :
      ∀ {g h} → Conjugate g h → cycleSignatureCode (signature g) ≡ cycleSignatureCode (signature h)
    conjugatePreservesTrace :
      ∀ {g h} → Conjugate g h → linearisedTraceCode (signature g) ≡ linearisedTraceCode (signature h)

------------------------------------------------------------------------
-- 4. The existing 3B lane supplies a genuine external calibration target.
------------------------------------------------------------------------

monster3BIrrepDimension : Nat
monster3BIrrepDimension = 196883

monster3BTrivialMultiplicity : Nat
monster3BTrivialMultiplicity = 65663

monster3BNontrivialMultiplicity : Nat
monster3BNontrivialMultiplicity = 65610

monster3BCharacterTrace : Nat
monster3BCharacterTrace = 53

monster3BDimensionSplits :
  monster3BIrrepDimension
  ≡ monster3BTrivialMultiplicity
  + monster3BNontrivialMultiplicity
  + monster3BNontrivialMultiplicity
monster3BDimensionSplits = refl

monster3BMultiplicityDefect :
  monster3BTrivialMultiplicity
  ≡ monster3BCharacterTrace + monster3BNontrivialMultiplicity
monster3BMultiplicityDefect = refl

------------------------------------------------------------------------
-- 5. Candidate fusion is a typed receipt, not an equality-by-cardinality.
------------------------------------------------------------------------

data MonsterClassAnchor : Set where
  monster3B : MonsterClassAnchor

record CandidateClassFusion (Element : Set) : Set₁ where
  constructor candidateClassFusion
  field
    selectedElement : Element
    targetClass : MonsterClassAnchor
    orderCompatible : Set
    phaseConjugationCompatible : Set
    characterTraceCompatible : Set

------------------------------------------------------------------------
-- 6. Current boundary.
------------------------------------------------------------------------

record HyperfabricMonsterConjugacyBoundary : Set where
  constructor hyperfabricMonsterConjugacyBoundary
  field
    literalHyperformalCarrierUsed : Bool
    literalNoncommutingGeneratorsUsed : Bool
    actionSignatureInterfaceConstructed : Bool
    conjugacyInvariantInterfaceConstructed : Bool
    existing3BCharacterCalibrationRecorded : Bool
    finiteGeneratedActionGroupEnumerated : Bool
    hyperfabricConjugacyClassesEnumerated : Bool
    all194MonsterClassesCompared : Bool
    classFusionToMonsterConstructed : Bool
    fullMonsterActionOnHyperfabricEstablished : Bool
    cardinalityAlonePromotesMonsterAction : Bool

canonicalHyperfabricMonsterConjugacyBoundary :
  HyperfabricMonsterConjugacyBoundary
canonicalHyperfabricMonsterConjugacyBoundary =
  hyperfabricMonsterConjugacyBoundary
    true true true true true
    false false false false false false

------------------------------------------------------------------------
-- 7. Cross-check the existing fine-carrier authority boundary remains active.
------------------------------------------------------------------------

sameCardinalityDoesNotSupplyMonsterAction :
  Fine.FineCarrierBidiBoundary.fullMonsterActionOnHyperfabricEstablished
    Fine.canonicalFineCarrierBidiBoundary
  ≡ false
sameCardinalityDoesNotSupplyMonsterAction = refl

existingThreeBProbeAvailable : Bool
existingThreeBProbeAvailable = true
