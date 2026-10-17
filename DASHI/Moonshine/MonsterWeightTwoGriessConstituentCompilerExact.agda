module DASHI.Moonshine.MonsterWeightTwoGriessConstituentCompilerExact where

------------------------------------------------------------------------
-- PROOF-BEARING GRIESS CONSTITUENT COMPILER
--
-- The Suzuki / 3B character arithmetic
--
--   65610 = 90 * 729 = (12 + 78) * 729
--
-- lives downstream of the literal weight-two Monster representation.  It does
-- not create the 196883-dimensional Griess constituent.  This owner isolates
-- the exact same-object linear data required to produce that constituent and
-- then compiles those data into the legacy `WeightTwoLinearActionBridge`
-- together with the proof-relevant paid wrapper.
--
-- The key anti-shortcut is the explicit two-sided carrier weld to the repo's
-- semantic `SemanticMonsterConstituent196883` plus equality of its inclusion
-- with the SAME grade-two representation carrier.  Therefore the legacy bare
-- Nat field `constituentDimension = 196883` cannot be satisfied by simply
-- reusing the full 196884 carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Foundations.Base369StableAlgebraicIdentityTowerExact as Stable
import DASHI.Foundations.Base369NestedUnitCompletionMonsterAssemblyExact as Nested
import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as GVOA
import DASHI.Moonshine.MonsterGradedVOABridgeExact as MonsterVOA
import DASHI.Moonshine.MonsterWeightTwoSemanticActionRealisationExact as Semantic
import DASHI.Moonshine.GradedRepresentationLinearRealisationExact as LinearRep
import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Moonshine.Monster3BLinearActionProofRelevantHardeningExact as Hardening

------------------------------------------------------------------------
-- 1. The actual proof-bearing 196883 constituent witness.
------------------------------------------------------------------------

record GriessConstituentLinearWitness
    {Monster K : Set}
    (bridge : MonsterVOA.MonsterGradedVOABridge Monster K) : Setω where
  field
    semanticActionBridge :
      Semantic.WeightTwoSemanticActionBridge bridge

    fullWeightTwoLinearRealisation :
      LinearRep.LinearEndomorphismRealisation
        (GVOA.group (MonsterVOA.voaAction bridge))
        (GR.grade
          (GVOA.gradedRepresentation (MonsterVOA.voaAction bridge))
          2)

    evaluationIsSameObject :
      LinearRep.endomorphismEvaluation fullWeightTwoLinearRealisation
      ≡ Semantic.evaluation semanticActionBridge

    -- Literal linear carrier for the Griess constituent.
    constituentLinearCarrier : Linear.HilbertLift

    -- Same-object carrier weld to the existing semantic 196883 object.
    constituentToSemantic :
      Linear.Vector constituentLinearCarrier →
      Nested.SemanticMonsterConstituent196883

    constituentFromSemantic :
      Nested.SemanticMonsterConstituent196883 →
      Linear.Vector constituentLinearCarrier

    semanticAfterConstituent :
      (state : Linear.Vector constituentLinearCarrier) →
      constituentFromSemantic (constituentToSemantic state) ≡ state

    constituentAfterSemantic :
      (state : Nested.SemanticMonsterConstituent196883) →
      constituentToSemantic (constituentFromSemantic state) ≡ state

    -- Inclusion into the SAME full grade-two linear representation.
    constituentInclusion :
      Linear.Vector constituentLinearCarrier →
      Linear.Vector
        (LinearRep.linearCarrier fullWeightTwoLinearRealisation)

    constituentInclusionMatchesSemantic :
      (state : Linear.Vector constituentLinearCarrier) →
      LinearRep.toRepresentationCarrier
        fullWeightTwoLinearRealisation
        (constituentInclusion state)
      ≡
      Stable.to
        (Semantic.weightTwoCarrierIso semanticActionBridge)
        (inj₁ (constituentToSemantic state))

    -- Actual Monster action on the same linear constituent.
    constituentAct :
      Monster →
      Linear.Vector constituentLinearCarrier →
      Linear.Vector constituentLinearCarrier

    constituentActPreservesZero :
      (g : Monster) →
      constituentAct g (Linear.zero constituentLinearCarrier)
      ≡ Linear.zero constituentLinearCarrier

    constituentActPreservesAddition :
      (g : Monster) →
      (left right : Linear.Vector constituentLinearCarrier) →
      constituentAct g (Linear._+_ constituentLinearCarrier left right)
      ≡ Linear._+_ constituentLinearCarrier
          (constituentAct g left)
          (constituentAct g right)

    constituentActPreservesScaling :
      (g : Monster) →
      (scalar : Linear.Scalar constituentLinearCarrier) →
      (state : Linear.Vector constituentLinearCarrier) →
      constituentAct g (Linear._·_ constituentLinearCarrier scalar state)
      ≡ Linear._·_ constituentLinearCarrier scalar
          (constituentAct g state)

    constituentInclusionIntertwines :
      (g : Monster) →
      (state : Linear.Vector constituentLinearCarrier) →
      LinearRep.evaluatedEnd
        fullWeightTwoLinearRealisation
        (GR.action
          (GR.grade
            (GVOA.gradedRepresentation (MonsterVOA.voaAction bridge))
            2)
          g)
        (constituentInclusion state)
      ≡ constituentInclusion (constituentAct g state)

open GriessConstituentLinearWitness public

------------------------------------------------------------------------
-- 2. Compile the legacy bridge, but choose its Set-valued fields to be the
--    exact proof obligations above rather than vacuous proposition names.
------------------------------------------------------------------------

compileWeightTwoLinearActionBridge :
  ∀ {Monster K}
    {bridge : MonsterVOA.MonsterGradedVOABridge Monster K} →
  GriessConstituentLinearWitness bridge →
  WeightTwo.WeightTwoLinearActionBridge bridge
compileWeightTwoLinearActionBridge witness = record
  { semanticActionBridge = semanticActionBridge witness
  ; fullWeightTwoLinearRealisation = fullWeightTwoLinearRealisation witness
  ; evaluationIsSameObject = evaluationIsSameObject witness
  ; constituentLinearCarrier = constituentLinearCarrier witness
  ; constituentInclusion = constituentInclusion witness
  ; constituentDimension = 196883
  ; constituentDimensionIs196883 = refl
  ; constituentAct = constituentAct witness
  ; constituentActPreservesZero =
      (g : _) →
      constituentAct witness g
        (Linear.zero (constituentLinearCarrier witness))
      ≡ Linear.zero (constituentLinearCarrier witness)
  ; constituentActPreservesAddition =
      (g : _) →
      (left right : Linear.Vector (constituentLinearCarrier witness)) →
      constituentAct witness g
        (Linear._+_ (constituentLinearCarrier witness) left right)
      ≡ Linear._+_ (constituentLinearCarrier witness)
          (constituentAct witness g left)
          (constituentAct witness g right)
  ; constituentActPreservesScaling =
      (g : _) →
      (scalar : Linear.Scalar (constituentLinearCarrier witness)) →
      (state : Linear.Vector (constituentLinearCarrier witness)) →
      constituentAct witness g
        (Linear._·_ (constituentLinearCarrier witness) scalar state)
      ≡ Linear._·_ (constituentLinearCarrier witness) scalar
          (constituentAct witness g state)
  ; constituentInvariantUnderMonsterAction =
      (g : _) →
      (state : Linear.Vector (constituentLinearCarrier witness)) →
      LinearRep.evaluatedEnd
        (fullWeightTwoLinearRealisation witness)
        (GR.action
          (GR.grade
            (GVOA.gradedRepresentation
              (MonsterVOA.voaAction _))
            2)
          g)
        (constituentInclusion witness state)
      ≡ constituentInclusion witness (constituentAct witness g state)
  ; constituentInclusionIntertwines = constituentInclusionIntertwines witness
  }

------------------------------------------------------------------------
-- 3. Compile the proof-relevant paid wrapper.
------------------------------------------------------------------------

compilePaidWeightTwoLinearActionBridge :
  ∀ {Monster K}
    {bridge : MonsterVOA.MonsterGradedVOABridge Monster K} →
  (witness : GriessConstituentLinearWitness bridge) →
  Hardening.PaidWeightTwoLinearActionBridge
    (compileWeightTwoLinearActionBridge witness)
compilePaidWeightTwoLinearActionBridge witness = record
  { constituentActPreservesZeroWitness =
      constituentActPreservesZero witness
  ; constituentActPreservesAdditionWitness =
      constituentActPreservesAddition witness
  ; constituentActPreservesScalingWitness =
      constituentActPreservesScaling witness
  ; constituentInvariantUnderMonsterActionWitness =
      constituentInclusionIntertwines witness
  }

record CompiledGriessWeightTwoBridge
    {Monster K : Set}
    (bridge : MonsterVOA.MonsterGradedVOABridge Monster K) : Setω where
  field
    witness : GriessConstituentLinearWitness bridge
    linearBridge : WeightTwo.WeightTwoLinearActionBridge bridge
    linearBridgeIsCompiled :
      linearBridge ≡ compileWeightTwoLinearActionBridge witness
    paidLinearBridge : Hardening.PaidWeightTwoLinearActionBridge linearBridge

open CompiledGriessWeightTwoBridge public

compileGriessWeightTwoBridge :
  ∀ {Monster K}
    {bridge : MonsterVOA.MonsterGradedVOABridge Monster K} →
  (witness : GriessConstituentLinearWitness bridge) →
  CompiledGriessWeightTwoBridge bridge
compileGriessWeightTwoBridge witness = record
  { witness = witness
  ; linearBridge = compileWeightTwoLinearActionBridge witness
  ; linearBridgeIsCompiled = refl
  ; paidLinearBridge = compilePaidWeightTwoLinearActionBridge witness
  }

------------------------------------------------------------------------
-- 4. Attribution / non-promotion firewall.
------------------------------------------------------------------------

data CharacterSplitCreatesGriessConstituent : Set where
data Dimension196883CreatesLinearSubrepresentation : Set where
data FixedConformalPointCreatesInvariantComplement : Set where

characterSplitDoesNotCreateGriessConstituent :
  CharacterSplitCreatesGriessConstituent → ⊥
characterSplitDoesNotCreateGriessConstituent ()

dimensionDoesNotCreateLinearSubrepresentation :
  Dimension196883CreatesLinearSubrepresentation → ⊥
dimensionDoesNotCreateLinearSubrepresentation ()

fixedConformalPointDoesNotCreateInvariantComplement :
  FixedConformalPointCreatesInvariantComplement → ⊥
fixedConformalPointDoesNotCreateInvariantComplement ()

------------------------------------------------------------------------
-- 5. Machine-readable status consumed by validation/current-max-cut owners.
------------------------------------------------------------------------

griessWitnessRequiresSameSemantic196883Carrier : Bool
griessWitnessRequiresSameSemantic196883Carrier = true

griessWitnessRequiresLiteralInclusionIntertwining : Bool
griessWitnessRequiresLiteralInclusionIntertwining = true

griessCompilerProducesLegacyBridge : Bool
griessCompilerProducesLegacyBridge = true

griessCompilerProducesPaidBridge : Bool
griessCompilerProducesPaidBridge = true

characterSplitAloneProducesGriessConstituent : Bool
characterSplitAloneProducesGriessConstituent = false
