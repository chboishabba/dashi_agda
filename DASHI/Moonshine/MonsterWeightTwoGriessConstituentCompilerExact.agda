module DASHI.Moonshine.MonsterWeightTwoGriessConstituentCompilerExact where

------------------------------------------------------------------------
-- PROOF-BEARING GRIESS CONSTITUENT COMPILER
--
-- The Suzuki / 3B character arithmetic
--
--   65610 = 90 * 729 = (12 + 78) * 729
--
-- lives downstream of the literal weight-two Monster representation.  It does
-- not create the 196883-dimensional Griess constituent.
--
-- IMPORTANT WRONG-TYPE CORRECTION
-- --------------------------------
-- `Nested.SemanticMonsterConstituent196883` is a finite BASIS-LABEL carrier.
-- It is not the set of vectors of a 196883-dimensional complex vector space.
-- Therefore this owner does NOT demand or manufacture a bijection between that
-- finite set and the vector carrier of the Griess representation.
--
-- The correct proof-bearing object is instead:
--
--   * an actual finite-dimensional Monster representation C with declared
--     representation dimension 196883;
--   * a proof-bearing linear realisation of C;
--   * an injective Monster-equivariant linear inclusion of C into the SAME
--     full grade-two representation used by the literal VOA/trace authority.
--
-- From exactly those data this owner compiles the historical
-- `WeightTwoLinearActionBridge` and its proof-relevant paid wrapper.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as GVOA
import DASHI.Moonshine.MonsterGradedVOABridgeExact as MonsterVOA
import DASHI.Moonshine.MonsterWeightTwoSemanticActionRealisationExact as Semantic
import DASHI.Moonshine.GradedRepresentationLinearRealisationExact as LinearRep
import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Moonshine.Monster3BLinearActionProofRelevantHardeningExact as Hardening

------------------------------------------------------------------------
-- 1. Actual representation-level Griess constituent witness.
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

    -- Independent actual Monster representation object for the Griess piece.
    constituentRepresentation :
      GR.FiniteDimensionalRepresentation
        Monster K
        (GVOA.group (MonsterVOA.voaAction bridge))

    constituentDimensionIs196883 :
      GR.dimension constituentRepresentation ≡ 196883

    constituentLinearRealisation :
      LinearRep.LinearEndomorphismRealisation
        (GVOA.group (MonsterVOA.voaAction bridge))
        constituentRepresentation

    -- Inclusion into the SAME full grade-two linear representation.
    constituentInclusion :
      Linear.Vector
        (LinearRep.linearCarrier constituentLinearRealisation) →
      Linear.Vector
        (LinearRep.linearCarrier fullWeightTwoLinearRealisation)

    constituentInclusionInjective :
      ∀ {left right} →
      constituentInclusion left ≡ constituentInclusion right →
      left ≡ right

    constituentInclusionIntertwines :
      (g : Monster) →
      (state :
        Linear.Vector
          (LinearRep.linearCarrier constituentLinearRealisation)) →
      LinearRep.evaluatedEnd
        fullWeightTwoLinearRealisation
        (GR.action
          (GR.grade
            (GVOA.gradedRepresentation (MonsterVOA.voaAction bridge))
            2)
          g)
        (constituentInclusion state)
      ≡
      constituentInclusion
        (LinearRep.evaluatedEnd
          constituentLinearRealisation
          (GR.action constituentRepresentation g)
          state)

open GriessConstituentLinearWitness public

------------------------------------------------------------------------
-- 2. Actual constituent action and its linearity are compiler outputs of the
--    proof-bearing constituent representation.
------------------------------------------------------------------------

griessConstituentAct :
  ∀ {Monster K bridge}
    (witness : GriessConstituentLinearWitness {Monster} {K} bridge) →
  Monster →
  Linear.Vector
    (LinearRep.linearCarrier (constituentLinearRealisation witness)) →
  Linear.Vector
    (LinearRep.linearCarrier (constituentLinearRealisation witness))
griessConstituentAct witness g =
  LinearRep.evaluatedEnd
    (constituentLinearRealisation witness)
    (GR.action (constituentRepresentation witness) g)

griessActPreservesZero :
  ∀ {Monster K bridge}
    (witness : GriessConstituentLinearWitness {Monster} {K} bridge) →
  (g : Monster) →
  griessConstituentAct witness g
    (Linear.zero
      (LinearRep.linearCarrier (constituentLinearRealisation witness)))
  ≡
  Linear.zero
    (LinearRep.linearCarrier (constituentLinearRealisation witness))
griessActPreservesZero witness g =
  LinearRep.evaluatedEndPreservesZero
    (constituentLinearRealisation witness)
    (GR.action (constituentRepresentation witness) g)

griessActPreservesAddition :
  ∀ {Monster K bridge}
    (witness : GriessConstituentLinearWitness {Monster} {K} bridge) →
  (g : Monster) →
  (left right :
    Linear.Vector
      (LinearRep.linearCarrier (constituentLinearRealisation witness))) →
  griessConstituentAct witness g
    (Linear._+_
      (LinearRep.linearCarrier (constituentLinearRealisation witness))
      left right)
  ≡
  Linear._+_
    (LinearRep.linearCarrier (constituentLinearRealisation witness))
    (griessConstituentAct witness g left)
    (griessConstituentAct witness g right)
griessActPreservesAddition witness g left right =
  LinearRep.evaluatedEndPreservesAddition
    (constituentLinearRealisation witness)
    (GR.action (constituentRepresentation witness) g)
    left right

griessActPreservesScaling :
  ∀ {Monster K bridge}
    (witness : GriessConstituentLinearWitness {Monster} {K} bridge) →
  (g : Monster) →
  (scalar :
    Linear.Scalar
      (LinearRep.linearCarrier (constituentLinearRealisation witness))) →
  (state :
    Linear.Vector
      (LinearRep.linearCarrier (constituentLinearRealisation witness))) →
  griessConstituentAct witness g
    (Linear._·_
      (LinearRep.linearCarrier (constituentLinearRealisation witness))
      scalar state)
  ≡
  Linear._·_
    (LinearRep.linearCarrier (constituentLinearRealisation witness))
    scalar
    (griessConstituentAct witness g state)
griessActPreservesScaling witness g scalar state =
  LinearRep.evaluatedEndPreservesScaling
    (constituentLinearRealisation witness)
    (GR.action (constituentRepresentation witness) g)
    scalar state

------------------------------------------------------------------------
-- 3. Compile the historical bridge with exact proof obligations.
------------------------------------------------------------------------

compileWeightTwoLinearActionBridge :
  ∀ {Monster K}
    {bridge : MonsterVOA.MonsterGradedVOABridge Monster K} →
  GriessConstituentLinearWitness bridge →
  WeightTwo.WeightTwoLinearActionBridge bridge
compileWeightTwoLinearActionBridge {bridge = bridge} witness = record
  { semanticActionBridge = semanticActionBridge witness
  ; fullWeightTwoLinearRealisation = fullWeightTwoLinearRealisation witness
  ; evaluationIsSameObject = evaluationIsSameObject witness
  ; constituentLinearCarrier =
      LinearRep.linearCarrier (constituentLinearRealisation witness)
  ; constituentInclusion = constituentInclusion witness
  ; constituentDimension = GR.dimension (constituentRepresentation witness)
  ; constituentDimensionIs196883 = constituentDimensionIs196883 witness
  ; constituentAct = griessConstituentAct witness
  ; constituentActPreservesZero =
      (g : Monster) →
      griessConstituentAct witness g
        (Linear.zero
          (LinearRep.linearCarrier
            (constituentLinearRealisation witness)))
      ≡
      Linear.zero
        (LinearRep.linearCarrier (constituentLinearRealisation witness))
  ; constituentActPreservesAddition =
      (g : Monster) →
      (left right :
        Linear.Vector
          (LinearRep.linearCarrier
            (constituentLinearRealisation witness))) →
      griessConstituentAct witness g
        (Linear._+_
          (LinearRep.linearCarrier
            (constituentLinearRealisation witness))
          left right)
      ≡
      Linear._+_
        (LinearRep.linearCarrier (constituentLinearRealisation witness))
        (griessConstituentAct witness g left)
        (griessConstituentAct witness g right)
  ; constituentActPreservesScaling =
      (g : Monster) →
      (scalar :
        Linear.Scalar
          (LinearRep.linearCarrier
            (constituentLinearRealisation witness))) →
      (state :
        Linear.Vector
          (LinearRep.linearCarrier
            (constituentLinearRealisation witness))) →
      griessConstituentAct witness g
        (Linear._·_
          (LinearRep.linearCarrier
            (constituentLinearRealisation witness))
          scalar state)
      ≡
      Linear._·_
        (LinearRep.linearCarrier (constituentLinearRealisation witness))
        scalar
        (griessConstituentAct witness g state)
  ; constituentInvariantUnderMonsterAction =
      (g : Monster) →
      (state :
        Linear.Vector
          (LinearRep.linearCarrier
            (constituentLinearRealisation witness))) →
      LinearRep.evaluatedEnd
        (fullWeightTwoLinearRealisation witness)
        (GR.action
          (GR.grade
            (GVOA.gradedRepresentation
              (MonsterVOA.voaAction bridge))
            2)
          g)
        (constituentInclusion witness state)
      ≡ constituentInclusion witness (griessConstituentAct witness g state)
  ; constituentInclusionIntertwines = constituentInclusionIntertwines witness
  }

compilePaidWeightTwoLinearActionBridge :
  ∀ {Monster K}
    {bridge : MonsterVOA.MonsterGradedVOABridge Monster K} →
  (witness : GriessConstituentLinearWitness bridge) →
  Hardening.PaidWeightTwoLinearActionBridge
    (compileWeightTwoLinearActionBridge witness)
compilePaidWeightTwoLinearActionBridge witness = record
  { constituentActPreservesZeroWitness =
      griessActPreservesZero witness
  ; constituentActPreservesAdditionWitness =
      griessActPreservesAddition witness
  ; constituentActPreservesScalingWitness =
      griessActPreservesScaling witness
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
-- 4. Attribution / non-promotion firewalls.
------------------------------------------------------------------------

data CharacterSplitCreatesGriessConstituent : Set where
data Dimension196883CreatesLinearSubrepresentation : Set where
data FixedConformalPointCreatesInvariantComplement : Set where
data SemanticBasisLabelsCreateVectorCarrier : Set where

characterSplitDoesNotCreateGriessConstituent :
  CharacterSplitCreatesGriessConstituent → ⊥
characterSplitDoesNotCreateGriessConstituent ()

dimensionDoesNotCreateLinearSubrepresentation :
  Dimension196883CreatesLinearSubrepresentation → ⊥
dimensionDoesNotCreateLinearSubrepresentation ()

fixedConformalPointDoesNotCreateInvariantComplement :
  FixedConformalPointCreatesInvariantComplement → ⊥
fixedConformalPointDoesNotCreateInvariantComplement ()

semanticBasisLabelsDoNotCreateVectorCarrier :
  SemanticBasisLabelsCreateVectorCarrier → ⊥
semanticBasisLabelsDoNotCreateVectorCarrier ()

------------------------------------------------------------------------
-- 5. Machine-readable status consumed by validation/current-max-cut owners.
------------------------------------------------------------------------

griessWitnessRequiresActual196883Representation : Bool
griessWitnessRequiresActual196883Representation = true

griessWitnessRequiresInjectiveEquivariantInclusion : Bool
griessWitnessRequiresInjectiveEquivariantInclusion = true

griessCompilerProducesLegacyBridge : Bool
griessCompilerProducesLegacyBridge = true

griessCompilerProducesPaidBridge : Bool
griessCompilerProducesPaidBridge = true

semanticBasisLabelsAloneProduceGriessVectorCarrier : Bool
semanticBasisLabelsAloneProduceGriessVectorCarrier = false

characterSplitAloneProducesGriessConstituent : Bool
characterSplitAloneProducesGriessConstituent = false
