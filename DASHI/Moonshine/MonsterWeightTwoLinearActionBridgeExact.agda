module DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CALIBRATION
--
-- I. Frenkel, J. Lepowsky, A. Meurman,
-- Vertex Operator Algebras and the Monster, Academic Press, 1988.
-- No DOI asserted here; ISBN/custody remains with the existing VOA owners.
--
-- J.-P. Serre, Linear Representations of Finite Groups.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- `MonsterWeightTwoSemanticActionRealisationExact` already fixes the exact
-- grade-2 representation, evaluates its abstract endomorphisms, identifies the
-- semantic weight-two carrier, and keeps preservation of the 196883 constituent
-- as a separate payment.
--
-- `GradedRepresentationLinearRealisationExact` separately upgrades an abstract
-- graded representation + endomorphism evaluation to a genuine linear carrier.
--
-- This owner welds those two EXISTING surfaces on the SAME grade-2
-- representation.  It then requires a linear invariant 196883 constituent
-- inside that full linear weight-two carrier.  The semantic finite/set carrier
-- is not used as a vector space and cardinality does not create the inclusion.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as GVOA
import DASHI.Moonshine.MonsterGradedVOABridgeExact as MonsterVOA
import DASHI.Moonshine.MonsterWeightTwoSemanticActionRealisationExact as Semantic
import DASHI.Moonshine.GradedRepresentationLinearRealisationExact as LinearRep

------------------------------------------------------------------------
-- Same-object grade-2 linear bridge.
------------------------------------------------------------------------

record WeightTwoLinearActionBridge
    {Monster K : Set}
    (bridge : MonsterVOA.MonsterGradedVOABridge Monster K) : Setω where
  field
    semanticActionBridge : Semantic.WeightTwoSemanticActionBridge bridge

    fullWeightTwoLinearRealisation :
      LinearRep.LinearEndomorphismRealisation
        (GVOA.group (MonsterVOA.voaAction bridge))
        (GR.grade
          (GVOA.gradedRepresentation (MonsterVOA.voaAction bridge))
          2)

    evaluationIsSameObject :
      LinearRep.endomorphismEvaluation fullWeightTwoLinearRealisation
      ≡ Semantic.evaluation semanticActionBridge

    -- Actual linear Monster constituent, distinct from the semantic finite/set
    -- carrier but embedded into the SAME full grade-2 linear representation.
    constituentLinearCarrier : Linear.HilbertLift

    constituentInclusion :
      Linear.Vector constituentLinearCarrier →
      Linear.Vector
        (LinearRep.linearCarrier fullWeightTwoLinearRealisation)

    constituentDimension : Nat
    constituentDimensionIs196883 : constituentDimension ≡ 196883

    constituentAct :
      Monster →
      Linear.Vector constituentLinearCarrier →
      Linear.Vector constituentLinearCarrier

    constituentActPreservesZero : Set
    constituentActPreservesAddition : Set
    constituentActPreservesScaling : Set
    constituentInvariantUnderMonsterAction : Set

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

open WeightTwoLinearActionBridge public

------------------------------------------------------------------------
-- WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data SemanticConstituentSetCreatesLinearSubspace : Set where
data Dimension196883CreatesLinearSubspace : Set where
data FixedConformalPointCreatesLinearComplement : Set where
data TraceCreatesLinearInclusion : Set where

semanticConstituentSetDoesNotCreateLinearSubspace :
  SemanticConstituentSetCreatesLinearSubspace → ⊥
semanticConstituentSetDoesNotCreateLinearSubspace ()

dimensionDoesNotCreateLinearSubspace : Dimension196883CreatesLinearSubspace → ⊥
dimensionDoesNotCreateLinearSubspace ()

fixedConformalPointDoesNotCreateLinearComplement :
  FixedConformalPointCreatesLinearComplement → ⊥
fixedConformalPointDoesNotCreateLinearComplement ()

traceDoesNotCreateLinearInclusion : TraceCreatesLinearInclusion → ⊥
traceDoesNotCreateLinearInclusion ()

------------------------------------------------------------------------
-- Source / classification coordinates.
------------------------------------------------------------------------

serreDOI : String
serreDOI = "10.1007/978-1-4684-9458-7"

groupRepresentationQID : String
groupRepresentationQID = "Q1055807"

groupRepresentationDewey : String
groupRepresentationDewey = "512.22"

oeisRole : String
oeisRole = "not applicable: linear constituent inclusion/intertwining is representation structure, not integer-sequence evidence"

------------------------------------------------------------------------
-- Frontier.
------------------------------------------------------------------------

record WeightTwoLinearActionBoundary : Set where
  constructor weight-two-linear-action-boundary
  field
    semanticWeightTwoActionSurfaceAlreadyOwned : Bool
    genericLinearRealisationCompilerAlreadyOwned : Bool
    sameGradeTwoRepresentationRequired : Bool
    linear196883ConstituentRequired : Bool
    constituentIntertwiningRequired : Bool
    actualWeightTwoLinearBridgeInhabitedHere : Bool
open WeightTwoLinearActionBoundary public

canonicalWeightTwoLinearActionBoundary : WeightTwoLinearActionBoundary
canonicalWeightTwoLinearActionBoundary = weight-two-linear-action-boundary
  true true true true true false
