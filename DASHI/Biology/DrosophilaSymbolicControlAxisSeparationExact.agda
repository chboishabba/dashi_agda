module DASHI.Biology.DrosophilaSymbolicControlAxisSeparationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.DrosophilaSymbolicInterfaceLearningExact as Legacy

------------------------------------------------------------------------
-- Canonical control-axis separation.
--
-- The first symbolic-interface owner grouped topology nulls and intervention
-- controls under one legacy NullModelKind.  Downstream experiments must use
-- these orthogonal axes instead.
------------------------------------------------------------------------

data SymbolicTopologyKind : Set where
  maleCNSTopology : SymbolicTopologyKind
  degreePreservingRewiredTopology : SymbolicTopologyKind
  shuffledNeuronIdentityTopology : SymbolicTopologyKind
  matchedGenericRecurrentTopology : SymbolicTopologyKind

data SymbolicInterventionKind : Set where
  baselineIntervention : SymbolicInterventionKind
  noLearningIntervention : SymbolicInterventionKind
  alternateInitializationIntervention : SymbolicInterventionKind

record SymbolicControlArm : Set where
  constructor symbolicControlArm
  field
    topology : SymbolicTopologyKind
    intervention : SymbolicInterventionKind

open SymbolicControlArm public

canonicalMaleCNSArm : SymbolicControlArm
canonicalMaleCNSArm = symbolicControlArm maleCNSTopology baselineIntervention

rewiredTopologyArm : SymbolicControlArm
rewiredTopologyArm =
  symbolicControlArm degreePreservingRewiredTopology baselineIntervention

noLearningArm : SymbolicControlArm
noLearningArm = symbolicControlArm maleCNSTopology noLearningIntervention

alternateInitializationArm : SymbolicControlArm
alternateInitializationArm =
  symbolicControlArm maleCNSTopology alternateInitializationIntervention

data NoLearningIsTopologyPermission : Set where

data AlternateInitializationIsTopologyPermission : Set where

data TopologyInterventionAxisCollapsePermission : Set where

noLearningIsNotTopology : NoLearningIsTopologyPermission → ⊥
noLearningIsNotTopology ()

alternateInitializationIsNotTopology :
  AlternateInitializationIsTopologyPermission → ⊥
alternateInitializationIsNotTopology ()

topologyAndInterventionAreDistinctAxes :
  TopologyInterventionAxisCollapsePermission → ⊥
topologyAndInterventionAreDistinctAxes ()

record ControlAxisBoundary : Set where
  constructor controlAxisBoundary
  field
    noLearningPromotedAsTopology : Bool
    alternateInitializationPromotedAsTopology : Bool
    topologyAndInterventionCollapsed : Bool
    legacyMixedCarrierCanonicalForNewRuns : Bool

open ControlAxisBoundary public

canonicalControlAxisBoundary : ControlAxisBoundary
canonicalControlAxisBoundary = controlAxisBoundary false false false false

legacyMixedCarrierNotCanonicalForNewRuns :
  legacyMixedCarrierCanonicalForNewRuns canonicalControlAxisBoundary ≡ false
legacyMixedCarrierNotCanonicalForNewRuns = refl

------------------------------------------------------------------------
-- Legacy owner remains imported for provenance/backward compatibility only.
------------------------------------------------------------------------

legacyNullObligationRetained : Legacy.NullComparisonObligation
legacyNullObligationRetained = Legacy.canonicalNullComparisonObligation
