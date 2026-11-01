module DASHI.Biology.FiniteCoalitionConstruction where

open import DASHI.Core.Prelude

import DASHI.Biology.QuantitativeCompositionalDefect as Defect
import DASHI.Biology.DynamicEffectiveTopology as Topology

------------------------------------------------------------------------
-- Finite coalition construction.
--
-- A candidate is scored by a finite objective combining compositional defect,
-- recruitment cost, lack of reach, and lack of persistence.  The canonical
-- selected coalition is proved minimal over the complete finite candidate
-- family and recurrent under the supplied update law.
--
-- Source-facing references:
-- J. A. Scott Kelso, "Multistability and metastability: understanding
-- dynamic coordination in the brain", DOI 10.1098/rstb.2011.0351.
-- R. Matthew Hutchison et al., "Dynamic functional connectivity: Promise,
-- issues, and interpretations", DOI 10.1016/j.neuroimage.2013.05.079.

data CoalitionCandidate : Set where
  localCandidate : CoalitionCandidate
  unstableWideCandidate : CoalitionCandidate
  coherentRecurrentCandidate : CoalitionCandidate

candidateDefect : CoalitionCandidate → Nat
candidateDefect localCandidate = 1
candidateDefect unstableWideCandidate = 3
candidateDefect coherentRecurrentCandidate = 1

candidateCost : CoalitionCandidate → Nat
candidateCost localCandidate = 1
candidateCost unstableWideCandidate = 3
candidateCost coherentRecurrentCandidate = 2

reachPenalty : CoalitionCandidate → Nat
reachPenalty localCandidate = 3
reachPenalty unstableWideCandidate = 0
reachPenalty coherentRecurrentCandidate = 0

persistencePenalty : CoalitionCandidate → Nat
persistencePenalty localCandidate = 2
persistencePenalty unstableWideCandidate = 2
persistencePenalty coherentRecurrentCandidate = 0

objective : CoalitionCandidate → Nat
objective c =
  candidateDefect c
  + candidateCost c
  + reachPenalty c
  + persistencePenalty c

localObjectiveIsSeven : objective localCandidate ≡ 7
localObjectiveIsSeven = refl

unstableWideObjectiveIsEight : objective unstableWideCandidate ≡ 8
unstableWideObjectiveIsEight = refl

coherentRecurrentObjectiveIsThree :
  objective coherentRecurrentCandidate ≡ 3
coherentRecurrentObjectiveIsThree = refl

selectedCoalition : CoalitionCandidate
selectedCoalition = coherentRecurrentCandidate

selectedCoalitionMinimal :
  (c : CoalitionCandidate) →
  objective selectedCoalition ≤ objective c
selectedCoalitionMinimal localCandidate = s≤s (s≤s (s≤s z≤n))
selectedCoalitionMinimal unstableWideCandidate = s≤s (s≤s (s≤s z≤n))
selectedCoalitionMinimal coherentRecurrentCandidate = ≤-refl

------------------------------------------------------------------------
-- Competition and recurrent viability.

incompatible : CoalitionCandidate → CoalitionCandidate → Bool
incompatible localCandidate unstableWideCandidate = true
incompatible unstableWideCandidate localCandidate = true
incompatible unstableWideCandidate coherentRecurrentCandidate = true
incompatible coherentRecurrentCandidate unstableWideCandidate = true
incompatible _ _ = false

wideAndRecurrentCompete :
  incompatible unstableWideCandidate coherentRecurrentCandidate ≡ true
wideAndRecurrentCompete = refl

coalitionUpdate : CoalitionCandidate → CoalitionCandidate
coalitionUpdate localCandidate = coherentRecurrentCandidate
coalitionUpdate unstableWideCandidate = localCandidate
coalitionUpdate coherentRecurrentCandidate = coherentRecurrentCandidate

selectedCoalitionIsFixedPoint :
  coalitionUpdate selectedCoalition ≡ selectedCoalition
selectedCoalitionIsFixedPoint = refl

localCandidateRecruitsToSelected :
  coalitionUpdate localCandidate ≡ selectedCoalition
localCandidateRecruitsToSelected = refl

record ConstructedCoalitionWitness : Set₁ where
  constructor constructedCoalitionWitness
  field
    candidate : CoalitionCandidate
    minimal : (c : CoalitionCandidate) → objective candidate ≤ objective c
    recurrent : coalitionUpdate candidate ≡ candidate
    recurrentTopologyReach :
      Topology.Reachable Topology.recurrentState
        Topology.sensoryNode Topology.planningNode

open ConstructedCoalitionWitness public

canonicalConstructedCoalitionWitness : ConstructedCoalitionWitness
canonicalConstructedCoalitionWitness =
  constructedCoalitionWitness
    selectedCoalition
    selectedCoalitionMinimal
    selectedCoalitionIsFixedPoint
    Topology.recurrentSensoryPlanningReach

------------------------------------------------------------------------
-- The objective is model-relative, not a consciousness oracle.

record CoalitionConstructionBoundary : Set where
  constructor coalitionConstructionBoundary
  field
    finiteMinimumIsPhenomenalConsciousness : Bool
    finiteMinimumIsPhenomenalConsciousnessIsFalse :
      finiteMinimumIsPhenomenalConsciousness ≡ false

    objectiveWeightsAreEmpiricallyIdentified : Bool
    objectiveWeightsAreEmpiricallyIdentifiedIsFalse :
      objectiveWeightsAreEmpiricallyIdentified ≡ false

canonicalCoalitionConstructionBoundary : CoalitionConstructionBoundary
canonicalCoalitionConstructionBoundary =
  coalitionConstructionBoundary false refl false refl
