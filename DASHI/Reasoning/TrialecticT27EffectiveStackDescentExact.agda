module DASHI.Reasoning.TrialecticT27EffectiveStackDescentExact where

------------------------------------------------------------------------
-- EFFECTIVE OBJECT + MORPHISM DESCENT ON THE COMPLETED T^27 GLOBAL GRAPH
--
-- Local data remain the mature T^9 edge dialectics with T^3 overlaps.  For an
-- explicit completion policy P : T^18 -> T^9, compatible locals first glue to
-- the old T^18 boundary and then embed into CompletedT27 P.  The graph global
-- is therefore an exact carrier replacement, not 9 new independent degrees of
-- freedom.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369TriTruthField as Tri
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Foundations.RelationalStageTwelveSiteExact as RelSheaf
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticGrothendieckThreeCellDescentExact as OldDescent
import DASHI.Reasoning.TrialecticSetEffectiveDescentExact as OldSet
import DASHI.Reasoning.TrialecticWavePhaseGroupoidPresheafExact as OldPhase
import DASHI.Reasoning.TrialecticWavePhaseEffectiveStackDescentExact as OldStack
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27GraphGrothendieckSheafExact as GraphSheaf
import DASHI.Reasoning.TrialecticT27WavePhaseGroupoidPresheafExact as GraphPhase

------------------------------------------------------------------------
-- 1. Effective object descent.
------------------------------------------------------------------------

record GraphGlobalRealization
    (policy : Tower.T27CompletionPolicy)
    (locals : RelSheaf.TriadicLocals Cell.CellDialectic) : Set where
  constructor graph-global-realization
  field
    globalGraph : Tower.CompletedT27 policy
    realizesAB :
      GraphSheaf.restrictCompletedAB policy globalGraph
      ≡ RelSheaf.localAB locals
    realizesBC :
      GraphSheaf.restrictCompletedBC policy globalGraph
      ≡ RelSheaf.localBC locals
    realizesCA :
      GraphSheaf.restrictCompletedCA policy globalGraph
      ≡ RelSheaf.localCA locals

open GraphGlobalRealization public

realizeCompatibleLocals :
  (policy : Tower.T27CompletionPolicy) →
  (locals : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (compatibility :
    RelSheaf.CompatibleOnTriadicCover OldDescent.cellOverlapSystem locals) →
  GraphGlobalRealization policy locals
realizeCompatibleLocals policy locals compatibility =
  graph-global-realization
    (GraphSheaf.glueCompletedT27 policy locals compatibility)
    (GraphSheaf.glueCompletedRestrictsAB policy locals compatibility)
    (GraphSheaf.glueCompletedRestrictsBC policy locals compatibility)
    (GraphSheaf.glueCompletedRestrictsCA policy locals compatibility)

record GraphBoundaryObservationalEquivalence
    (policy : Tower.T27CompletionPolicy)
    (left right : Tower.CompletedT27 policy) : Set where
  constructor graph-boundary-observational-equivalence
  field
    sameAB :
      GraphSheaf.restrictCompletedAB policy left
      ≡ GraphSheaf.restrictCompletedAB policy right
    sameBC :
      GraphSheaf.restrictCompletedBC policy left
      ≡ GraphSheaf.restrictCompletedBC policy right
    sameCA :
      GraphSheaf.restrictCompletedCA policy left
      ≡ GraphSheaf.restrictCompletedCA policy right

open GraphBoundaryObservationalEquivalence public

graphRealizationsObservationallyUnique :
  (policy : Tower.T27CompletionPolicy) →
  ∀ {locals : RelSheaf.TriadicLocals Cell.CellDialectic} →
  (left right : GraphGlobalRealization policy locals) →
  GraphBoundaryObservationalEquivalence policy
    (globalGraph left)
    (globalGraph right)
graphRealizationsObservationallyUnique policy left right =
  graph-boundary-observational-equivalence
    (trans (realizesAB left) (sym (realizesAB right)))
    (trans (realizesBC left) (sym (realizesBC right)))
    (trans (realizesCA left) (sym (realizesCA right)))

------------------------------------------------------------------------
-- 2. Effective morphism descent.  The compatible local morphism carrier is
-- unchanged; only its global endpoints are now completed T^27 graph sections.
------------------------------------------------------------------------

glueGraphPhaseMorphisms :
  (policy : Tower.T27CompletionPolicy) →
  (source target : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (sourceCompatibility :
    RelSheaf.CompatibleOnTriadicCover OldDescent.cellOverlapSystem source) →
  (targetCompatibility :
    RelSheaf.CompatibleOnTriadicCover OldDescent.cellOverlapSystem target) →
  OldStack.TriadicPhaseMorphisms source target →
  GraphPhase.GraphFibreHom policy
    (GraphSheaf.glueCompletedT27 policy source sourceCompatibility)
    (GraphSheaf.glueCompletedT27 policy target targetCompatibility)
glueGraphPhaseMorphisms policy source target sourceCompatibility targetCompatibility morphisms =
  OldPhase.global-phase-hom
    (OldSet.boundary-observational-equivalence sameAB' sameBC' sameCA')
    (OldPhase.equalityPhase (OldStack.morphismAB morphisms))
  where
    sameAB' :
      OldDescent.restrictStructuredAB
        (GraphSheaf.completedT27ToBoundary policy
          (GraphSheaf.glueCompletedT27 policy source sourceCompatibility))
      ≡
      OldDescent.restrictStructuredAB
        (GraphSheaf.completedT27ToBoundary policy
          (GraphSheaf.glueCompletedT27 policy target targetCompatibility))
    sameAB' =
      trans
        (GraphSheaf.glueCompletedRestrictsAB policy source sourceCompatibility)
        (trans
          (OldPhase.underlyingEquality (OldStack.morphismAB morphisms))
          (sym (GraphSheaf.glueCompletedRestrictsAB policy target targetCompatibility)))

    sameBC' :
      OldDescent.restrictStructuredBC
        (GraphSheaf.completedT27ToBoundary policy
          (GraphSheaf.glueCompletedT27 policy source sourceCompatibility))
      ≡
      OldDescent.restrictStructuredBC
        (GraphSheaf.completedT27ToBoundary policy
          (GraphSheaf.glueCompletedT27 policy target targetCompatibility))
    sameBC' =
      trans
        (GraphSheaf.glueCompletedRestrictsBC policy source sourceCompatibility)
        (trans
          (OldPhase.underlyingEquality (OldStack.morphismBC morphisms))
          (sym (GraphSheaf.glueCompletedRestrictsBC policy target targetCompatibility)))

    sameCA' :
      OldDescent.restrictStructuredCA
        (GraphSheaf.completedT27ToBoundary policy
          (GraphSheaf.glueCompletedT27 policy source sourceCompatibility))
      ≡
      OldDescent.restrictStructuredCA
        (GraphSheaf.completedT27ToBoundary policy
          (GraphSheaf.glueCompletedT27 policy target targetCompatibility))
    sameCA' =
      trans
        (GraphSheaf.glueCompletedRestrictsCA policy source sourceCompatibility)
        (trans
          (OldPhase.underlyingEquality (OldStack.morphismCA morphisms))
          (sym (GraphSheaf.glueCompletedRestrictsCA policy target targetCompatibility)))

recoverGraphAB :
  (policy : Tower.T27CompletionPolicy) →
  (source target : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (sourceCompatibility :
    RelSheaf.CompatibleOnTriadicCover OldDescent.cellOverlapSystem source) →
  (targetCompatibility :
    RelSheaf.CompatibleOnTriadicCover OldDescent.cellOverlapSystem target) →
  (morphisms : OldStack.TriadicPhaseMorphisms source target) →
  GraphPhase.graphHomEquivalent policy
    (GraphPhase.graphRestrictHom policy Site.abToGlobal
      (glueGraphPhaseMorphisms policy source target sourceCompatibility targetCompatibility morphisms))
    (OldStack.morphismAB morphisms)
recoverGraphAB policy source target sourceCompatibility targetCompatibility morphisms = refl

recoverGraphBC :
  (policy : Tower.T27CompletionPolicy) →
  (source target : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (sourceCompatibility :
    RelSheaf.CompatibleOnTriadicCover OldDescent.cellOverlapSystem source) →
  (targetCompatibility :
    RelSheaf.CompatibleOnTriadicCover OldDescent.cellOverlapSystem target) →
  (morphisms : OldStack.TriadicPhaseMorphisms source target) →
  GraphPhase.graphHomEquivalent policy
    (GraphPhase.graphRestrictHom policy Site.bcToGlobal
      (glueGraphPhaseMorphisms policy source target sourceCompatibility targetCompatibility morphisms))
    (OldStack.morphismBC morphisms)
recoverGraphBC policy source target sourceCompatibility targetCompatibility morphisms =
  OldStack.phaseABequalsBC morphisms

recoverGraphCA :
  (policy : Tower.T27CompletionPolicy) →
  (source target : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (sourceCompatibility :
    RelSheaf.CompatibleOnTriadicCover OldDescent.cellOverlapSystem source) →
  (targetCompatibility :
    RelSheaf.CompatibleOnTriadicCover OldDescent.cellOverlapSystem target) →
  (morphisms : OldStack.TriadicPhaseMorphisms source target) →
  GraphPhase.graphHomEquivalent policy
    (GraphPhase.graphRestrictHom policy Site.caToGlobal
      (glueGraphPhaseMorphisms policy source target sourceCompatibility targetCompatibility morphisms))
    (OldStack.morphismCA morphisms)
recoverGraphCA policy source target sourceCompatibility targetCompatibility morphisms =
  OldStack.phaseABequalsCA morphisms

------------------------------------------------------------------------
-- 3. Uniqueness up to the transported typed phase-groupoid isomorphism.
------------------------------------------------------------------------

record GraphGlobalPhaseIso
    (policy : Tower.T27CompletionPolicy)
    (left right : Tower.CompletedT27 policy) : Set where
  constructor graph-global-phase-iso
  field
    forward : GraphPhase.GraphFibreHom policy left right
    backward : GraphPhase.GraphFibreHom policy right left
    backwardAfterForward :
      GraphPhase.graphHomEquivalent policy
        (GraphPhase.graphComposeHom policy backward forward)
        (GraphPhase.graphIdentityHom policy left)
    forwardAfterBackward :
      GraphPhase.graphHomEquivalent policy
        (GraphPhase.graphComposeHom policy forward backward)
        (GraphPhase.graphIdentityHom policy right)

open GraphGlobalPhaseIso public

graphRealizationsUniqueUpToTypedIso :
  (policy : Tower.T27CompletionPolicy) →
  ∀ {locals : RelSheaf.TriadicLocals Cell.CellDialectic} →
  (left right : GraphGlobalRealization policy locals) →
  GraphGlobalPhaseIso policy (globalGraph left) (globalGraph right)
graphRealizationsUniqueUpToTypedIso policy left right =
  graph-global-phase-iso
    forwardHom
    (GraphPhase.graphInverseHom policy forwardHom)
    (GraphPhase.graphInverseAfterForward policy forwardHom)
    (GraphPhase.graphForwardAfterInverse policy forwardHom)
  where
    obs : GraphBoundaryObservationalEquivalence policy
      (globalGraph left) (globalGraph right)
    obs = graphRealizationsObservationallyUnique policy left right

    forwardHom : GraphPhase.GraphFibreHom policy
      (globalGraph left) (globalGraph right)
    forwardHom =
      OldPhase.global-phase-hom
        (OldSet.boundary-observational-equivalence
          (sameAB obs)
          (sameBC obs)
          (sameCA obs))
        Tri.triZero

------------------------------------------------------------------------
-- 4. Boundary.
------------------------------------------------------------------------

record TrialecticT27EffectiveStackBoundary : Set where
  constructor trialectic-t27-effective-stack-boundary
  field
    completedT27ObjectDescentPaid : Bool
    completedT27MorphismDescentPaid : Bool
    allThreeLocalMorphismsRecovered : Bool
    completedT27RealizationsUniqueUpToTypedIso : Bool
    localT9T3DescentDataUnchanged : Bool
    completionPolicyRequiredExplicitly : Bool
    unconstrainedAmbientT27EffectiveStackClaimed : Bool

open TrialecticT27EffectiveStackBoundary public

canonicalTrialecticT27EffectiveStackBoundary :
  TrialecticT27EffectiveStackBoundary
canonicalTrialecticT27EffectiveStackBoundary =
  trialectic-t27-effective-stack-boundary
    true true true true true true false
