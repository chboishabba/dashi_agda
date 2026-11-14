module DASHI.Reasoning.TrialecticT27WavePhaseGroupoidPresheafExact where

------------------------------------------------------------------------
-- WAVE-PHASE GROUPOID PRESHEAF TRANSPORTED TO COMPLETED T^27 GLOBAL OBJECTS
--
-- The old groupoid presheaf is already fully non-discrete on all seven site
-- fibres.  TrialecticT27GraphSitePresheafExact changes only the global object,
-- by an exact equivalence T^18 <-> CompletedT27(policy).  The local T^9/T^3
-- carriers and all restriction payloads are unchanged.
--
-- Therefore the wave-phase homs, groupoid laws and restriction functors are
-- transported through the object equivalence rather than rebuilt.  This is a
-- same-information graph lift: unconstrained ambient T^27 is still not an
-- object of the promoted presheaf.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Base369 using (TriTruth)

import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27GraphSitePresheafExact as Graph
import DASHI.Reasoning.TrialecticWavePhaseGroupoidPresheafExact as OldPhase

GraphFibreHom :
  (policy : Tower.T27CompletionPolicy) →
  {U : Site.RelObj} →
  Graph.GraphSection policy U →
  Graph.GraphSection policy U →
  Set
GraphFibreHom policy {U} x y =
  OldPhase.FibreHom
    (Graph.graphSectionToOld policy U x)
    (Graph.graphSectionToOld policy U y)

graphPhaseOf :
  (policy : Tower.T27CompletionPolicy) →
  {U : Site.RelObj}
  {x y : Graph.GraphSection policy U} →
  GraphFibreHom policy x y →
  TriTruth
graphPhaseOf policy hom = OldPhase.phaseOf hom

graphHomEquivalent :
  (policy : Tower.T27CompletionPolicy) →
  {U : Site.RelObj}
  {x y : Graph.GraphSection policy U} →
  GraphFibreHom policy x y →
  GraphFibreHom policy x y →
  Set
graphHomEquivalent policy f g =
  graphPhaseOf policy f ≡ graphPhaseOf policy g

graphIdentityHom :
  (policy : Tower.T27CompletionPolicy) →
  {U : Site.RelObj} →
  (x : Graph.GraphSection policy U) →
  GraphFibreHom policy x x
graphIdentityHom policy {U} x =
  OldPhase.identityHom (Graph.graphSectionToOld policy U x)

graphComposeHom :
  (policy : Tower.T27CompletionPolicy) →
  {U : Site.RelObj}
  {x y z : Graph.GraphSection policy U} →
  GraphFibreHom policy y z →
  GraphFibreHom policy x y →
  GraphFibreHom policy x z
graphComposeHom policy g f = OldPhase.composeHom g f

graphInverseHom :
  (policy : Tower.T27CompletionPolicy) →
  {U : Site.RelObj}
  {x y : Graph.GraphSection policy U} →
  GraphFibreHom policy x y →
  GraphFibreHom policy y x
graphInverseHom policy f = OldPhase.inverseHom f

graphLeftIdentity :
  (policy : Tower.T27CompletionPolicy) →
  {U : Site.RelObj}
  {x y : Graph.GraphSection policy U} →
  (f : GraphFibreHom policy x y) →
  graphHomEquivalent policy
    (graphComposeHom policy (graphIdentityHom policy y) f)
    f
graphLeftIdentity policy f = OldPhase.leftIdentity f

graphRightIdentity :
  (policy : Tower.T27CompletionPolicy) →
  {U : Site.RelObj}
  {x y : Graph.GraphSection policy U} →
  (f : GraphFibreHom policy x y) →
  graphHomEquivalent policy
    (graphComposeHom policy f (graphIdentityHom policy x))
    f
graphRightIdentity policy f = OldPhase.rightIdentity f

graphAssociative :
  (policy : Tower.T27CompletionPolicy) →
  {U : Site.RelObj}
  {w x y z : Graph.GraphSection policy U} →
  (h : GraphFibreHom policy y z) →
  (g : GraphFibreHom policy x y) →
  (f : GraphFibreHom policy w x) →
  graphHomEquivalent policy
    (graphComposeHom policy h (graphComposeHom policy g f))
    (graphComposeHom policy (graphComposeHom policy h g) f)
graphAssociative policy h g f = OldPhase.associative h g f

graphInverseAfterForward :
  (policy : Tower.T27CompletionPolicy) →
  {U : Site.RelObj}
  {x y : Graph.GraphSection policy U} →
  (f : GraphFibreHom policy x y) →
  graphHomEquivalent policy
    (graphComposeHom policy (graphInverseHom policy f) f)
    (graphIdentityHom policy x)
graphInverseAfterForward policy f = OldPhase.inverseAfterForward f

graphForwardAfterInverse :
  (policy : Tower.T27CompletionPolicy) →
  {U : Site.RelObj}
  {x y : Graph.GraphSection policy U} →
  (f : GraphFibreHom policy x y) →
  graphHomEquivalent policy
    (graphComposeHom policy f (graphInverseHom policy f))
    (graphIdentityHom policy y)
graphForwardAfterInverse policy f = OldPhase.forwardAfterInverse f

graphRestrictHom :
  (policy : Tower.T27CompletionPolicy) →
  ∀ {U V : Site.RelObj}
    (arrow : Site.RelHom U V)
    {x y : Graph.GraphSection policy V} →
  GraphFibreHom policy x y →
  GraphFibreHom policy
    (Graph.graphRestrict policy arrow x)
    (Graph.graphRestrict policy arrow y)
graphRestrictHom policy arrow hom =
  OldPhase.restrictHom arrow hom

graphRestrictHomPreservesPhase :
  (policy : Tower.T27CompletionPolicy) →
  ∀ {U V : Site.RelObj}
    (arrow : Site.RelHom U V)
    {x y : Graph.GraphSection policy V}
    (hom : GraphFibreHom policy x y) →
  graphPhaseOf policy (graphRestrictHom policy arrow hom)
  ≡ graphPhaseOf policy hom
graphRestrictHomPreservesPhase policy arrow hom =
  OldPhase.restrictHomPreservesPhase arrow hom

graphRestrictIdentityHom :
  (policy : Tower.T27CompletionPolicy) →
  ∀ {U : Site.RelObj}
    {x y : Graph.GraphSection policy U}
    (hom : GraphFibreHom policy x y) →
  graphHomEquivalent policy
    (graphRestrictHom policy (Site.idR U) hom)
    hom
graphRestrictIdentityHom policy hom =
  OldPhase.restrictIdentityHom hom

graphRestrictCompositionHom :
  (policy : Tower.T27CompletionPolicy) →
  ∀ {U V W : Site.RelObj}
    (g : Site.RelHom V W)
    (f : Site.RelHom U V)
    {x y : Graph.GraphSection policy W}
    (hom : GraphFibreHom policy x y) →
  graphHomEquivalent policy
    (graphRestrictHom policy (Site.composeRel g f) hom)
    (graphRestrictHom policy f (graphRestrictHom policy g hom))
graphRestrictCompositionHom policy g f hom =
  OldPhase.restrictCompositionHom g f hom

graphRestrictPreservesIdentity :
  (policy : Tower.T27CompletionPolicy) →
  ∀ {U V : Site.RelObj}
    (arrow : Site.RelHom U V)
    (x : Graph.GraphSection policy V) →
  graphHomEquivalent policy
    (graphRestrictHom policy arrow (graphIdentityHom policy x))
    (graphIdentityHom policy (Graph.graphRestrict policy arrow x))
graphRestrictPreservesIdentity policy {V = V} arrow x =
  OldPhase.restrictPreservesIdentity arrow
    (Graph.graphSectionToOld policy V x)

graphRestrictPreservesComposition :
  (policy : Tower.T27CompletionPolicy) →
  ∀ {U V : Site.RelObj}
    (arrow : Site.RelHom U V)
    {x y z : Graph.GraphSection policy V}
    (g : GraphFibreHom policy y z)
    (f : GraphFibreHom policy x y) →
  graphHomEquivalent policy
    (graphRestrictHom policy arrow (graphComposeHom policy g f))
    (graphComposeHom policy
      (graphRestrictHom policy arrow g)
      (graphRestrictHom policy arrow f))
graphRestrictPreservesComposition policy arrow g f =
  OldPhase.restrictPreservesComposition arrow g f

graphPositivePhaseAutomorphism :
  (policy : Tower.T27CompletionPolicy) →
  {U : Site.RelObj} →
  (x : Graph.GraphSection policy U) →
  GraphFibreHom policy x x
graphPositivePhaseAutomorphism policy {U} x =
  OldPhase.positivePhaseAutomorphism
    (Graph.graphSectionToOld policy U x)

graphPositivePhaseDiffersFromIdentity :
  (policy : Tower.T27CompletionPolicy) →
  {U : Site.RelObj} →
  (x : Graph.GraphSection policy U) →
  graphHomEquivalent policy
    (graphIdentityHom policy x)
    (graphPositivePhaseAutomorphism policy x) →
  ⊥
graphPositivePhaseDiffersFromIdentity policy {U} x =
  OldPhase.positivePhaseDiffersFromIdentity
    (Graph.graphSectionToOld policy U x)

record TrialecticT27WavePhaseGroupoidPresheafBoundary : Set where
  constructor trialectic-t27-wave-phase-groupoid-presheaf-boundary
  field
    globalCompletedT27CarriesPhaseGroupoid : Bool
    localT9T3GroupoidsReused : Bool
    identityCompositionInverseTransported : Bool
    groupoidLawsTransportedModuloPhaseSetoid : Bool
    restrictionMorphismFunctorTransported : Bool
    restrictionFunctorLawsTransported : Bool
    nontrivialPhaseAutomorphismAtCompletedT27 : Bool
    unconstrainedAmbientT27PromotedToGroupoidObject : Bool

open TrialecticT27WavePhaseGroupoidPresheafBoundary public

canonicalTrialecticT27WavePhaseGroupoidPresheafBoundary :
  TrialecticT27WavePhaseGroupoidPresheafBoundary
canonicalTrialecticT27WavePhaseGroupoidPresheafBoundary =
  trialectic-t27-wave-phase-groupoid-presheaf-boundary
    true true true true true true true false
