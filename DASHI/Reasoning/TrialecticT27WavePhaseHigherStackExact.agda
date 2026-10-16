module DASHI.Reasoning.TrialecticT27WavePhaseHigherStackExact where

------------------------------------------------------------------------
-- SETOID-TRUNCATED HIGHER STACK ON THE COMPLETED T^27 GRAPH PRESHEAF
--
-- The T^27 promotion is an exact global-carrier transport of the mature
-- wave-phase stack.  Restriction unit/composition coherence is witnessed by
-- graph phase 2-cells, effective descent is paid on objects and morphisms, and
-- proof witnesses are truncated by a terminal 3-cell relation exactly as in
-- the older T^18 presentation.
--
-- This is a higher-stack certificate for CompletedT27(policy), not for the
-- unconstrained ambient T^27 carrier.  The latter has nine additional free
-- coordinates and is intentionally outside the promotion.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27GraphSitePresheafExact as Graph
import DASHI.Reasoning.TrialecticT27WavePhaseGroupoidPresheafExact as Groupoid27
import DASHI.Reasoning.TrialecticT27WavePhaseTwoCellExact as Two27
import DASHI.Reasoning.TrialecticT27EffectiveStackDescentExact as Stack27
import DASHI.Reasoning.TrialecticT27FiniteTriadicHypersheafExact as Hyper27

------------------------------------------------------------------------
-- 1. Restriction pseudofunctor coherence as explicit graph phase 2-cells.
------------------------------------------------------------------------

graphRestrictionUnit2Cell :
  (policy : Tower.T27CompletionPolicy) →
  ∀ {U : Site.RelObj}
    {x y : Graph.GraphSection policy U}
    (hom : Groupoid27.GraphFibreHom policy x y) →
  Two27.GraphPhase2Cell policy
    (Groupoid27.graphRestrictHom policy (Site.idR U) hom)
    hom
graphRestrictionUnit2Cell policy hom =
  Groupoid27.graphRestrictIdentityHom policy hom

graphRestrictionComposition2Cell :
  (policy : Tower.T27CompletionPolicy) →
  ∀ {U V W : Site.RelObj}
    (g : Site.RelHom V W)
    (f : Site.RelHom U V)
    {x y : Graph.GraphSection policy W}
    (hom : Groupoid27.GraphFibreHom policy x y) →
  Two27.GraphPhase2Cell policy
    (Groupoid27.graphRestrictHom policy (Site.composeRel g f) hom)
    (Groupoid27.graphRestrictHom policy f
      (Groupoid27.graphRestrictHom policy g hom))
graphRestrictionComposition2Cell policy g f hom =
  Groupoid27.graphRestrictCompositionHom policy g f hom

------------------------------------------------------------------------
-- 2. Proof-witness truncation at the next level.
------------------------------------------------------------------------

GraphPhase3Cell :
  {policy : Tower.T27CompletionPolicy}
  {U : Site.RelObj}
  {x y : Graph.GraphSection policy U}
  {f g : Groupoid27.GraphFibreHom policy x y} →
  Two27.GraphPhase2Cell policy f g →
  Two27.GraphPhase2Cell policy f g →
  Set
GraphPhase3Cell alpha beta = ⊤

graphPhase3CellRefl :
  {policy : Tower.T27CompletionPolicy}
  {U : Site.RelObj}
  {x y : Graph.GraphSection policy U}
  {f g : Groupoid27.GraphFibreHom policy x y} →
  (alpha : Two27.GraphPhase2Cell policy f g) →
  GraphPhase3Cell alpha alpha
graphPhase3CellRefl alpha = tt

graphPhase3CellSym :
  {policy : Tower.T27CompletionPolicy}
  {U : Site.RelObj}
  {x y : Graph.GraphSection policy U}
  {f g : Groupoid27.GraphFibreHom policy x y}
  {alpha beta : Two27.GraphPhase2Cell policy f g} →
  GraphPhase3Cell alpha beta →
  GraphPhase3Cell beta alpha
graphPhase3CellSym cell = tt

graphPhase3CellTrans :
  {policy : Tower.T27CompletionPolicy}
  {U : Site.RelObj}
  {x y : Graph.GraphSection policy U}
  {f g : Groupoid27.GraphFibreHom policy x y}
  {alpha beta gamma : Two27.GraphPhase2Cell policy f g} →
  GraphPhase3Cell alpha beta →
  GraphPhase3Cell beta gamma →
  GraphPhase3Cell alpha gamma
graphPhase3CellTrans left right = tt

------------------------------------------------------------------------
-- 3. Imported exact promotion receipts.
------------------------------------------------------------------------

groupoidBoundary : Groupoid27.TrialecticT27WavePhaseGroupoidPresheafBoundary
groupoidBoundary = Groupoid27.canonicalTrialecticT27WavePhaseGroupoidPresheafBoundary

twoBoundary : Two27.TrialecticT27WavePhaseTwoCellBoundary
twoBoundary = Two27.canonicalTrialecticT27WavePhaseTwoCellBoundary

stackBoundary : Stack27.TrialecticT27EffectiveStackBoundary
stackBoundary = Stack27.canonicalTrialecticT27EffectiveStackBoundary

hyperBoundary : Hyper27.TrialecticT27FiniteTriadicHypersheafBoundary
hyperBoundary = Hyper27.canonicalTrialecticT27FiniteTriadicHypersheafBoundary

completedGroupoidReceipt :
  Groupoid27.globalCompletedT27CarriesPhaseGroupoid groupoidBoundary ≡ true
completedGroupoidReceipt = refl

completedEffectiveStackReceipt :
  Stack27.completedT27MorphismDescentPaid stackBoundary ≡ true
completedEffectiveStackReceipt = refl

completedTwoCellReceipt :
  Two27.phaseTwoCellsOnEveryGraphSiteFibre twoBoundary ≡ true
completedTwoCellReceipt = refl

completedFiniteHypersheafReceipt :
  Hyper27.certifiedCompletedT27FiniteHypersheaf hyperBoundary ≡ true
completedFiniteHypersheafReceipt = refl

------------------------------------------------------------------------
-- 4. Promotion boundary.
------------------------------------------------------------------------

record TrialecticT27WavePhaseHigherStackBoundary : Set where
  constructor trialectic-t27-wave-phase-higher-stack-boundary
  field
    completedT27GroupoidPresheafPaid : Bool
    completedT27RestrictionPseudofunctorPaid : Bool
    completedT27EffectiveStackPaid : Bool
    completedT27TwoCellCalculusPaid : Bool
    completedT27ProofWitnessSetoidPaid : Bool
    certifiedCompletedT27HigherStack : Bool
    certifiedCompletedT27FiniteHypersheaf : Bool
    completedT27FreeInformationRemainsT18 : Bool
    unconstrainedAmbientT27HigherStackClaimed : Bool
    certifiedArbitraryInfinityT27Hypersheaf : Bool

open TrialecticT27WavePhaseHigherStackBoundary public

canonicalTrialecticT27WavePhaseHigherStackBoundary :
  TrialecticT27WavePhaseHigherStackBoundary
canonicalTrialecticT27WavePhaseHigherStackBoundary =
  trialectic-t27-wave-phase-higher-stack-boundary
    true true true true true true true true false false
