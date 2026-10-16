module DASHI.Reasoning.TrialecticT27WavePhaseTwoCellExact where

------------------------------------------------------------------------
-- PHASE 2-CELLS ON THE COMPLETED T^27 GROUPOID PRESHEAF
--
-- The graph lift changes object payload only.  Its hom setoid remains equality
-- of the retained C3/TriTruth phase.  Consequently the full phase 2-cell
-- calculus transports pointwise: identity/reversal/vertical composition,
-- whiskering, horizontal composition and restriction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369TriTruthField as Tri
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Foundations.RelationalStageTwelveSiteExact as RelSheaf
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticWavePhaseGroupoidPresheafExact as OldPhase
import DASHI.Reasoning.TrialecticWavePhaseEffectiveStackDescentExact as OldStack
import DASHI.Reasoning.TrialecticWavePhaseTwoCellCocycleExact as OldTwo
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27GraphSitePresheafExact as Graph
import DASHI.Reasoning.TrialecticT27WavePhaseGroupoidPresheafExact as Phase27

GraphPhase2Cell :
  (policy : Tower.T27CompletionPolicy) →
  {U : Site.RelObj}
  {x y : Graph.GraphSection policy U} →
  Phase27.GraphFibreHom policy x y →
  Phase27.GraphFibreHom policy x y →
  Set
GraphPhase2Cell policy = Phase27.graphHomEquivalent policy

graphIdentity2Cell :
  {policy : Tower.T27CompletionPolicy}
  {U : Site.RelObj}
  {x y : Graph.GraphSection policy U}
  {f : Phase27.GraphFibreHom policy x y} →
  GraphPhase2Cell policy f f
graphIdentity2Cell = refl

graphReverse2Cell :
  {policy : Tower.T27CompletionPolicy}
  {U : Site.RelObj}
  {x y : Graph.GraphSection policy U}
  {f g : Phase27.GraphFibreHom policy x y} →
  GraphPhase2Cell policy f g →
  GraphPhase2Cell policy g f
graphReverse2Cell = sym

graphVerticalCompose :
  {policy : Tower.T27CompletionPolicy}
  {U : Site.RelObj}
  {x y : Graph.GraphSection policy U}
  {f g h : Phase27.GraphFibreHom policy x y} →
  GraphPhase2Cell policy f g →
  GraphPhase2Cell policy g h →
  GraphPhase2Cell policy f h
graphVerticalCompose = trans

graphLeftWhisker :
  {policy : Tower.T27CompletionPolicy}
  {U : Site.RelObj}
  {x y z : Graph.GraphSection policy U}
  {f g : Phase27.GraphFibreHom policy x y} →
  (h : Phase27.GraphFibreHom policy y z) →
  GraphPhase2Cell policy f g →
  GraphPhase2Cell policy
    (Phase27.graphComposeHom policy h f)
    (Phase27.graphComposeHom policy h g)
graphLeftWhisker {policy} h alpha =
  cong (λ p → Tri.triAdd (Phase27.graphPhaseOf policy h) p) alpha

graphRightWhisker :
  {policy : Tower.T27CompletionPolicy}
  {U : Site.RelObj}
  {x y z : Graph.GraphSection policy U}
  {f g : Phase27.GraphFibreHom policy y z} →
  (h : Phase27.GraphFibreHom policy x y) →
  GraphPhase2Cell policy f g →
  GraphPhase2Cell policy
    (Phase27.graphComposeHom policy f h)
    (Phase27.graphComposeHom policy g h)
graphRightWhisker {policy} h alpha =
  cong (λ p → Tri.triAdd p (Phase27.graphPhaseOf policy h)) alpha

graphHorizontalCompose :
  {policy : Tower.T27CompletionPolicy}
  {U : Site.RelObj}
  {w x y : Graph.GraphSection policy U}
  {f g : Phase27.GraphFibreHom policy w x}
  {h k : Phase27.GraphFibreHom policy x y} →
  GraphPhase2Cell policy h k →
  GraphPhase2Cell policy f g →
  GraphPhase2Cell policy
    (Phase27.graphComposeHom policy h f)
    (Phase27.graphComposeHom policy k g)
graphHorizontalCompose beta alpha = cong₂ Tri.triAdd beta alpha

graphRestrict2Cell :
  {policy : Tower.T27CompletionPolicy} →
  ∀ {U V : Site.RelObj}
    (arrow : Site.RelHom U V)
    {x y : Graph.GraphSection policy V}
    {f g : Phase27.GraphFibreHom policy x y} →
  GraphPhase2Cell policy f g →
  GraphPhase2Cell policy
    (Phase27.graphRestrictHom policy arrow f)
    (Phase27.graphRestrictHom policy arrow g)
graphRestrict2Cell {policy} arrow {f = f} {g = g} alpha =
  trans
    (Phase27.graphRestrictHomPreservesPhase policy arrow f)
    (trans alpha
      (sym (Phase27.graphRestrictHomPreservesPhase policy arrow g)))

------------------------------------------------------------------------
-- The triadic overlap cocycle is local T^9 data, hence literally unchanged by
-- replacing only the global object with its completed T^27 graph equivalent.
------------------------------------------------------------------------

graphTriadicPhaseCycleCloses :
  ∀ {source target : RelSheaf.TriadicLocals Cell.CellDialectic} →
  (morphisms : OldStack.TriadicPhaseMorphisms source target) →
  Tri.triAdd
    (OldPhase.equalityPhase (OldStack.morphismAB morphisms))
    (Tri.triAdd
      (OldPhase.equalityPhase (OldStack.morphismBC morphisms))
      (OldPhase.equalityPhase (OldStack.morphismCA morphisms)))
  ≡
  Tri.triAdd
    (OldPhase.equalityPhase (OldStack.morphismAB morphisms))
    (Tri.triAdd
      (OldPhase.equalityPhase (OldStack.morphismAB morphisms))
      (OldPhase.equalityPhase (OldStack.morphismAB morphisms)))
graphTriadicPhaseCycleCloses = OldTwo.triadicPhaseCycleCloses

record TrialecticT27WavePhaseTwoCellBoundary : Set where
  constructor trialectic-t27-wave-phase-two-cell-boundary
  field
    phaseTwoCellsOnEveryGraphSiteFibre : Bool
    identityReverseVerticalPaid : Bool
    leftRightWhiskeringPaid : Bool
    horizontalCompositionPaid : Bool
    restrictionPreservesTwoCells : Bool
    arbitraryTriadicOverlapPhaseCocycleReused : Bool
    completedT27ChangesLocalCocycle : Bool

open TrialecticT27WavePhaseTwoCellBoundary public

canonicalTrialecticT27WavePhaseTwoCellBoundary :
  TrialecticT27WavePhaseTwoCellBoundary
canonicalTrialecticT27WavePhaseTwoCellBoundary =
  trialectic-t27-wave-phase-two-cell-boundary
    true true true true true true false
