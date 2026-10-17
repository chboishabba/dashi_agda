module DASHI.Reasoning.TrialecticWavePhaseTwoCellCocycleExact where

------------------------------------------------------------------------
-- GENERAL PHASE 2-CELLS + TRIADIC OVERLAP COCYCLE
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369TriTruthField as Tri
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Foundations.RelationalStageTwelveSiteExact as RelSheaf
import DASHI.Reasoning.TrialecticGrothendieckCellPresheafExact as Presheaf
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticWavePhaseGroupoidPresheafExact as Phase
import DASHI.Reasoning.TrialecticWavePhaseEffectiveStackDescentExact as Stack

Phase2Cell :
  {U : Site.RelObj}
  {x y : Presheaf.Section U} →
  Phase.FibreHom x y →
  Phase.FibreHom x y →
  Set
Phase2Cell = Phase._≈ₚ_

identity2Cell :
  {U : Site.RelObj}
  {x y : Presheaf.Section U}
  {f : Phase.FibreHom x y} →
  Phase2Cell f f
identity2Cell = refl

reverse2Cell :
  {U : Site.RelObj}
  {x y : Presheaf.Section U}
  {f g : Phase.FibreHom x y} →
  Phase2Cell f g → Phase2Cell g f
reverse2Cell = sym

verticalCompose :
  {U : Site.RelObj}
  {x y : Presheaf.Section U}
  {f g h : Phase.FibreHom x y} →
  Phase2Cell f g →
  Phase2Cell g h →
  Phase2Cell f h
verticalCompose = trans

leftWhisker :
  {U : Site.RelObj}
  {x y z : Presheaf.Section U}
  {f g : Phase.FibreHom x y} →
  (h : Phase.FibreHom y z) →
  Phase2Cell f g →
  Phase2Cell
    (Phase.composeHom h f)
    (Phase.composeHom h g)
leftWhisker h alpha =
  cong (λ p → Tri.triAdd (Phase.phaseOf h) p) alpha

rightWhisker :
  {U : Site.RelObj}
  {x y z : Presheaf.Section U}
  {f g : Phase.FibreHom y z} →
  (h : Phase.FibreHom x y) →
  Phase2Cell f g →
  Phase2Cell
    (Phase.composeHom f h)
    (Phase.composeHom g h)
rightWhisker h alpha =
  cong (λ p → Tri.triAdd p (Phase.phaseOf h)) alpha

horizontalCompose :
  {U : Site.RelObj}
  {w x y : Presheaf.Section U}
  {f g : Phase.FibreHom w x}
  {h k : Phase.FibreHom x y} →
  Phase2Cell h k →
  Phase2Cell f g →
  Phase2Cell
    (Phase.composeHom h f)
    (Phase.composeHom k g)
horizontalCompose beta alpha = cong₂ Tri.triAdd beta alpha

restrict2Cell :
  ∀ {U V : Site.RelObj}
    (arrow : Site.RelHom U V)
    {x y : Presheaf.Section V}
    {f g : Phase.FibreHom x y} →
  Phase2Cell f g →
  Phase2Cell (Phase.restrictHom arrow f) (Phase.restrictHom arrow g)
restrict2Cell arrow {f = f} {g = g} alpha =
  trans
    (Phase.restrictHomPreservesPhase arrow f)
    (trans alpha (sym (Phase.restrictHomPreservesPhase arrow g)))

phaseBCequalsCA :
  ∀ {source target : RelSheaf.TriadicLocals Cell.CellDialectic}
    (morphisms : Stack.TriadicPhaseMorphisms source target) →
  Phase.equalityPhase (Stack.morphismBC morphisms)
  ≡
  Phase.equalityPhase (Stack.morphismCA morphisms)
phaseBCequalsCA morphisms =
  trans
    (sym (Stack.phaseABequalsBC morphisms))
    (Stack.phaseABequalsCA morphisms)

triadicPhaseCycleCloses :
  ∀ {source target : RelSheaf.TriadicLocals Cell.CellDialectic}
    (morphisms : Stack.TriadicPhaseMorphisms source target) →
  Tri.triAdd
    (Phase.equalityPhase (Stack.morphismAB morphisms))
    (Tri.triAdd
      (Phase.equalityPhase (Stack.morphismBC morphisms))
      (Phase.equalityPhase (Stack.morphismCA morphisms)))
  ≡
  Tri.triAdd
    (Phase.equalityPhase (Stack.morphismAB morphisms))
    (Tri.triAdd
      (Phase.equalityPhase (Stack.morphismAB morphisms))
      (Phase.equalityPhase (Stack.morphismAB morphisms)))
triadicPhaseCycleCloses morphisms
  rewrite sym (Stack.phaseABequalsBC morphisms)
        | sym (Stack.phaseABequalsCA morphisms)
  = refl

record TrialecticWavePhaseTwoCellBoundary : Set where
  constructor trialectic-wave-phase-two-cell-boundary
  field
    phaseTwoCellsOnEverySiteFibre : Bool
    identityReverseVerticalPaid : Bool
    leftRightWhiskeringPaid : Bool
    horizontalCompositionPaid : Bool
    restrictionPreservesTwoCells : Bool
    arbitraryTriadicOverlapPhaseCocyclePaid : Bool
    concreteC3OnlyRestrictionRemoved : Bool

open TrialecticWavePhaseTwoCellBoundary public

canonicalTrialecticWavePhaseTwoCellBoundary :
  TrialecticWavePhaseTwoCellBoundary
canonicalTrialecticWavePhaseTwoCellBoundary =
  trialectic-wave-phase-two-cell-boundary
    true true true true true true true
