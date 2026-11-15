module DASHI.Reasoning.TrialecticWavePhaseEffectiveStackDescentExact where

------------------------------------------------------------------------
-- EFFECTIVE MORPHISM DESCENT FOR THE C3 WAVE-PHASE GROUPOID PRESHEAF
--
-- Object descent was already paid by TrialecticSetEffectiveDescentExact.
-- TrialecticWavePhaseGroupoidPresheafExact adds a non-discrete C3 phase to
-- every fibre hom.  Because restriction preserves that phase exactly, local
-- edge morphisms with one common phase glue to a global observational morphism.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369TriTruthField as Tri
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Foundations.RelationalStageTwelveSiteExact as RelSheaf
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticGrothendieckThreeCellDescentExact as Descent
import DASHI.Reasoning.TrialecticSetEffectiveDescentExact as SetEffective
import DASHI.Reasoning.TrialecticWavePhaseGroupoidPresheafExact as Phase

------------------------------------------------------------------------
-- 1. Compatible local morphisms.
------------------------------------------------------------------------

record TriadicPhaseMorphisms
    (source target : RelSheaf.TriadicLocals Cell.CellDialectic) : Set where
  constructor triadic-phase-morphisms
  field
    morphismAB :
      Phase.PhaseEqualityHom
        (RelSheaf.localAB source)
        (RelSheaf.localAB target)
    morphismBC :
      Phase.PhaseEqualityHom
        (RelSheaf.localBC source)
        (RelSheaf.localBC target)
    morphismCA :
      Phase.PhaseEqualityHom
        (RelSheaf.localCA source)
        (RelSheaf.localCA target)
    phaseABequalsBC :
      Phase.equalityPhase morphismAB ≡ Phase.equalityPhase morphismBC
    phaseABequalsCA :
      Phase.equalityPhase morphismAB ≡ Phase.equalityPhase morphismCA

open TriadicPhaseMorphisms public

------------------------------------------------------------------------
-- 2. Glue morphisms over already-compatible object data.
------------------------------------------------------------------------

gluePhaseMorphisms :
  (source target : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (sourceCompatibility :
    RelSheaf.CompatibleOnTriadicCover Descent.cellOverlapSystem source) →
  (targetCompatibility :
    RelSheaf.CompatibleOnTriadicCover Descent.cellOverlapSystem target) →
  TriadicPhaseMorphisms source target →
  Phase.GlobalPhaseHom
    (Descent.glueStructured source sourceCompatibility)
    (Descent.glueStructured target targetCompatibility)
gluePhaseMorphisms source target sourceCompatibility targetCompatibility morphisms =
  Phase.global-phase-hom
    (SetEffective.boundary-observational-equivalence
      sameAB'
      sameBC'
      sameCA')
    (Phase.equalityPhase (morphismAB morphisms))
  where
    sameAB' :
      Descent.restrictStructuredAB
        (Descent.glueStructured source sourceCompatibility)
      ≡
      Descent.restrictStructuredAB
        (Descent.glueStructured target targetCompatibility)
    sameAB' =
      trans
        (Descent.glueStructuredRestrictsAB source sourceCompatibility)
        (trans
          (Phase.underlyingEquality (morphismAB morphisms))
          (sym (Descent.glueStructuredRestrictsAB target targetCompatibility)))

    sameBC' :
      Descent.restrictStructuredBC
        (Descent.glueStructured source sourceCompatibility)
      ≡
      Descent.restrictStructuredBC
        (Descent.glueStructured target targetCompatibility)
    sameBC' =
      trans
        (Descent.glueStructuredRestrictsBC source sourceCompatibility)
        (trans
          (Phase.underlyingEquality (morphismBC morphisms))
          (sym (Descent.glueStructuredRestrictsBC target targetCompatibility)))

    sameCA' :
      Descent.restrictStructuredCA
        (Descent.glueStructured source sourceCompatibility)
      ≡
      Descent.restrictStructuredCA
        (Descent.glueStructured target targetCompatibility)
    sameCA' =
      trans
        (Descent.glueStructuredRestrictsCA source sourceCompatibility)
        (trans
          (Phase.underlyingEquality (morphismCA morphisms))
          (sym (Descent.glueStructuredRestrictsCA target targetCompatibility)))

------------------------------------------------------------------------
-- 3. All three local morphisms are recovered up to the phase setoid.
------------------------------------------------------------------------

recoverAB :
  (source target : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (sourceCompatibility :
    RelSheaf.CompatibleOnTriadicCover Descent.cellOverlapSystem source) →
  (targetCompatibility :
    RelSheaf.CompatibleOnTriadicCover Descent.cellOverlapSystem target) →
  (morphisms : TriadicPhaseMorphisms source target) →
  Phase.restrictHom Site.abToGlobal
    (gluePhaseMorphisms
      source target sourceCompatibility targetCompatibility morphisms)
  Phase.≈ₚ
  morphismAB morphisms
recoverAB source target sourceCompatibility targetCompatibility morphisms = refl

recoverBC :
  (source target : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (sourceCompatibility :
    RelSheaf.CompatibleOnTriadicCover Descent.cellOverlapSystem source) →
  (targetCompatibility :
    RelSheaf.CompatibleOnTriadicCover Descent.cellOverlapSystem target) →
  (morphisms : TriadicPhaseMorphisms source target) →
  Phase.restrictHom Site.bcToGlobal
    (gluePhaseMorphisms
      source target sourceCompatibility targetCompatibility morphisms)
  Phase.≈ₚ
  morphismBC morphisms
recoverBC source target sourceCompatibility targetCompatibility morphisms =
  phaseABequalsBC morphisms

recoverCA :
  (source target : RelSheaf.TriadicLocals Cell.CellDialectic) →
  (sourceCompatibility :
    RelSheaf.CompatibleOnTriadicCover Descent.cellOverlapSystem source) →
  (targetCompatibility :
    RelSheaf.CompatibleOnTriadicCover Descent.cellOverlapSystem target) →
  (morphisms : TriadicPhaseMorphisms source target) →
  Phase.restrictHom Site.caToGlobal
    (gluePhaseMorphisms
      source target sourceCompatibility targetCompatibility morphisms)
  Phase.≈ₚ
  morphismCA morphisms
recoverCA source target sourceCompatibility targetCompatibility morphisms =
  phaseABequalsCA morphisms

------------------------------------------------------------------------
-- 4. Global realizations are unique up to a typed phase-groupoid isomorphism.
------------------------------------------------------------------------

record GlobalPhaseIso
    (left right : Cell.CompatibleThreeCellTrialecticBoundary) : Set where
  constructor global-phase-iso
  field
    forward : Phase.GlobalPhaseHom left right
    backward : Phase.GlobalPhaseHom right left
    backwardAfterForward :
      Phase.composeHom backward forward
      Phase.≈ₚ
      Phase.identityHom left
    forwardAfterBackward :
      Phase.composeHom forward backward
      Phase.≈ₚ
      Phase.identityHom right

open GlobalPhaseIso public

realizationsUniqueUpToTypedIso :
  ∀ {locals : RelSheaf.TriadicLocals Cell.CellDialectic} →
  (left right : SetEffective.GlobalRealization locals) →
  GlobalPhaseIso
    (SetEffective.globalBoundary left)
    (SetEffective.globalBoundary right)
realizationsUniqueUpToTypedIso left right =
  global-phase-iso
    forwardHom
    (Phase.inverseHom forwardHom)
    (Phase.inverseAfterForward forwardHom)
    (Phase.forwardAfterInverse forwardHom)
  where
    forwardHom :
      Phase.GlobalPhaseHom
        (SetEffective.globalBoundary left)
        (SetEffective.globalBoundary right)
    forwardHom =
      Phase.global-phase-hom
        (SetEffective.realizationsObservationallyUnique left right)
        Tri.triZero

------------------------------------------------------------------------
-- 5. Promotion boundary for the distinguished triadic cover.
------------------------------------------------------------------------

record TrialecticWavePhaseEffectiveStackBoundary : Set where
  constructor trialectic-wave-phase-effective-stack-boundary
  field
    objectEffectiveDescentPaid : Bool
    fullSiteNonDiscreteGroupoidPresheafPaid : Bool
    compatibleLocalMorphismsGlue : Bool
    allThreeLocalMorphismsRecovered : Bool
    globalRealizationsUniqueUpToTypedIso : Bool
    distinguishedTriadicCoverPrestackPaid : Bool
    distinguishedTriadicCoverEffectiveStackPaid : Bool
    arbitraryHypercoverDescentPaid : Bool

open TrialecticWavePhaseEffectiveStackBoundary public

canonicalTrialecticWavePhaseEffectiveStackBoundary :
  TrialecticWavePhaseEffectiveStackBoundary
canonicalTrialecticWavePhaseEffectiveStackBoundary =
  trialectic-wave-phase-effective-stack-boundary
    true true true true true true true false
