module DASHI.Culture.IntersectionalPowerValueFolkModelBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Intersectionality / power / ideology / value / folk-model boundary.
--
-- This module gathers the remaining philosophical audit lanes without making
-- any philosopher, level model, attraction model, or political metaphor a
-- sovereign ontology. Each lane is an audit question or candidate operator.

data StructuralAxis : Set where
  raceAxis : StructuralAxis
  sexGenderAxis : StructuralAxis
  classAxis : StructuralAxis
  disabilityAxis : StructuralAxis
  sexualityAxis : StructuralAxis
  ageAxis : StructuralAxis
  familyRoleAxis : StructuralAxis
  colonialAxis : StructuralAxis
  institutionalAxis : StructuralAxis
  neurotypeAxis : StructuralAxis
  legalAuthorityAxis : StructuralAxis
  careDependencyAxis : StructuralAxis

canonicalStructuralAxes : List StructuralAxis
canonicalStructuralAxes =
  raceAxis ∷ sexGenderAxis ∷ classAxis ∷ disabilityAxis
  ∷ sexualityAxis ∷ ageAxis ∷ familyRoleAxis ∷ colonialAxis
  ∷ institutionalAxis ∷ neurotypeAxis ∷ legalAuthorityAxis
  ∷ careDependencyAxis ∷ []

data PhilosophicalAudit : Set where
  foucaultPowerAudit : PhilosophicalAudit
  zizekFantasyAudit : PhilosophicalAudit
  marxMaterialAudit : PhilosophicalAudit
  nietzscheResidualToFormAudit : PhilosophicalAudit
  spinozaPowerToActAudit : PhilosophicalAudit
  kantNonInstrumentalisationAudit : PhilosophicalAudit
  levinasOtherExceedsChartAudit : PhilosophicalAudit
  derridaNoFinalClosureAudit : PhilosophicalAudit

canonicalPhilosophicalAudits : List PhilosophicalAudit
canonicalPhilosophicalAudits =
  foucaultPowerAudit
  ∷ zizekFantasyAudit
  ∷ marxMaterialAudit
  ∷ nietzscheResidualToFormAudit
  ∷ spinozaPowerToActAudit
  ∷ kantNonInstrumentalisationAudit
  ∷ levinasOtherExceedsChartAudit
  ∷ derridaNoFinalClosureAudit
  ∷ []

data FolkModelSurface : Set where
  developmentalLevelSurface : FolkModelSurface
  ickResidualSurface : FolkModelSurface
  relationalZoneSurface : FolkModelSurface
  hypergamyCandidateFibreSurface : FolkModelSurface
  environmentFeedbackLoopSurface : FolkModelSurface

canonicalFolkModelSurfaces : List FolkModelSurface
canonicalFolkModelSurfaces =
  developmentalLevelSurface
  ∷ ickResidualSurface
  ∷ relationalZoneSurface
  ∷ hypergamyCandidateFibreSurface
  ∷ environmentFeedbackLoopSurface
  ∷ []

record IntersectionalPowerValueFolkModelBoundary : Set where
  constructor mkIntersectionalPowerValueFolkModelBoundary
  field
    structuralAxes : List StructuralAxis
    structuralAxesAreCanonical : structuralAxes ≡ canonicalStructuralAxes

    philosophicalAudits : List PhilosophicalAudit
    philosophicalAuditsAreCanonical :
      philosophicalAudits ≡ canonicalPhilosophicalAudits

    folkModelSurfaces : List FolkModelSurface
    folkModelSurfacesAreCanonical :
      folkModelSurfaces ≡ canonicalFolkModelSurfaces

    structuralResidualTracked : Bool
    structuralResidualTrackedIsTrue : structuralResidualTracked ≡ true

    fantasyCanSuppressCarryTracked : Bool
    fantasyCanSuppressCarryTrackedIsTrue :
      fantasyCanSuppressCarryTracked ≡ true

    materialConditionsTracked : Bool
    materialConditionsTrackedIsTrue : materialConditionsTracked ≡ true

    willToPowerAsResidualToFormTracked : Bool
    willToPowerAsResidualToFormTrackedIsTrue :
      willToPowerAsResidualToFormTracked ≡ true

    anhedoniaAsTransitionValueCollapseTracked : Bool
    anhedoniaAsTransitionValueCollapseTrackedIsTrue :
      anhedoniaAsTransitionValueCollapseTracked ≡ true

    amalekEnemyCompressionTracked : Bool
    amalekEnemyCompressionTrackedIsTrue :
      amalekEnemyCompressionTracked ≡ true

    levelSovereigntyPromoted : Bool
    levelSovereigntyPromotedIsFalse : levelSovereigntyPromoted ≡ false

    genderEssencePromoted : Bool
    genderEssencePromotedIsFalse : genderEssencePromoted ≡ false

    ickSovereigntyPromoted : Bool
    ickSovereigntyPromotedIsFalse : ickSovereigntyPromoted ≡ false

    zoneEssencePromoted : Bool
    zoneEssencePromotedIsFalse : zoneEssencePromoted ≡ false

    hypergamySovereigntyPromoted : Bool
    hypergamySovereigntyPromotedIsFalse :
      hypergamySovereigntyPromoted ≡ false

    guruAuthorityPromoted : Bool
    guruAuthorityPromotedIsFalse : guruAuthorityPromoted ≡ false

    fascisticWillToPowerPromoted : Bool
    fascisticWillToPowerPromotedIsFalse :
      fascisticWillToPowerPromoted ≡ false

    reading : String

open IntersectionalPowerValueFolkModelBoundary public

canonicalIntersectionalPowerValueFolkModelBoundary :
  IntersectionalPowerValueFolkModelBoundary
canonicalIntersectionalPowerValueFolkModelBoundary =
  mkIntersectionalPowerValueFolkModelBoundary
    canonicalStructuralAxes refl
    canonicalPhilosophicalAudits refl
    canonicalFolkModelSurfaces refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Intersectionality supplies a multi-axis atlas; Foucault, Zizek, Marx, Nietzsche, Spinoza, Kant, Levinas, and Derrida remain audit lanes; levels, ick, zones, and hypergamy remain local folk-model surfaces rather than person essences."

canonicalLevelSovereigntyPromotedFalse :
  levelSovereigntyPromoted canonicalIntersectionalPowerValueFolkModelBoundary ≡ false
canonicalLevelSovereigntyPromotedFalse =
  levelSovereigntyPromotedIsFalse canonicalIntersectionalPowerValueFolkModelBoundary

canonicalFascisticWillToPowerPromotedFalse :
  fascisticWillToPowerPromoted canonicalIntersectionalPowerValueFolkModelBoundary ≡ false
canonicalFascisticWillToPowerPromotedFalse =
  fascisticWillToPowerPromotedIsFalse canonicalIntersectionalPowerValueFolkModelBoundary
