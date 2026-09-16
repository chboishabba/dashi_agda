module DASHI.Philosophy.PlatoSymposiumPhilosophyBridgeRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Philosophy.PlatoSymposiumPhilosophyBridgeExact as Bridge

rightOpinionIsNotCollapsedIntoIgnorance :
  Bridge.rightOpinionEqualsIgnorance
    Bridge.canonicalPlatoSymposiumPhilosophyBoundary ≡ false
rightOpinionIsNotCollapsedIntoIgnorance = refl

pluralSpeechDoesNotGuaranteeReconciliation :
  Bridge.dialogueGuaranteesReconciliation
    Bridge.canonicalPlatoSymposiumPhilosophyBoundary ≡ false
pluralSpeechDoesNotGuaranteeReconciliation = refl

complementarityDoesNotPayRelationalAdequacy :
  Bridge.complementarityImpliesRelationalAdequacy
    Bridge.canonicalPlatoSymposiumPhilosophyBoundary ≡ false
complementarityDoesNotPayRelationalAdequacy = refl

surfaceDoesNotDetermineInteriorSignificance :
  Bridge.surfaceAppearanceDeterminesInteriorSignificance
    Bridge.canonicalPlatoSymposiumPhilosophyBoundary ≡ false
surfaceDoesNotDetermineInteriorSignificance = refl

sameAscentCarrierDoesNotMeanSameSemantics :
  Bridge.sameAscentCarrierMeansSameSemantics
    Bridge.canonicalPlatoSymposiumPhilosophyBoundary ≡ false
sameAscentCarrierDoesNotMeanSameSemantics = refl

rulerRoleDoesNotDetermineServiceOrientation :
  Bridge.roleAuthorityDeterminesServiceOrientation
    Bridge.canonicalPlatoSymposiumPhilosophyBoundary ≡ false
rulerRoleDoesNotDetermineServiceOrientation = refl

jmdSourceDoesNotOwnDashiNonfactorability :
  Bridge.jmdLeanOwnsDashiFactorisationTheorems
    Bridge.canonicalPlatoSymposiumPhilosophyBoundary ≡ false
jmdSourceDoesNotOwnDashiNonfactorability = refl

sourceAtlasRemainsParent :
  Bridge.jmdSourceAtlasRetained ≡ true
sourceAtlasRemainsParent = refl
