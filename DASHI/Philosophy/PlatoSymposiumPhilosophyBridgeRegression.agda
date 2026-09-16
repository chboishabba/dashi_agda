module DASHI.Philosophy.PlatoSymposiumPhilosophyBridgeRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Philosophy.PlatoSymposiumPhilosophyBridgeExact as Bridge

jmdOwnershipRemainsExplicit :
  Bridge.jmdOwnershipRetained
    Bridge.canonicalPlatoSymposiumPhilosophyBoundary ≡ true
jmdOwnershipRemainsExplicit = refl

leanSourceDoesNotBecomeAgdaProof :
  Bridge.leanTheoremsImportedAsAgdaProofs
    Bridge.canonicalPlatoSymposiumPhilosophyBoundary ≡ false
leanSourceDoesNotBecomeAgdaProof = refl

rightOpinionKeepsNonBinaryRoom :
  Bridge.rightOpinionRequiresNonBinaryEpistemicRoom
    Bridge.canonicalPlatoSymposiumPhilosophyBoundary ≡ true
rightOpinionKeepsNonBinaryRoom = refl

pluralSpeechMayRetainContradiction :
  Bridge.contradictionMayRemainWithoutForcedConsensus
    Bridge.canonicalPlatoSymposiumPhilosophyBoundary ≡ true
pluralSpeechMayRetainContradiction = refl

complementarityDoesNotPayRelationalAdequacy :
  Bridge.aristophanicHalfDefinesRelationalAdequacy
    Bridge.canonicalPlatoSymposiumPhilosophyBoundary ≡ false
complementarityDoesNotPayRelationalAdequacy = refl

surfaceDoesNotDetermineInteriorSignificance :
  Bridge.alcibiadesExteriorDeterminesInterior
    Bridge.canonicalPlatoSymposiumPhilosophyBoundary ≡ false
surfaceDoesNotDetermineInteriorSignificance = refl

sameShapeRequiresSemanticBridge :
  Bridge.sharedShapeRequiresSeparateSemanticBridge
    Bridge.canonicalPlatoSymposiumPhilosophyBoundary ≡ true
sameShapeRequiresSemanticBridge = refl

lackAloneDoesNotDefinePhilosophy :
  Bridge.lackAloneDefinesPhilosophy
    Bridge.canonicalPlatoSymposiumPhilosophyBoundary ≡ false
lackAloneDoesNotDefinePhilosophy = refl
