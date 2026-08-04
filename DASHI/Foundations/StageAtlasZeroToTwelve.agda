module DASHI.Foundations.StageAtlasZeroToTwelve where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.StageAtlasZeroToEleven as Legacy

------------------------------------------------------------------------
-- Conservative 0..12 extension.
--
-- The existing 0..11 carrier remains unchanged.  This module embeds it and
-- adds stage 12 as the relation-opened position at the new decimal scale.
-- Two coordinate systems are kept separate:
--
--   * the inherited four-position residue/revolution chart;
--   * the decimal carry address q * 10 + r.
--
-- The local j-basis unit is one fine unit.  A decimal carry contains ten
-- local j-units.  Neither notation is identified with the classical modular
-- j-invariant.
------------------------------------------------------------------------

data StageAtlasZeroToTwelve : Set where
  stage-0 stage-1 stage-2 stage-3 stage-4 stage-5 stage-6 : StageAtlasZeroToTwelve
  stage-7 stage-8 stage-9 stage-10 stage-11 stage-12 : StageAtlasZeroToTwelve

toNat : StageAtlasZeroToTwelve → Nat
toNat stage-0 = 0
toNat stage-1 = 1
toNat stage-2 = 2
toNat stage-3 = 3
toNat stage-4 = 4
toNat stage-5 = 5
toNat stage-6 = 6
toNat stage-7 = 7
toNat stage-8 = 8
toNat stage-9 = 9
toNat stage-10 = 10
toNat stage-11 = 11
toNat stage-12 = 12

embedLegacy : Legacy.StageAtlasZeroToEleven → StageAtlasZeroToTwelve
embedLegacy Legacy.atlas-0 = stage-0
embedLegacy Legacy.atlas-1 = stage-1
embedLegacy Legacy.atlas-2 = stage-2
embedLegacy Legacy.atlas-3 = stage-3
embedLegacy Legacy.atlas-4 = stage-4
embedLegacy Legacy.atlas-5 = stage-5
embedLegacy Legacy.atlas-6 = stage-6
embedLegacy Legacy.atlas-7 = stage-7
embedLegacy Legacy.atlas-8 = stage-8
embedLegacy Legacy.atlas-9 = stage-9
embedLegacy Legacy.atlas-10 = stage-10
embedLegacy Legacy.atlas-11 = stage-11

legacyEmbeddingPreservesIndex :
  ∀ stage → toNat (embedLegacy stage) ≡ Legacy.toNat stage
legacyEmbeddingPreservesIndex Legacy.atlas-0 = refl
legacyEmbeddingPreservesIndex Legacy.atlas-1 = refl
legacyEmbeddingPreservesIndex Legacy.atlas-2 = refl
legacyEmbeddingPreservesIndex Legacy.atlas-3 = refl
legacyEmbeddingPreservesIndex Legacy.atlas-4 = refl
legacyEmbeddingPreservesIndex Legacy.atlas-5 = refl
legacyEmbeddingPreservesIndex Legacy.atlas-6 = refl
legacyEmbeddingPreservesIndex Legacy.atlas-7 = refl
legacyEmbeddingPreservesIndex Legacy.atlas-8 = refl
legacyEmbeddingPreservesIndex Legacy.atlas-9 = refl
legacyEmbeddingPreservesIndex Legacy.atlas-10 = refl
legacyEmbeddingPreservesIndex Legacy.atlas-11 = refl

------------------------------------------------------------------------
-- Decimal j-scale addresses.
------------------------------------------------------------------------

localJUnit : Nat
localJUnit = 1

decimalCarryUnit : Nat
decimalCarryUnit = 10

record JScaleAddress : Set where
  field
    coarseJUnits : Nat
    localOffset : Nat
    globalIndex : Nat
    decomposition :
      decimalCarryUnit * coarseJUnits + localOffset ≡ globalIndex

jAddress : StageAtlasZeroToTwelve → JScaleAddress
jAddress stage-0 = record { coarseJUnits = 0 ; localOffset = 0 ; globalIndex = 0 ; decomposition = refl }
jAddress stage-1 = record { coarseJUnits = 0 ; localOffset = 1 ; globalIndex = 1 ; decomposition = refl }
jAddress stage-2 = record { coarseJUnits = 0 ; localOffset = 2 ; globalIndex = 2 ; decomposition = refl }
jAddress stage-3 = record { coarseJUnits = 0 ; localOffset = 3 ; globalIndex = 3 ; decomposition = refl }
jAddress stage-4 = record { coarseJUnits = 0 ; localOffset = 4 ; globalIndex = 4 ; decomposition = refl }
jAddress stage-5 = record { coarseJUnits = 0 ; localOffset = 5 ; globalIndex = 5 ; decomposition = refl }
jAddress stage-6 = record { coarseJUnits = 0 ; localOffset = 6 ; globalIndex = 6 ; decomposition = refl }
jAddress stage-7 = record { coarseJUnits = 0 ; localOffset = 7 ; globalIndex = 7 ; decomposition = refl }
jAddress stage-8 = record { coarseJUnits = 0 ; localOffset = 8 ; globalIndex = 8 ; decomposition = refl }
jAddress stage-9 = record { coarseJUnits = 0 ; localOffset = 9 ; globalIndex = 9 ; decomposition = refl }
jAddress stage-10 = record { coarseJUnits = 1 ; localOffset = 0 ; globalIndex = 10 ; decomposition = refl }
jAddress stage-11 = record { coarseJUnits = 1 ; localOffset = 1 ; globalIndex = 11 ; decomposition = refl }
jAddress stage-12 = record { coarseJUnits = 1 ; localOffset = 2 ; globalIndex = 12 ; decomposition = refl }

stage10IsOneJ :
  JScaleAddress.globalIndex (jAddress stage-10) ≡ decimalCarryUnit
stage10IsOneJ = refl

stage11IsOneJPlusOne :
  decimalCarryUnit + localJUnit ≡ JScaleAddress.globalIndex (jAddress stage-11)
stage11IsOneJPlusOne = refl

stage12IsOneJPlusTwo :
  decimalCarryUnit + 2 * localJUnit ≡ JScaleAddress.globalIndex (jAddress stage-12)
stage12IsOneJPlusTwo = refl

------------------------------------------------------------------------
-- Recursive local roles.  10, 11 and 12 replay root, unit and relation at a
-- new place-value scale without claiming that all semantics recursively copy.
------------------------------------------------------------------------

data RecursiveStageRole : Set where
  rootAtScale : RecursiveStageRole
  unitAtScale : RecursiveStageRole
  relationOpenedAtScale : RecursiveStageRole
  interiorStage : RecursiveStageRole

recursiveRole : StageAtlasZeroToTwelve → RecursiveStageRole
recursiveRole stage-0 = rootAtScale
recursiveRole stage-1 = unitAtScale
recursiveRole stage-2 = relationOpenedAtScale
recursiveRole stage-3 = interiorStage
recursiveRole stage-4 = interiorStage
recursiveRole stage-5 = interiorStage
recursiveRole stage-6 = interiorStage
recursiveRole stage-7 = interiorStage
recursiveRole stage-8 = interiorStage
recursiveRole stage-9 = interiorStage
recursiveRole stage-10 = rootAtScale
recursiveRole stage-11 = unitAtScale
recursiveRole stage-12 = relationOpenedAtScale

stage12OpensRelationAtNewScale :
  recursiveRole stage-12 ≡ relationOpenedAtScale
stage12OpensRelationAtNewScale = refl

canonicalStagesZeroToTwelve : List StageAtlasZeroToTwelve
canonicalStagesZeroToTwelve =
  stage-0 ∷ stage-1 ∷ stage-2 ∷ stage-3 ∷ stage-4 ∷ stage-5 ∷
  stage-6 ∷ stage-7 ∷ stage-8 ∷ stage-9 ∷ stage-10 ∷ stage-11 ∷
  stage-12 ∷ []

stageCount : ∀ {A : Set} → List A → Nat
stageCount [] = 0
stageCount (_ ∷ stages) = 1 + stageCount stages

canonicalStageCount : Nat
canonicalStageCount = stageCount canonicalStagesZeroToTwelve

record StageZeroToTwelveAuthorityBoundary : Set where
  field
    legacyZeroToElevenPreserved : Bool
    stageTwelveRelationAtNewScale : Bool
    stageTwelveIsMaximumClaimed : Bool
    localJUnitEqualsModularJInvariantClaimed : Bool
    numeralAlonePromotesPsychologicalMeaning : Bool
    numeralAlonePromotesPoliticalMeaning : Bool
    stageTwelveClinicalOutcomeClaimed : Bool
    boundaryNote : String

canonicalStageZeroToTwelveAuthorityBoundary :
  StageZeroToTwelveAuthorityBoundary
canonicalStageZeroToTwelveAuthorityBoundary = record
  { legacyZeroToElevenPreserved = true
  ; stageTwelveRelationAtNewScale = true
  ; stageTwelveIsMaximumClaimed = false
  ; localJUnitEqualsModularJInvariantClaimed = false
  ; numeralAlonePromotesPsychologicalMeaning = false
  ; numeralAlonePromotesPoliticalMeaning = false
  ; stageTwelveClinicalOutcomeClaimed = false
  ; boundaryNote =
      "0..12 extends the guarded atlas by place-value recursion: local j is the unit 1, 10j is the carried decimal bundle, 11j = 10j + j, and 12j = 10j + 2j. The modular j-function remains a separate sourced bridge."
  }
