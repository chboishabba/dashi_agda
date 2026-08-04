module DASHI.Foundations.StageCantorScaleRecursion where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.CantorDiagonalCore as Cantor
import DASHI.Foundations.StageAtlasZeroToTwelve as Stage

------------------------------------------------------------------------
-- A precise one-step bridge from stage carry/fresh relation to Cantorian
-- predicate non-totalisation.
--
-- Stage 10 carries an existing predicate family as one coarse object.
-- Stage 11 may index the omitted diagonal predicate as a fresh local unit.
-- Stage 12 records the relation between the old enumeration and that omitted
-- predicate.  This is a governed address interpretation, not an identity
-- between numerals and transfinite cardinals.
------------------------------------------------------------------------

record StageCantorScaleStep (A : Set) : Set₁ where
  field
    enumeration : A → Cantor.Pred A
    diagonalReceipt : Cantor.CantorDiagonalReceipt A
    receiptMatchesEnumeration :
      Cantor.CantorDiagonalReceipt.enumeration diagonalReceipt ≡ enumeration
    carriedStage : Stage.StageAtlasZeroToTwelve
    freshStage : Stage.StageAtlasZeroToTwelve
    relationStage : Stage.StageAtlasZeroToTwelve
    carriedStageIsTen : carriedStage ≡ Stage.stage-10
    freshStageIsEleven : freshStage ≡ Stage.stage-11
    relationStageIsTwelve : relationStage ≡ Stage.stage-12
    scaleInterpretationCandidateOnly : Bool
    cardinalNameAssigned : Bool
    bridgeReceipt : String

canonicalStageCantorScaleStep :
  ∀ {A : Set} (enumeration : A → Cantor.Pred A) →
  StageCantorScaleStep A
canonicalStageCantorScaleStep enumeration = record
  { enumeration = enumeration
  ; diagonalReceipt = Cantor.canonicalCantorDiagonalReceipt enumeration
  ; receiptMatchesEnumeration = refl
  ; carriedStage = Stage.stage-10
  ; freshStage = Stage.stage-11
  ; relationStage = Stage.stage-12
  ; carriedStageIsTen = refl
  ; freshStageIsEleven = refl
  ; relationStageIsTwelve = refl
  ; scaleInterpretationCandidateOnly = true
  ; cardinalNameAssigned = false
  ; bridgeReceipt =
      "10 carries an existing enumeration, 11 addresses its omitted diagonal as fresh, and 12 opens the enumeration/omission relation."
  }

stageCantorOmittedPredicateNotInImage :
  ∀ {A : Set} (enumeration : A → Cantor.Pred A) →
  Cantor.NotInImage enumeration (Cantor.Diagonal enumeration)
stageCantorOmittedPredicateNotInImage =
  Cantor.diagonalNotInImage

record StageCantorScaleAuthorityBoundary : Set where
  field
    constructiveDiagonalWitnessImported : Bool
    stageTenCanAddressCarriedFamily : Bool
    stageElevenCanAddressFreshOmission : Bool
    stageTwelveCanAddressRelation : Bool
    stageElevenEqualsAlephOne : Bool
    stageTwelveEqualsContinuum : Bool
    repeatedStagesConstructAllInfiniteCardinals : Bool
    arbitraryResidualRaisesCardinality : Bool
    boundaryNote : String

canonicalStageCantorScaleAuthorityBoundary :
  StageCantorScaleAuthorityBoundary
canonicalStageCantorScaleAuthorityBoundary = record
  { constructiveDiagonalWitnessImported = true
  ; stageTenCanAddressCarriedFamily = true
  ; stageElevenCanAddressFreshOmission = true
  ; stageTwelveCanAddressRelation = true
  ; stageElevenEqualsAlephOne = false
  ; stageTwelveEqualsContinuum = false
  ; repeatedStagesConstructAllInfiniteCardinals = false
  ; arbitraryResidualRaisesCardinality = false
  ; boundaryNote =
      "The stage bridge addresses one exact predicate-lift step; it does not identify finite stages with named transfinite cardinals or construct an unrestricted universe tower."
  }
