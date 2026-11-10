module DASHI.Foundations.TernaryThirteenOriginalRelational144NonIdentificationExact where

------------------------------------------------------------------------
-- H1.01 decisive SAME-SOURCE negative control.
--
-- The independently existing StageTwelve owner has the actual
-- full field StageRelation144 -> Base369.TriTruth (144 cells).
-- The newly constructed 12-axis valuation + *one* central trit
-- is NOT automatically that full relational carrier.
--
-- Even choosing one genuine off-diagonal relation cell (0,1)
-- as the centre loses the independent opposite cell (1,0).
-- An explicit pair of original 144-cell fields has exactly
-- the same 12 diagonal entries AND the same chosen (0,1)
-- central entry but different (1,0) consumers.
--
-- This is a stronger negative test than counting 3^13 vs 3^144.
-- It does not deny a separately justified quotient/subcarrier
-- with 13 independent coordinates; that selection is the unpaid
-- independent semantic H1.01 theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact as Original
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Foundations.TernaryThirteenOriginalAxisValuationBridgeExact as Codec
import DASHI.Foundations.TernaryThirteenFibreSplitExact as Word
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import Base369 as Base

-- One central cell selected FROM THE ACTUAL SOURCE RELATION field.
chosenOriginalCentralCell : Original.StageRelationField → Base.TriTruth
chosenOriginalCentralCell relation =
  Original.relationAt relation Atlas.atlas-0 Atlas.atlas-1

-- Encoding the real diagonal as twelve explicit original trits,
-- and retaining the single selected source central cell.
relationToThirteen :
  Original.StageRelationField → Word.TritWord 13
relationToThirteen relation =
  Codec.sourceCentralToThirteen
    (Original.diagonalObservation relation ,
     chosenOriginalCentralCell relation)

-- A second source field differs ONLY at the inverse ordered cell.
-- The source StageRelation144 is ORDERED, not an unordered pair.
reverseCellRaised : Original.StageRelationField
reverseCellRaised (Atlas.atlas-1 , Atlas.atlas-0) =
  Base.tri-high
reverseCellRaised _ = Base.tri-mid

originalFlatField : Original.StageRelationField
originalFlatField = Original.flatRelation

-- Evaluating the original source's 12 literal axes gives the same
-- code for both fields; no extensional equality of functions needed.
diagonalCodesAgree :
  Codec.valuationToWord
    (Original.diagonalObservation originalFlatField)
  ≡
  Codec.valuationToWord
    (Original.diagonalObservation reverseCellRaised)
diagonalCodesAgree = refl

centralCellCodesAgree :
  chosenOriginalCentralCell originalFlatField
  ≡ chosenOriginalCentralCell reverseCellRaised
centralCellCodesAgree = refl

originalThirteenCodeCollision :
  relationToThirteen originalFlatField
  ≡ relationToThirteen reverseCellRaised
originalThirteenCodeCollision = refl

-- The omitted source field is a genuine independently typed
-- 144th-cell consumer, not a synthetic 'extra information' tag.
reverseCellConsumer : Original.StageRelationField → Base.TriTruth
reverseCellConsumer relation =
  Original.relationAt relation Atlas.atlas-1 Atlas.atlas-0

reverseCellReallyDiffers :
  reverseCellConsumer originalFlatField
  ≡ reverseCellConsumer reverseCellRaised → ⊥
reverseCellReallyDiffers ()

originalRelation144NonDescent :
  Descent.ConsumerNonDescentWitness
    relationToThirteen
    reverseCellConsumer
originalRelation144NonDescent =
  Descent.consumerNonDescentWitness
    originalFlatField
    reverseCellRaised
    originalThirteenCodeCollision
    reverseCellReallyDiffers

-- No consumer of only the chosen 13-coordinate code can
-- reconstruct all original 144-cell relation observations.
sourceThirteenCannotDetermineReverseCell :
  Descent.ConsumerSufficient
    relationToThirteen
    reverseCellConsumer → ⊥
sourceThirteenCannotDetermineReverseCell =
  Descent.nonDescentWitnessBlocksSufficiency
    originalRelation144NonDescent

sourceThirteenCannotFactorReverseCell :
  Descent.FactorsThrough
    relationToThirteen reverseCellConsumer → ⊥
sourceThirteenCannotFactorReverseCell =
  Descent.nonDescentWitnessBlocksFactorization
    originalRelation144NonDescent

-- By a very small abstract proof, a putative left inverse of the
-- source 13-coordinate code would contradict the explicit pair.
sourceThirteenCannotBeLosslessLeftInverse :
  (reconstruct :
    Word.TritWord 13 → Original.StageRelationField) →
  ((field : Original.StageRelationField) →
    (cell : Original.StageRelation144) →
    reconstruct (relationToThirteen field) cell ≡ field cell) →
  ⊥
sourceThirteenCannotBeLosslessLeftInverse reconstruct recover =
  reverseCellReallyDiffers
    (trans
      (sym (recover originalFlatField
        (Atlas.atlas-1 , Atlas.atlas-0)))
      (trans
        (cong
          (λ code →
            reconstruct code (Atlas.atlas-1 , Atlas.atlas-0))
          originalThirteenCodeCollision)
        (recover reverseCellRaised
          (Atlas.atlas-1 , Atlas.atlas-0))))

-- The source is still allowed to choose a *restricted* 13-parameter
-- relational subcarrier; this theorem simply forbids declaring
-- the entire original 144-field to be losslessly encoded by its
-- diagonal and a single off-diagonal centre.
