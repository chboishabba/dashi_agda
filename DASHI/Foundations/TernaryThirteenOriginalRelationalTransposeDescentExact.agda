module DASHI.Foundations.TernaryThirteenOriginalRelationalTransposeDescentExact where

------------------------------------------------------------------------
-- H1.01/H2.01: the ORIGINAL 144-ordered-relation transpose is a
-- concrete operation that DOES NOT descend to the 13-coordinate
-- diagonal + directed (0,1) observer alone.
--
-- Transposition exchanges the retained central (0,1) cell with
-- the omitted residual (1,0) cell. The original 13+131
-- complete observation DOES reconstruct transposition at
-- every original ordered address.
--
-- This is a dynamic/functorial obstruction, stronger than a mere
-- pair of differing source fields, and uses the actual original
-- transposeRelation rather than a fabricated operator.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact as Original
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Foundations.TernaryThirteenOriginalRelational144NonIdentificationExact as Boundary
import DASHI.Foundations.TernaryThirteenOriginalRelationResidualReopeningExact as Residual
import DASHI.Foundations.TernaryThirteenOriginalAxisValuationBridgeExact as Codec
import DASHI.Foundations.TernaryThirteenFibrePunctureExact as Puncture
import DASHI.Foundations.TernaryThirteenFibreSplitExact as Word
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import Base369 as Base

transposeCentralConsumer :
  Original.StageRelationField → Base.TriTruth
transposeCentralConsumer field =
  Boundary.chosenOriginalCentralCell (Original.transposeRelation field)

transposeCentralIsReverseCell :
  (field : Original.StageRelationField) →
  transposeCentralConsumer field
  ≡ Boundary.reverseCellConsumer field
transposeCentralIsReverseCell field = refl

transposeCentralDifferentOnOriginalCollision :
  transposeCentralConsumer Boundary.originalFlatField
  ≡ transposeCentralConsumer Boundary.reverseCellRaised → ⊥
transposeCentralDifferentOnOriginalCollision =
  Boundary.reverseCellReallyDiffers

transposedCentralNonDescent :
  Descent.ConsumerNonDescentWitness
    Boundary.relationToThirteen
    transposeCentralConsumer
transposedCentralNonDescent =
  Descent.consumerNonDescentWitness
    Boundary.originalFlatField
    Boundary.reverseCellRaised
    Boundary.originalThirteenCodeCollision
    transposeCentralDifferentOnOriginalCollision

transposeCentralCannotFactorThroughCoarse :
  Descent.FactorsThrough
    Boundary.relationToThirteen
    transposeCentralConsumer → ⊥
transposeCentralCannotFactorThroughCoarse =
  Descent.nonDescentWitnessBlocksFactorization
    transposedCentralNonDescent

-- Extract the actual central trit from an original coarse word.
decodeCentral :
  Word.TritWord 13 → Base.TriTruth
decodeCentral code =
  proj₂ (Codec.thirteenToSourceCentral code)

originalRelationCodeCentralRecovers :
  (field : Original.StageRelationField) →
  decodeCentral (Boundary.relationToThirteen field)
  ≡ Boundary.chosenOriginalCentralCell field
originalRelationCodeCentralRecovers field =
  Codec.sourceCentralRoundTripOnCentre
    (Original.diagonalObservation field ,
     Boundary.chosenOriginalCentralCell field)

-- Stronger prohibition: even constructing the COARSE WORD of
-- the transposed field from the original coarse word is impossible.
-- The contradiction is the omitted directed reverse cell.
transposeCodeCannotDescend :
  (transposedCode : Word.TritWord 13 → Word.TritWord 13) →
  ((field : Original.StageRelationField) →
    transposedCode (Boundary.relationToThirteen field)
    ≡ Boundary.relationToThirteen (Original.transposeRelation field)) →
  ⊥
transposeCodeCannotDescend transposedCode commutes =
  transposeCentralDifferentOnOriginalCollision
    (trans
      (sym (originalRelationCodeCentralRecovers
        (Original.transposeRelation Boundary.originalFlatField)))
      (trans
        (sym (cong decodeCentral
          (commutes Boundary.originalFlatField)))
        (trans
          (cong
            (λ code → decodeCentral (transposedCode code))
            Boundary.originalThirteenCodeCollision)
          (trans
            (cong decodeCentral
              (commutes Boundary.reverseCellRaised))
            (originalRelationCodeCentralRecovers
              (Original.transposeRelation Boundary.reverseCellRaised))))))

-- Exact induced transpose on the LOSSLESS original source
-- 13-code + normalized residual, with no arbitrary new state.
transposeOnFullObservation :
  Word.TritWord 13 × Residual.Residual131 →
  Word.TritWord 13 × Residual.Residual131
transposeOnFullObservation (code , rest) =
  Residual.fullRelationalObserver
    (Original.transposeRelation (Residual.reopenNormalized code rest))

-- All original field values of the transposed state are
-- reconstructed pointwise by the induced full observation.
transposeFullObservationRecoversAt :
  (field : Original.StageRelationField)
  (cell : Original.StageRelation144) →
  Residual.reopenNormalized
    (proj₁ (transposeOnFullObservation
      (Residual.fullRelationalObserver field)))
    (proj₂ (transposeOnFullObservation
      (Residual.fullRelationalObserver field)))
    cell
  ≡ Original.transposeRelation field cell
transposeFullObservationRecoversAt field cell =
  trans
    (Residual.reopenNormalizedExact
      (Original.transposeRelation
        (Residual.reopenNormalized
          (Boundary.relationToThirteen field)
          (Residual.maskToResidual131 field)))
      cell)
    (Residual.reopenNormalizedExact field
      (proj₂ cell , proj₁ cell))
