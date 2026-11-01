module DASHI.Physics.YangMills.BalabanBishopFullHalfBallParityChartExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- PURPOSE
-- Extend the nonnegative-half-ball interlacing theorem to a constructive
-- full-half-ball chart without assuming decidable trichotomy for Bishop reals.
-- A chart records whether the represented point is the nonnegative
-- representative itself or its negation.  Sine is transported oddly, cosine
-- evenly, and the positive representative retains the existing omitted-term
-- interlacing data.  Negative-leading sine brackets are kept orientation-aware
-- rather than being incorrectly forced into the positive-leading record.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as HalfBall
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Terms
import DASHI.Physics.YangMills.BalabanBishopSeriesParityAndLimitExact as ParityLimit
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Interlacing
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Brackets
open import DASHI.Physics.YangMills.CompactLieProofLevel

data HalfBallOrientation : Set where
  directNonnegative : HalfBallOrientation
  reflectedNegative : HalfBallOrientation

ChartRelation :
  HalfBallOrientation →
  BishopReal.ℝ → BishopReal.ℝ → Set
ChartRelation directNonnegative value representative =
  value ≡ representative
ChartRelation reflectedNegative value representative =
  value ≡ BishopReal.- representative

orientedSineValue :
  Elementary.BishopElementaryPowerSeriesData →
  HalfBallOrientation →
  BishopReal.ℝ →
  BishopReal.ℝ
orientedSineValue dataSet directNonnegative representative =
  Elementary.bishopSin dataSet representative
orientedSineValue dataSet reflectedNegative representative =
  BishopReal.- (Elementary.bishopSin dataSet representative)

record FullHalfBallParityChart
    (dataSet : Elementary.BishopElementaryPowerSeriesData)
    (value : BishopReal.ℝ) : Set₁ where
  field
    representative : BishopReal.ℝ
    orientation : HalfBallOrientation

    representativeNonnegative :
      BishopReal.NonNegative representative

    representativeInsideHalf :
      BishopReal._≤_
        (BishopReal.∣_∣ representative)
        HalfBall.bishopHalf

    valueRelation :
      ChartRelation orientation value representative

    termIdentification :
      Terms.ConcreteSineCosineTermIdentification dataSet

    parityInputs :
      ParityLimit.BishopSeriesLimitParityInputs dataSet

    chartSineValueRelation :
      BishopReal._≃_
        (Elementary.bishopSin dataSet value)
        (orientedSineValue dataSet orientation representative)

    chartCosineValueRelation :
      BishopReal._≃_
        (Elementary.bishopCos dataSet value)
        (Elementary.bishopCos dataSet representative)

open FullHalfBallParityChart public

nonnegativeHalfBallChart :
  ∀ {dataSet value} →
  Terms.ConcreteSineCosineTermIdentification dataSet →
  ParityLimit.BishopSeriesLimitParityInputs dataSet →
  BishopReal.NonNegative value →
  BishopReal._≤_ (BishopReal.∣_∣ value) HalfBall.bishopHalf →
  FullHalfBallParityChart dataSet value
nonnegativeHalfBallChart {value = value}
    identification parity nonnegative inside = record
  { representative = value
  ; orientation = directNonnegative
  ; representativeNonnegative = nonnegative
  ; representativeInsideHalf = inside
  ; valueRelation = refl
  ; termIdentification = identification
  ; parityInputs = parity
  ; chartSineValueRelation = BishopProperties.≃-refl
  ; chartCosineValueRelation = BishopProperties.≃-refl
  }

reflectedNegativeHalfBallChart :
  ∀ {dataSet representative} →
  Terms.ConcreteSineCosineTermIdentification dataSet →
  ParityLimit.BishopSeriesLimitParityInputs dataSet →
  BishopReal.NonNegative representative →
  BishopReal._≤_
    (BishopReal.∣_∣ representative)
    HalfBall.bishopHalf →
  FullHalfBallParityChart
    dataSet (BishopReal.- representative)
reflectedNegativeHalfBallChart {representative = representative}
    identification parity nonnegative inside = record
  { representative = representative
  ; orientation = reflectedNegative
  ; representativeNonnegative = nonnegative
  ; representativeInsideHalf = inside
  ; valueRelation = refl
  ; termIdentification = identification
  ; parityInputs = parity
  ; chartSineValueRelation =
      ParityLimit.bishopSinNeg parity representative
  ; chartCosineValueRelation =
      ParityLimit.bishopCosNeg parity representative
  }

representativeSineCosineInterlacing :
  ∀ {dataSet value} →
  FullHalfBallParityChart dataSet value →
  Brackets.BishopSineCosineInterlacingData
representativeSineCosineInterlacing chart =
  Interlacing.concreteSineCosineInterlacing record
    { termIdentification = termIdentification chart
    ; valueNonnegative = representativeNonnegative chart
    ; insideHalf = representativeInsideHalf chart
    }

sineValueFromRepresentative :
  ∀ {dataSet value} →
  (chart : FullHalfBallParityChart dataSet value) →
  BishopReal._≃_
    (Elementary.bishopSin dataSet value)
    (orientedSineValue
      dataSet (orientation chart) (representative chart))
sineValueFromRepresentative = chartSineValueRelation

cosineValueFromRepresentative :
  ∀ {dataSet value} →
  (chart : FullHalfBallParityChart dataSet value) →
  BishopReal._≃_
    (Elementary.bishopCos dataSet value)
    (Elementary.bishopCos dataSet (representative chart))
cosineValueFromRepresentative = chartCosineValueRelation

record OrientedFullHalfBallBrackets
    (dataSet : Elementary.BishopElementaryPowerSeriesData)
    (value : BishopReal.ℝ) : Set₁ where
  field
    chart : FullHalfBallParityChart dataSet value

    representativeInterlacing :
      Brackets.BishopSineCosineInterlacingData

    representativeInterlacingIsConcrete :
      representativeInterlacing
      ≡ representativeSineCosineInterlacing chart

    sineValueRelation :
      BishopReal._≃_
        (Elementary.bishopSin dataSet value)
        (orientedSineValue
          dataSet (orientation chart) (representative chart))

    cosineValueRelation :
      BishopReal._≃_
        (Elementary.bishopCos dataSet value)
        (Elementary.bishopCos dataSet (representative chart))

open OrientedFullHalfBallBrackets public

orientedFullHalfBallBrackets :
  ∀ {dataSet value} →
  (chart : FullHalfBallParityChart dataSet value) →
  OrientedFullHalfBallBrackets dataSet value
orientedFullHalfBallBrackets chart = record
  { chart = chart
  ; representativeInterlacing =
      representativeSineCosineInterlacing chart
  ; representativeInterlacingIsConcrete = refl
  ; sineValueRelation = sineValueFromRepresentative chart
  ; cosineValueRelation = cosineValueFromRepresentative chart
  }

fullHalfBallParityChartLevel : ProofLevel
fullHalfBallParityChartLevel = machineChecked

fullHalfBallRepresentativeInterlacingLevel : ProofLevel
fullHalfBallRepresentativeInterlacingLevel = machineChecked

constructiveSignChartSelectionLevel : ProofLevel
constructiveSignChartSelectionLevel = conditional
