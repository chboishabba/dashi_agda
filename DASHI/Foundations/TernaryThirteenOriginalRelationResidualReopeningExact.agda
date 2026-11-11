module DASHI.Foundations.TernaryThirteenOriginalRelationResidualReopeningExact where

------------------------------------------------------------------------
-- H1.01 / H2.01: actual 144-cell original relational field
-- = 13-coordinate SOURCE OBSERVATION + 131 unobserved cells.
--
-- This is a pointwise, fully constructive exact residual reopening.
-- The residual is itself a 144-address function *forced neutral*
-- on the 13 selected addresses. Thus it contains precisely the
-- remaining independent 131 ordered relation values, not a
-- disguised entire source field and not a fabricated group quotient.
--
-- We explicitly enumerate all 144 source addresses for the inverse
-- proof, avoiding functional extensionality and not assuming a
-- function equality from pointwise equality.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact as Original
import DASHI.Foundations.TernaryThirteenOriginalRelational144NonIdentificationExact as Boundary
import DASHI.Foundations.TernaryThirteenOriginalAxisValuationBridgeExact as Codec
import DASHI.Foundations.TernaryThirteenFibreSplitExact as Word
import Base369 as Base

UnobservedResidual : Set
UnobservedResidual = Original.StageRelationField

-- 12 diagonal cells and (0,1) are already retained by the source
-- 13-code; their residual values are normalized to neutral.
maskUnobserved :
  Original.StageRelationField → UnobservedResidual
maskUnobserved field (Atlas.atlas-0 , Atlas.atlas-0) = Base.tri-mid
maskUnobserved field (Atlas.atlas-1 , Atlas.atlas-1) = Base.tri-mid
maskUnobserved field (Atlas.atlas-2 , Atlas.atlas-2) = Base.tri-mid
maskUnobserved field (Atlas.atlas-3 , Atlas.atlas-3) = Base.tri-mid
maskUnobserved field (Atlas.atlas-4 , Atlas.atlas-4) = Base.tri-mid
maskUnobserved field (Atlas.atlas-5 , Atlas.atlas-5) = Base.tri-mid
maskUnobserved field (Atlas.atlas-6 , Atlas.atlas-6) = Base.tri-mid
maskUnobserved field (Atlas.atlas-7 , Atlas.atlas-7) = Base.tri-mid
maskUnobserved field (Atlas.atlas-8 , Atlas.atlas-8) = Base.tri-mid
maskUnobserved field (Atlas.atlas-9 , Atlas.atlas-9) = Base.tri-mid
maskUnobserved field (Atlas.atlas-10 , Atlas.atlas-10) = Base.tri-mid
maskUnobserved field (Atlas.atlas-11 , Atlas.atlas-11) = Base.tri-mid
maskUnobserved field (Atlas.atlas-0 , Atlas.atlas-1) = Base.tri-mid
maskUnobserved field cell = field cell

-- Reopen the source field: decode observed diagonal and central
-- cells from the 13-code; use the masked residual elsewhere.
reopenRelation :
  Word.TritWord 13 →
  UnobservedResidual →
  Original.StageRelationField
reopenRelation code residual (Atlas.atlas-0 , Atlas.atlas-0) =
  proj₁ (Codec.thirteenToSourceCentral code) Atlas.atlas-0
reopenRelation code residual (Atlas.atlas-1 , Atlas.atlas-1) =
  proj₁ (Codec.thirteenToSourceCentral code) Atlas.atlas-1
reopenRelation code residual (Atlas.atlas-2 , Atlas.atlas-2) =
  proj₁ (Codec.thirteenToSourceCentral code) Atlas.atlas-2
reopenRelation code residual (Atlas.atlas-3 , Atlas.atlas-3) =
  proj₁ (Codec.thirteenToSourceCentral code) Atlas.atlas-3
reopenRelation code residual (Atlas.atlas-4 , Atlas.atlas-4) =
  proj₁ (Codec.thirteenToSourceCentral code) Atlas.atlas-4
reopenRelation code residual (Atlas.atlas-5 , Atlas.atlas-5) =
  proj₁ (Codec.thirteenToSourceCentral code) Atlas.atlas-5
reopenRelation code residual (Atlas.atlas-6 , Atlas.atlas-6) =
  proj₁ (Codec.thirteenToSourceCentral code) Atlas.atlas-6
reopenRelation code residual (Atlas.atlas-7 , Atlas.atlas-7) =
  proj₁ (Codec.thirteenToSourceCentral code) Atlas.atlas-7
reopenRelation code residual (Atlas.atlas-8 , Atlas.atlas-8) =
  proj₁ (Codec.thirteenToSourceCentral code) Atlas.atlas-8
reopenRelation code residual (Atlas.atlas-9 , Atlas.atlas-9) =
  proj₁ (Codec.thirteenToSourceCentral code) Atlas.atlas-9
reopenRelation code residual (Atlas.atlas-10 , Atlas.atlas-10) =
  proj₁ (Codec.thirteenToSourceCentral code) Atlas.atlas-10
reopenRelation code residual (Atlas.atlas-11 , Atlas.atlas-11) =
  proj₁ (Codec.thirteenToSourceCentral code) Atlas.atlas-11
reopenRelation code residual (Atlas.atlas-0 , Atlas.atlas-1) =
  proj₂ (Codec.thirteenToSourceCentral code)
reopenRelation code residual cell = residual cell

-- Full cell-by-cell reconstruction, not merely a code section.
reopenExactlyPointwise :
  (field : Original.StageRelationField) →
  (cell : Original.StageRelation144) →
  reopenRelation (Boundary.relationToThirteen field)
    (maskUnobserved field) cell ≡ field cell
reopenExactlyPointwise field (Atlas.atlas-0 , Atlas.atlas-0) =
  Codec.valuationPointwiseRoundTrip
    (Original.diagonalObservation field) Atlas.atlas-0
reopenExactlyPointwise field (Atlas.atlas-0 , Atlas.atlas-1) =
  Codec.toFromSource (Boundary.chosenOriginalCentralCell field)
reopenExactlyPointwise field (Atlas.atlas-0 , Atlas.atlas-2) =
  refl
reopenExactlyPointwise field (Atlas.atlas-0 , Atlas.atlas-3) =
  refl
reopenExactlyPointwise field (Atlas.atlas-0 , Atlas.atlas-4) =
  refl
reopenExactlyPointwise field (Atlas.atlas-0 , Atlas.atlas-5) =
  refl
reopenExactlyPointwise field (Atlas.atlas-0 , Atlas.atlas-6) =
  refl
reopenExactlyPointwise field (Atlas.atlas-0 , Atlas.atlas-7) =
  refl
reopenExactlyPointwise field (Atlas.atlas-0 , Atlas.atlas-8) =
  refl
reopenExactlyPointwise field (Atlas.atlas-0 , Atlas.atlas-9) =
  refl
reopenExactlyPointwise field (Atlas.atlas-0 , Atlas.atlas-10) =
  refl
reopenExactlyPointwise field (Atlas.atlas-0 , Atlas.atlas-11) =
  refl
reopenExactlyPointwise field (Atlas.atlas-1 , Atlas.atlas-0) =
  refl
reopenExactlyPointwise field (Atlas.atlas-1 , Atlas.atlas-1) =
  Codec.valuationPointwiseRoundTrip
    (Original.diagonalObservation field) Atlas.atlas-1
reopenExactlyPointwise field (Atlas.atlas-1 , Atlas.atlas-2) =
  refl
reopenExactlyPointwise field (Atlas.atlas-1 , Atlas.atlas-3) =
  refl
reopenExactlyPointwise field (Atlas.atlas-1 , Atlas.atlas-4) =
  refl
reopenExactlyPointwise field (Atlas.atlas-1 , Atlas.atlas-5) =
  refl
reopenExactlyPointwise field (Atlas.atlas-1 , Atlas.atlas-6) =
  refl
reopenExactlyPointwise field (Atlas.atlas-1 , Atlas.atlas-7) =
  refl
reopenExactlyPointwise field (Atlas.atlas-1 , Atlas.atlas-8) =
  refl
reopenExactlyPointwise field (Atlas.atlas-1 , Atlas.atlas-9) =
  refl
reopenExactlyPointwise field (Atlas.atlas-1 , Atlas.atlas-10) =
  refl
reopenExactlyPointwise field (Atlas.atlas-1 , Atlas.atlas-11) =
  refl
reopenExactlyPointwise field (Atlas.atlas-2 , Atlas.atlas-0) =
  refl
reopenExactlyPointwise field (Atlas.atlas-2 , Atlas.atlas-1) =
  refl
reopenExactlyPointwise field (Atlas.atlas-2 , Atlas.atlas-2) =
  Codec.valuationPointwiseRoundTrip
    (Original.diagonalObservation field) Atlas.atlas-2
reopenExactlyPointwise field (Atlas.atlas-2 , Atlas.atlas-3) =
  refl
reopenExactlyPointwise field (Atlas.atlas-2 , Atlas.atlas-4) =
  refl
reopenExactlyPointwise field (Atlas.atlas-2 , Atlas.atlas-5) =
  refl
reopenExactlyPointwise field (Atlas.atlas-2 , Atlas.atlas-6) =
  refl
reopenExactlyPointwise field (Atlas.atlas-2 , Atlas.atlas-7) =
  refl
reopenExactlyPointwise field (Atlas.atlas-2 , Atlas.atlas-8) =
  refl
reopenExactlyPointwise field (Atlas.atlas-2 , Atlas.atlas-9) =
  refl
reopenExactlyPointwise field (Atlas.atlas-2 , Atlas.atlas-10) =
  refl
reopenExactlyPointwise field (Atlas.atlas-2 , Atlas.atlas-11) =
  refl
reopenExactlyPointwise field (Atlas.atlas-3 , Atlas.atlas-0) =
  refl
reopenExactlyPointwise field (Atlas.atlas-3 , Atlas.atlas-1) =
  refl
reopenExactlyPointwise field (Atlas.atlas-3 , Atlas.atlas-2) =
  refl
reopenExactlyPointwise field (Atlas.atlas-3 , Atlas.atlas-3) =
  Codec.valuationPointwiseRoundTrip
    (Original.diagonalObservation field) Atlas.atlas-3
reopenExactlyPointwise field (Atlas.atlas-3 , Atlas.atlas-4) =
  refl
reopenExactlyPointwise field (Atlas.atlas-3 , Atlas.atlas-5) =
  refl
reopenExactlyPointwise field (Atlas.atlas-3 , Atlas.atlas-6) =
  refl
reopenExactlyPointwise field (Atlas.atlas-3 , Atlas.atlas-7) =
  refl
reopenExactlyPointwise field (Atlas.atlas-3 , Atlas.atlas-8) =
  refl
reopenExactlyPointwise field (Atlas.atlas-3 , Atlas.atlas-9) =
  refl
reopenExactlyPointwise field (Atlas.atlas-3 , Atlas.atlas-10) =
  refl
reopenExactlyPointwise field (Atlas.atlas-3 , Atlas.atlas-11) =
  refl
reopenExactlyPointwise field (Atlas.atlas-4 , Atlas.atlas-0) =
  refl
reopenExactlyPointwise field (Atlas.atlas-4 , Atlas.atlas-1) =
  refl
reopenExactlyPointwise field (Atlas.atlas-4 , Atlas.atlas-2) =
  refl
reopenExactlyPointwise field (Atlas.atlas-4 , Atlas.atlas-3) =
  refl
reopenExactlyPointwise field (Atlas.atlas-4 , Atlas.atlas-4) =
  Codec.valuationPointwiseRoundTrip
    (Original.diagonalObservation field) Atlas.atlas-4
reopenExactlyPointwise field (Atlas.atlas-4 , Atlas.atlas-5) =
  refl
reopenExactlyPointwise field (Atlas.atlas-4 , Atlas.atlas-6) =
  refl
reopenExactlyPointwise field (Atlas.atlas-4 , Atlas.atlas-7) =
  refl
reopenExactlyPointwise field (Atlas.atlas-4 , Atlas.atlas-8) =
  refl
reopenExactlyPointwise field (Atlas.atlas-4 , Atlas.atlas-9) =
  refl
reopenExactlyPointwise field (Atlas.atlas-4 , Atlas.atlas-10) =
  refl
reopenExactlyPointwise field (Atlas.atlas-4 , Atlas.atlas-11) =
  refl
reopenExactlyPointwise field (Atlas.atlas-5 , Atlas.atlas-0) =
  refl
reopenExactlyPointwise field (Atlas.atlas-5 , Atlas.atlas-1) =
  refl
reopenExactlyPointwise field (Atlas.atlas-5 , Atlas.atlas-2) =
  refl
reopenExactlyPointwise field (Atlas.atlas-5 , Atlas.atlas-3) =
  refl
reopenExactlyPointwise field (Atlas.atlas-5 , Atlas.atlas-4) =
  refl
reopenExactlyPointwise field (Atlas.atlas-5 , Atlas.atlas-5) =
  Codec.valuationPointwiseRoundTrip
    (Original.diagonalObservation field) Atlas.atlas-5
reopenExactlyPointwise field (Atlas.atlas-5 , Atlas.atlas-6) =
  refl
reopenExactlyPointwise field (Atlas.atlas-5 , Atlas.atlas-7) =
  refl
reopenExactlyPointwise field (Atlas.atlas-5 , Atlas.atlas-8) =
  refl
reopenExactlyPointwise field (Atlas.atlas-5 , Atlas.atlas-9) =
  refl
reopenExactlyPointwise field (Atlas.atlas-5 , Atlas.atlas-10) =
  refl
reopenExactlyPointwise field (Atlas.atlas-5 , Atlas.atlas-11) =
  refl
reopenExactlyPointwise field (Atlas.atlas-6 , Atlas.atlas-0) =
  refl
reopenExactlyPointwise field (Atlas.atlas-6 , Atlas.atlas-1) =
  refl
reopenExactlyPointwise field (Atlas.atlas-6 , Atlas.atlas-2) =
  refl
reopenExactlyPointwise field (Atlas.atlas-6 , Atlas.atlas-3) =
  refl
reopenExactlyPointwise field (Atlas.atlas-6 , Atlas.atlas-4) =
  refl
reopenExactlyPointwise field (Atlas.atlas-6 , Atlas.atlas-5) =
  refl
reopenExactlyPointwise field (Atlas.atlas-6 , Atlas.atlas-6) =
  Codec.valuationPointwiseRoundTrip
    (Original.diagonalObservation field) Atlas.atlas-6
reopenExactlyPointwise field (Atlas.atlas-6 , Atlas.atlas-7) =
  refl
reopenExactlyPointwise field (Atlas.atlas-6 , Atlas.atlas-8) =
  refl
reopenExactlyPointwise field (Atlas.atlas-6 , Atlas.atlas-9) =
  refl
reopenExactlyPointwise field (Atlas.atlas-6 , Atlas.atlas-10) =
  refl
reopenExactlyPointwise field (Atlas.atlas-6 , Atlas.atlas-11) =
  refl
reopenExactlyPointwise field (Atlas.atlas-7 , Atlas.atlas-0) =
  refl
reopenExactlyPointwise field (Atlas.atlas-7 , Atlas.atlas-1) =
  refl
reopenExactlyPointwise field (Atlas.atlas-7 , Atlas.atlas-2) =
  refl
reopenExactlyPointwise field (Atlas.atlas-7 , Atlas.atlas-3) =
  refl
reopenExactlyPointwise field (Atlas.atlas-7 , Atlas.atlas-4) =
  refl
reopenExactlyPointwise field (Atlas.atlas-7 , Atlas.atlas-5) =
  refl
reopenExactlyPointwise field (Atlas.atlas-7 , Atlas.atlas-6) =
  refl
reopenExactlyPointwise field (Atlas.atlas-7 , Atlas.atlas-7) =
  Codec.valuationPointwiseRoundTrip
    (Original.diagonalObservation field) Atlas.atlas-7
reopenExactlyPointwise field (Atlas.atlas-7 , Atlas.atlas-8) =
  refl
reopenExactlyPointwise field (Atlas.atlas-7 , Atlas.atlas-9) =
  refl
reopenExactlyPointwise field (Atlas.atlas-7 , Atlas.atlas-10) =
  refl
reopenExactlyPointwise field (Atlas.atlas-7 , Atlas.atlas-11) =
  refl
reopenExactlyPointwise field (Atlas.atlas-8 , Atlas.atlas-0) =
  refl
reopenExactlyPointwise field (Atlas.atlas-8 , Atlas.atlas-1) =
  refl
reopenExactlyPointwise field (Atlas.atlas-8 , Atlas.atlas-2) =
  refl
reopenExactlyPointwise field (Atlas.atlas-8 , Atlas.atlas-3) =
  refl
reopenExactlyPointwise field (Atlas.atlas-8 , Atlas.atlas-4) =
  refl
reopenExactlyPointwise field (Atlas.atlas-8 , Atlas.atlas-5) =
  refl
reopenExactlyPointwise field (Atlas.atlas-8 , Atlas.atlas-6) =
  refl
reopenExactlyPointwise field (Atlas.atlas-8 , Atlas.atlas-7) =
  refl
reopenExactlyPointwise field (Atlas.atlas-8 , Atlas.atlas-8) =
  Codec.valuationPointwiseRoundTrip
    (Original.diagonalObservation field) Atlas.atlas-8
reopenExactlyPointwise field (Atlas.atlas-8 , Atlas.atlas-9) =
  refl
reopenExactlyPointwise field (Atlas.atlas-8 , Atlas.atlas-10) =
  refl
reopenExactlyPointwise field (Atlas.atlas-8 , Atlas.atlas-11) =
  refl
reopenExactlyPointwise field (Atlas.atlas-9 , Atlas.atlas-0) =
  refl
reopenExactlyPointwise field (Atlas.atlas-9 , Atlas.atlas-1) =
  refl
reopenExactlyPointwise field (Atlas.atlas-9 , Atlas.atlas-2) =
  refl
reopenExactlyPointwise field (Atlas.atlas-9 , Atlas.atlas-3) =
  refl
reopenExactlyPointwise field (Atlas.atlas-9 , Atlas.atlas-4) =
  refl
reopenExactlyPointwise field (Atlas.atlas-9 , Atlas.atlas-5) =
  refl
reopenExactlyPointwise field (Atlas.atlas-9 , Atlas.atlas-6) =
  refl
reopenExactlyPointwise field (Atlas.atlas-9 , Atlas.atlas-7) =
  refl
reopenExactlyPointwise field (Atlas.atlas-9 , Atlas.atlas-8) =
  refl
reopenExactlyPointwise field (Atlas.atlas-9 , Atlas.atlas-9) =
  Codec.valuationPointwiseRoundTrip
    (Original.diagonalObservation field) Atlas.atlas-9
reopenExactlyPointwise field (Atlas.atlas-9 , Atlas.atlas-10) =
  refl
reopenExactlyPointwise field (Atlas.atlas-9 , Atlas.atlas-11) =
  refl
reopenExactlyPointwise field (Atlas.atlas-10 , Atlas.atlas-0) =
  refl
reopenExactlyPointwise field (Atlas.atlas-10 , Atlas.atlas-1) =
  refl
reopenExactlyPointwise field (Atlas.atlas-10 , Atlas.atlas-2) =
  refl
reopenExactlyPointwise field (Atlas.atlas-10 , Atlas.atlas-3) =
  refl
reopenExactlyPointwise field (Atlas.atlas-10 , Atlas.atlas-4) =
  refl
reopenExactlyPointwise field (Atlas.atlas-10 , Atlas.atlas-5) =
  refl
reopenExactlyPointwise field (Atlas.atlas-10 , Atlas.atlas-6) =
  refl
reopenExactlyPointwise field (Atlas.atlas-10 , Atlas.atlas-7) =
  refl
reopenExactlyPointwise field (Atlas.atlas-10 , Atlas.atlas-8) =
  refl
reopenExactlyPointwise field (Atlas.atlas-10 , Atlas.atlas-9) =
  refl
reopenExactlyPointwise field (Atlas.atlas-10 , Atlas.atlas-10) =
  Codec.valuationPointwiseRoundTrip
    (Original.diagonalObservation field) Atlas.atlas-10
reopenExactlyPointwise field (Atlas.atlas-10 , Atlas.atlas-11) =
  refl
reopenExactlyPointwise field (Atlas.atlas-11 , Atlas.atlas-0) =
  refl
reopenExactlyPointwise field (Atlas.atlas-11 , Atlas.atlas-1) =
  refl
reopenExactlyPointwise field (Atlas.atlas-11 , Atlas.atlas-2) =
  refl
reopenExactlyPointwise field (Atlas.atlas-11 , Atlas.atlas-3) =
  refl
reopenExactlyPointwise field (Atlas.atlas-11 , Atlas.atlas-4) =
  refl
reopenExactlyPointwise field (Atlas.atlas-11 , Atlas.atlas-5) =
  refl
reopenExactlyPointwise field (Atlas.atlas-11 , Atlas.atlas-6) =
  refl
reopenExactlyPointwise field (Atlas.atlas-11 , Atlas.atlas-7) =
  refl
reopenExactlyPointwise field (Atlas.atlas-11 , Atlas.atlas-8) =
  refl
reopenExactlyPointwise field (Atlas.atlas-11 , Atlas.atlas-9) =
  refl
reopenExactlyPointwise field (Atlas.atlas-11 , Atlas.atlas-10) =
  refl
reopenExactlyPointwise field (Atlas.atlas-11 , Atlas.atlas-11) =
  Codec.valuationPointwiseRoundTrip
    (Original.diagonalObservation field) Atlas.atlas-11

-- The exact source residual is guaranteed neutral where the coarse
-- thirteen-coordinate source observer already retains information.
maskedDiagonalIsNeutral0 :
  (field : Original.StageRelationField) →
  maskUnobserved field (Atlas.atlas-0 , Atlas.atlas-0) ≡ Base.tri-mid
maskedDiagonalIsNeutral0 field = refl

maskedDiagonalIsNeutral1 :
  (field : Original.StageRelationField) →
  maskUnobserved field (Atlas.atlas-1 , Atlas.atlas-1) ≡ Base.tri-mid
maskedDiagonalIsNeutral1 field = refl

maskedDiagonalIsNeutral2 :
  (field : Original.StageRelationField) →
  maskUnobserved field (Atlas.atlas-2 , Atlas.atlas-2) ≡ Base.tri-mid
maskedDiagonalIsNeutral2 field = refl

maskedDiagonalIsNeutral3 :
  (field : Original.StageRelationField) →
  maskUnobserved field (Atlas.atlas-3 , Atlas.atlas-3) ≡ Base.tri-mid
maskedDiagonalIsNeutral3 field = refl

maskedDiagonalIsNeutral4 :
  (field : Original.StageRelationField) →
  maskUnobserved field (Atlas.atlas-4 , Atlas.atlas-4) ≡ Base.tri-mid
maskedDiagonalIsNeutral4 field = refl

maskedDiagonalIsNeutral5 :
  (field : Original.StageRelationField) →
  maskUnobserved field (Atlas.atlas-5 , Atlas.atlas-5) ≡ Base.tri-mid
maskedDiagonalIsNeutral5 field = refl

maskedDiagonalIsNeutral6 :
  (field : Original.StageRelationField) →
  maskUnobserved field (Atlas.atlas-6 , Atlas.atlas-6) ≡ Base.tri-mid
maskedDiagonalIsNeutral6 field = refl

maskedDiagonalIsNeutral7 :
  (field : Original.StageRelationField) →
  maskUnobserved field (Atlas.atlas-7 , Atlas.atlas-7) ≡ Base.tri-mid
maskedDiagonalIsNeutral7 field = refl

maskedDiagonalIsNeutral8 :
  (field : Original.StageRelationField) →
  maskUnobserved field (Atlas.atlas-8 , Atlas.atlas-8) ≡ Base.tri-mid
maskedDiagonalIsNeutral8 field = refl

maskedDiagonalIsNeutral9 :
  (field : Original.StageRelationField) →
  maskUnobserved field (Atlas.atlas-9 , Atlas.atlas-9) ≡ Base.tri-mid
maskedDiagonalIsNeutral9 field = refl

maskedDiagonalIsNeutral10 :
  (field : Original.StageRelationField) →
  maskUnobserved field (Atlas.atlas-10 , Atlas.atlas-10) ≡ Base.tri-mid
maskedDiagonalIsNeutral10 field = refl

maskedDiagonalIsNeutral11 :
  (field : Original.StageRelationField) →
  maskUnobserved field (Atlas.atlas-11 , Atlas.atlas-11) ≡ Base.tri-mid
maskedDiagonalIsNeutral11 field = refl

maskedCentralIsNeutral :
  (field : Original.StageRelationField) →
  maskUnobserved field (Atlas.atlas-0 , Atlas.atlas-1) ≡ Base.tri-mid
maskedCentralIsNeutral field = refl

-- Independent reverse (1,0) relation cell is carried by the
-- residual and is therefore recovered, unlike by the 13-code alone.
residualPreservesReverseCell :
  (field : Original.StageRelationField) →
  maskUnobserved field (Atlas.atlas-1 , Atlas.atlas-0)
    ≡ Boundary.reverseCellConsumer field
residualPreservesReverseCell field = refl

reopenedReverseCell :
  (field : Original.StageRelationField) →
  reopenRelation (Boundary.relationToThirteen field)
    (maskUnobserved field) (Atlas.atlas-1 , Atlas.atlas-0)
  ≡ Boundary.reverseCellConsumer field
reopenedReverseCell field =
  reopenExactlyPointwise field (Atlas.atlas-1 , Atlas.atlas-0)

-- Formal interface for the source's pointwise exact decoding law.
-- Unlike ResidualReopening's function equality, this retains the
-- actual constructive pointwise notion of equality for original
-- StageRelationField functions, without adding funext/postulates.
record OriginalRelationPointwiseReopening : Set₁ where
  field
    coarse : Original.StageRelationField → Word.TritWord 13
    residual : Original.StageRelationField → UnobservedResidual
    reopen : Word.TritWord 13 →
      UnobservedResidual → Original.StageRelationField
    exact :
      (field : Original.StageRelationField)
      (cell : Original.StageRelation144) →
      reopen (coarse field) (residual field) cell ≡ field cell

originalRelationPointwiseReopening :
  OriginalRelationPointwiseReopening
originalRelationPointwiseReopening = record
  { coarse = Boundary.relationToThirteen
  ; residual = maskUnobserved
  ; reopen = reopenRelation
  ; exact = reopenExactlyPointwise
  }

------------------------------------------------------------------------
-- The 13-code is recovered after reopening for ANY residual, not
-- only a residual produced by maskUnobserved.
------------------------------------------------------------------------

reopenPreservesCoarseCode :
  (code : Word.TritWord 13)
  (residual : UnobservedResidual) →
  Boundary.relationToThirteen (reopenRelation code residual)
    ≡ code
reopenPreservesCoarseCode code residual =
  trans
    (Boundary.selectedRelationThirteenCodeRoundTrip
      (Codec.thirteenToSourceCentral code))
    (Codec.thirteenSourceRoundTrip code)

-- The omitted (1,0) slot separates exactly the collision that
-- the original 13-coordinate observation cannot distinguish.
differentOriginalResiduals :
  maskUnobserved Boundary.originalFlatField
  ≡ maskUnobserved Boundary.reverseCellRaised → ⊥
differentOriginalResiduals sameResidual =
  Boundary.reverseCellReallyDiffers
    (trans
      (sym (residualPreservesReverseCell Boundary.originalFlatField))
      (trans
        (cong (λ residual → residual (Atlas.atlas-1 , Atlas.atlas-0))
          sameResidual)
        (residualPreservesReverseCell Boundary.reverseCellRaised)))

-- Every source relation field is reconstructed at every addressed
-- cell from its own coarse observation and its own masked residual.
-- Conversely the coarse observation always survives reopening.
-- Together this provides the selected finite residual splitting
-- WITHOUT any chosen section being confused with a full inverse.
originalRelationRoundTripAt :
  (field : Original.StageRelationField)
  (cell : Original.StageRelation144) →
  reopenRelation (Boundary.relationToThirteen field)
    (maskUnobserved field) cell ≡ field cell
originalRelationRoundTripAt = reopenExactlyPointwise
