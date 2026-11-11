module DASHI.Foundations.TernaryThirteenOriginalRelationConsumerUniversalityExact where

------------------------------------------------------------------------
-- H1.01/H2.01: universality of the ORIGINAL 13+131 pointwise
-- relational normal form for ANY extensional consumer.
--
-- The prior owner pays 144 exact pointwise reconstruction laws.
-- This owner makes the consumer consequence precise: if the
-- consumer respects pointwise equality of original relation
-- fields, it factors CONSTRUCTIVELY through the retained 13-code
-- and normalized 131-cell residual.
--
-- No function extensionality, field equality, world-node
-- identification, arbitrary analytic object or semantic group
-- quotient is assumed. "Extensional" is explicit, never inferred.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact as Original
import DASHI.Foundations.TernaryThirteenOriginalRelationResidualReopeningExact as Residual
import DASHI.Foundations.TernaryThirteenOriginalRelational144NonIdentificationExact as Boundary
import DASHI.Foundations.TernaryThirteenFibreSplitExact as Word
import DASHI.Core.ObserverFactorizedRefinementExact as Factor
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import Base369 as Base

PointwiseEqual :
  Original.StageRelationField →
  Original.StageRelationField → Set
PointwiseEqual left right =
  (cell : Original.StageRelation144) →
  left cell ≡ right cell

record PointwiseExtensionalConsumer (Outcome : Set) : Set₁ where
  constructor pointwise-extensional-consumer
  field
    consume : Original.StageRelationField → Outcome
    respectsPointwise :
      (left right : Original.StageRelationField) →
      PointwiseEqual left right →
      consume left ≡ consume right

open PointwiseExtensionalConsumer public

-- The same input 13+131 code reopens to exactly the pointwise
-- original source field, for every actual cell.
reopenedFieldIsPointwiseOriginal :
  (field : Original.StageRelationField) →
  PointwiseEqual
    (Residual.reopenNormalized
      (Boundary.relationToThirteen field)
      (Residual.maskToResidual131 field))
    field
reopenedFieldIsPointwiseOriginal field =
  Residual.reopenNormalizedExact field

reconstructConsumer :
  {Outcome : Set} →
  PointwiseExtensionalConsumer Outcome →
  Word.TritWord 13 × Residual.Residual131 → Outcome
reconstructConsumer selected (code , residual) =
  consume selected (Residual.reopenNormalized code residual)

reconstructConsumerCommutes :
  {Outcome : Set}
  (selected : PointwiseExtensionalConsumer Outcome)
  (field : Original.StageRelationField) →
  consume selected field
  ≡ reconstructConsumer selected
      (Residual.fullRelationalObserver field)
reconstructConsumerCommutes selected field =
  sym (respectsPointwise selected
    (Residual.reopenNormalized
      (Boundary.relationToThirteen field)
      (Residual.maskToResidual131 field))
    field
    (reopenedFieldIsPointwiseOriginal field))

-- This is the ORIGINAL FactorizedRefinement owner, rather
-- than a newly invented "factorization" receipt or assertion.
everyExtensionalConsumerFactors :
  {Outcome : Set}
  (selected : PointwiseExtensionalConsumer Outcome) →
  Descent.FactorsThrough
    Residual.fullRelationalObserver
    (consume selected)
everyExtensionalConsumerFactors selected =
  Factor.factorizedRefinement
    (reconstructConsumer selected)
    (reconstructConsumerCommutes selected)

everyExtensionalConsumerIsSufficient :
  {Outcome : Set}
  (selected : PointwiseExtensionalConsumer Outcome) →
  Descent.ConsumerSufficient
    Residual.fullRelationalObserver
    (consume selected)
everyExtensionalConsumerIsSufficient selected =
  Descent.factorsThroughImpliesFibreConstant
    (everyExtensionalConsumerFactors selected)

-- Exact induced transport of ANY chosen consumer through the
-- original coarse+residual observer without requiring
-- a global equality of the 144-cell function itself.
originalFullObservationKernelControlsConsumers :
  {Outcome : Set}
  (selected : PointwiseExtensionalConsumer Outcome) →
  (left right : Original.StageRelationField) →
  Residual.fullRelationalObserver left
    ≡ Residual.fullRelationalObserver right →
  consume selected left ≡ consume selected right
originalFullObservationKernelControlsConsumers selected left right same =
  everyExtensionalConsumerIsSufficient selected left right same

-- An actual indexed original relation-cell consumer is
-- pointwise extensional, and hence a concrete instance of the
-- universal factorization rather than an informal assertion.
originalCellConsumerExtensional :
  (cell : Original.StageRelation144) →
  PointwiseExtensionalConsumer Base.TriTruth
originalCellConsumerExtensional cell =
  pointwise-extensional-consumer
    (Residual.originalRelationCellConsumer cell)
    (λ left right same → same cell)

everyOriginalCellExplicitlyFactors :
  (cell : Original.StageRelation144) →
  Descent.FactorsThrough
    Residual.fullRelationalObserver
    (Residual.originalRelationCellConsumer cell)
everyOriginalCellExplicitlyFactors cell =
  everyExtensionalConsumerFactors
    (originalCellConsumerExtensional cell)

-- The coarse-only 13-code is NOT enough, even for this
-- same original source's (1,0) cell consumer.
reverseCellStillDoesNotFactorThroughCoarse :
  Descent.FactorsThrough
    Boundary.relationToThirteen
    Boundary.reverseCellConsumer →
  ⊥
reverseCellStillDoesNotFactorThroughCoarse =
  Boundary.sourceThirteenCannotFactorReverseCell
