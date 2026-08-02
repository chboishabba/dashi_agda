module DASHI.Physics.YangMills.BalabanClayGate4SeriesLipschitzAssemblyExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Constructive termwise-to-series Lipschitz assembly.
--
-- A power-series coefficient proof naturally gives
--
--   |t_n(x)-t_n(y)| <= c_n d(x,y).
--
-- This module proves by induction that every finite partial difference is
-- bounded by the partial coefficient sum times d(x,y).  A complete ordered
-- real backend then needs only its standard order-closed limit principle to
-- pass the estimate to the series value.
------------------------------------------------------------------------

record SeriesLipschitzAlgebra (Bound : Set) : Set₁ where
  field
    zero : Bound
    add multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

    multiplyRightMonotone : ∀ {left right} distance →
      LessEqual left right →
      LessEqual (multiply left distance) (multiply right distance)

    multiplyZeroLeft : ∀ distance →
      multiply zero distance ≡ zero

    rightDistributes : ∀ left right distance →
      add (multiply left distance) (multiply right distance)
      ≡ multiply (add left right) distance

open SeriesLipschitzAlgebra public

partialSum :
  ∀ {Bound} → SeriesLipschitzAlgebra Bound →
  (Nat → Bound) → Nat → Bound
partialSum algebra sequence zero = zero algebra
partialSum algebra sequence (suc depth) =
  add algebra (sequence depth) (partialSum algebra sequence depth)

record TermwiseSeriesLipschitz
    (Point Bound : Set)
    (algebra : SeriesLipschitzAlgebra Bound) : Set₁ where
  field
    distance : Point → Point → Bound
    coefficient : Nat → Bound
    termDifference : Nat → Point → Point → Bound

    termDifferenceBound : ∀ index left right →
      LessEqual algebra
        (termDifference index left right)
        (multiply algebra (coefficient index) (distance left right))

open TermwiseSeriesLipschitz public

partialDifference :
  ∀ {Point Bound}
    {algebra : SeriesLipschitzAlgebra Bound} →
  TermwiseSeriesLipschitz Point Bound algebra →
  Nat → Point → Point → Bound
partialDifference {algebra = algebra} dataSet depth left right =
  partialSum algebra
    (λ index → termDifference dataSet index left right) depth

coefficientPartial :
  ∀ {Point Bound}
    {algebra : SeriesLipschitzAlgebra Bound} →
  TermwiseSeriesLipschitz Point Bound algebra → Nat → Bound
coefficientPartial {algebra = algebra} dataSet =
  partialSum algebra (coefficient dataSet)

partialDifferenceLipschitz :
  ∀ {Point Bound}
    {algebra : SeriesLipschitzAlgebra Bound}
    (dataSet : TermwiseSeriesLipschitz Point Bound algebra)
    depth left right →
  LessEqual algebra
    (partialDifference dataSet depth left right)
    (multiply algebra
      (coefficientPartial dataSet depth)
      (distance dataSet left right))
partialDifferenceLipschitz {algebra = algebra} dataSet zero left right =
  subst
    (λ upper → LessEqual algebra (zero algebra) upper)
    (sym (multiplyZeroLeft algebra (distance dataSet left right)))
    (reflexive algebra (zero algebra))
partialDifferenceLipschitz {algebra = algebra}
    dataSet (suc depth) left right =
  subst
    (λ upper →
      LessEqual algebra
        (add algebra
          (termDifference dataSet depth left right)
          (partialDifference dataSet depth left right))
        upper)
    (rightDistributes algebra
      (coefficient dataSet depth)
      (coefficientPartial dataSet depth)
      (distance dataSet left right))
    (addMonotone algebra
      (termDifferenceBound dataSet depth left right)
      (partialDifferenceLipschitz dataSet depth left right))

record SeriesLipschitzLimitPassage
    {Point Bound : Set}
    {algebra : SeriesLipschitzAlgebra Bound}
    (dataSet : TermwiseSeriesLipschitz Point Bound algebra) : Set₁ where
  field
    coefficientTotal : Bound
    fullDifference : Point → Point → Bound

    partialCoefficientBelowTotal : ∀ depth →
      LessEqual algebra
        (coefficientPartial dataSet depth) coefficientTotal

    orderClosedAtSeriesLimit : ∀ left right upper →
      (∀ depth →
        LessEqual algebra
          (partialDifference dataSet depth left right) upper) →
      LessEqual algebra (fullDifference left right) upper

open SeriesLipschitzLimitPassage public

seriesDifferenceLipschitz :
  ∀ {Point Bound}
    {algebra : SeriesLipschitzAlgebra Bound}
    {dataSet : TermwiseSeriesLipschitz Point Bound algebra} →
  (limit : SeriesLipschitzLimitPassage dataSet) →
  ∀ left right →
  LessEqual algebra
    (fullDifference limit left right)
    (multiply algebra
      (coefficientTotal limit)
      (distance dataSet left right))
seriesDifferenceLipschitz {algebra = algebra} {dataSet = dataSet}
    limit left right =
  orderClosedAtSeriesLimit limit left right
    (multiply algebra
      (coefficientTotal limit)
      (distance dataSet left right))
    λ depth →
      transitive algebra
        (partialDifferenceLipschitz dataSet depth left right)
        (multiplyRightMonotone algebra
          (distance dataSet left right)
          (partialCoefficientBelowTotal limit depth))

finiteSeriesLipschitzAssemblyLevel : ProofLevel
finiteSeriesLipschitzAssemblyLevel = machineChecked

seriesLimitLipschitzPassageLevel : ProofLevel
seriesLimitLipschitzPassageLevel = machineChecked

physicalBishopOrderClosedLimitInputsLevel : ProofLevel
physicalBishopOrderClosedLimitInputsLevel = conditional
