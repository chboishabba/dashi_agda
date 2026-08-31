{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119DyadicPrintedFactorWeldRound186Exact where

------------------------------------------------------------------------
-- ROUND186 A1 BIDI: DIAGNOSTIC FOUR-FACTOR WELD
--
-- Round185 gives the literal CMP98 relative element the same four-factor
-- parenthesization as printed CMP109 equation (0.12).  This file records a
-- sufficient factorwise route to the remaining whole-object weld.  It is an
-- audit/decomposition route: equation-(0.11) source/target factors are genuine
-- group averages, so their equality with a selected canonical contour is not
-- assumed elsewhere merely from common endpoints.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicProjectionNormalizationExact as Dyadic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicPrintedPhysicalInstantiationExact as DyadicPrinted
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PrintedPathFormulaExact as Printed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveCoarseBondSourceRound182Exact as R182
import DASHI.Physics.YangMills.BalabanCMP98Equation119EmbeddedFineSiteProducerRound184Exact as R184
import DASHI.Physics.YangMills.BalabanCMP98Equation119FourFactorRelativeNormalFormRound185Exact as R185

record DyadicPrintedFactorWeld
    {coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier
      (Dyadic.dyadicFineN coarseN)
      (suc coarseN)
      Group group)
    (inputs : DyadicPrinted.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry) : Set₁ where
  field
    fieldAtStep : Nat → Field

    physicalSmallFieldAtStep : ∀ step →
      Log.PhysicalSmallField
        (DyadicPrinted.principalLogMeaning inputs)
        (fieldAtStep step)

    printedMultiplyIsSourceMultiply : ∀ left right →
      Printed.multiplyGroup (DyadicPrinted.printedData inputs) left right
      ≡ Bond.multiply group left right

    transportedRelativeIsPrintedProduct : ∀ step point →
      Log.transportedRelativeBond
        (DyadicPrinted.principalLogMeaning inputs)
        (fieldAtStep step)
        (R182.coarseBond source step)
        (DyadicPrinted.crossingFineBond inputs
          (R182.coarseBond source step)
          (Embed.embed (R182.minusEmbedding source step) point))
      ≡ Printed.printedEquation012RelativeProduct
          (DyadicPrinted.printedData inputs)
          (fieldAtStep step)
          (R182.coarseBond source step)
          (Embed.embed (R182.minusEmbedding source step) point)

    sourceFactorMatches : ∀ step point →
      Printed.sourceAveragedContour
        (DyadicPrinted.printedData inputs)
        (fieldAtStep step)
        (R182.coarseBond source step)
        (Embed.embed (R182.minusEmbedding source step) point)
      ≡ R185.sourceContourHolonomy
          (R158.asRound152Source
            (R182.asCanonicalL13Equation119Source source))
          step point

    crossingFactorMatches : ∀ step point →
      Printed.crossingValue
        (DyadicPrinted.printedData inputs)
        (fieldAtStep step)
        (R182.coarseBond source step)
        (Embed.embed (R182.minusEmbedding source step) point)
      ≡ R185.crossingHolonomy
          (R158.asRound152Source
            (R182.asCanonicalL13Equation119Source source))
          step point

    targetReverseFactorMatches : ∀ step point →
      Printed.targetAveragedContourReverse
        (DyadicPrinted.printedData inputs)
        (fieldAtStep step)
        (R182.coarseBond source step)
        (Embed.embed (R182.minusEmbedding source step) point)
      ≡ R185.targetReverseHolonomy
          (R158.asRound152Source
            (R182.asCanonicalL13Equation119Source source))
          step point

    coarseReverseFactorMatches : ∀ step →
      Printed.reversedCoarseBondValue
        (DyadicPrinted.printedData inputs)
        (fieldAtStep step)
        (R182.coarseBond source step)
      ≡ R185.coarseReverseHolonomy
          (R158.asRound152Source
            (R182.asCanonicalL13Equation119Source source))
          step

open DyadicPrintedFactorWeld public

printedFourFactorUsesSourceMultiplication :
  ∀ {coarseN Group group Field Scalar Radius Entry}
    {source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier
      (Dyadic.dyadicFineN coarseN)
      (suc coarseN)
      Group group}
    {inputs : DyadicPrinted.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry}
    (weld : DyadicPrintedFactorWeld source inputs)
    a b c d →
  Printed.multiplyGroup (DyadicPrinted.printedData inputs) a
    (Printed.multiplyGroup (DyadicPrinted.printedData inputs) b
      (Printed.multiplyGroup (DyadicPrinted.printedData inputs) c d))
  ≡ Bond.multiply group a
      (Bond.multiply group b (Bond.multiply group c d))
printedFourFactorUsesSourceMultiplication {group = group} {inputs = inputs}
    weld a b c d =
  trans
    (printedMultiplyIsSourceMultiply weld a
      (Printed.multiplyGroup (DyadicPrinted.printedData inputs) b
        (Printed.multiplyGroup (DyadicPrinted.printedData inputs) c d)))
    (cong (Bond.multiply group a)
      (trans
        (printedMultiplyIsSourceMultiply weld b
          (Printed.multiplyGroup (DyadicPrinted.printedData inputs) c d))
        (cong (Bond.multiply group b)
          (printedMultiplyIsSourceMultiply weld c d))))

printedRelativeProductIsLiteralRelative :
  ∀ {coarseN Group group Field Scalar Radius Entry}
    {source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier
      (Dyadic.dyadicFineN coarseN)
      (suc coarseN)
      Group group}
    {inputs : DyadicPrinted.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry}
    (weld : DyadicPrintedFactorWeld source inputs)
    step point →
  Printed.printedEquation012RelativeProduct
      (DyadicPrinted.printedData inputs)
      (fieldAtStep weld step)
      (R182.coarseBond source step)
      (Embed.embed (R182.minusEmbedding source step) point)
  ≡ R155.relativeContourElement
      (R158.asRound152Source
        (R182.asCanonicalL13Equation119Source source))
      step point
printedRelativeProductIsLiteralRelative {group = group} {source = source} {inputs = inputs}
    weld step point =
  let
    pd = DyadicPrinted.printedData inputs
    field = fieldAtStep weld step
    coarse = R182.coarseBond source step
    fine = Embed.embed (R182.minusEmbedding source step) point
    cmp98Source =
      R158.asRound152Source (R182.asCanonicalL13Equation119Source source)
    a = Printed.sourceAveragedContour pd field coarse fine
    b = Printed.crossingValue pd field coarse fine
    c = Printed.targetAveragedContourReverse pd field coarse fine
    d = Printed.reversedCoarseBondValue pd field coarse
    multiplication = printedFourFactorUsesSourceMultiplication weld a b c d
    factors =
      cong₂ (Bond.multiply group)
        (sourceFactorMatches weld step point)
        (cong₂ (Bond.multiply group)
          (crossingFactorMatches weld step point)
          (cong₂ (Bond.multiply group)
            (targetReverseFactorMatches weld step point)
            (coarseReverseFactorMatches weld step)))
  in
  trans multiplication
    (trans factors
      (sym (R185.relativeContourElementFourFactorNormalForm
        cmp98Source step point)))

asEmbeddedFineSiteRelativeWeld :
  ∀ {coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier
      (Dyadic.dyadicFineN coarseN)
      (suc coarseN)
      Group group)
    (inputs : DyadicPrinted.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry) →
  DyadicPrintedFactorWeld source inputs →
  R184.EmbeddedFineSiteRelativeWeld source inputs
asEmbeddedFineSiteRelativeWeld source inputs weld = record
  { R184.EmbeddedFineSiteRelativeWeld.fieldAtStep = fieldAtStep weld
  ; R184.EmbeddedFineSiteRelativeWeld.physicalSmallFieldAtStep =
      physicalSmallFieldAtStep weld
  ; R184.EmbeddedFineSiteRelativeWeld.transportedRelativeIsLiteralContour =
      λ step point →
        trans
          (transportedRelativeIsPrintedProduct weld step point)
          (printedRelativeProductIsLiteralRelative weld step point)
  }

dyadicPrintedFactorOneStepDerivative :
  ∀ {coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier
      (Dyadic.dyadicFineN coarseN)
      (suc coarseN)
      Group group)
    (inputs : DyadicPrinted.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry)
    (weld : DyadicPrintedFactorWeld source inputs) →
  R177.ExistingFederbushConventionFamily →
  R126.OneStepAveragingDerivative R178.su2AdditiveCarrier
dyadicPrintedFactorOneStepDerivative source inputs weld family =
  R184.embeddedFineSiteOneStepDerivative
    source inputs (asEmbeddedFineSiteRelativeWeld source inputs weld) family

cmp98Equation119DyadicPrintedFactorWeldRound186Level : ProofLevel
cmp98Equation119DyadicPrintedFactorWeldRound186Level = machineChecked

-- This route is sufficient but deliberately not promoted as the shortest path:
-- source/target CMP109 factors are genuine equation-(0.11) group averages.
-- Their equality with one selected canonical contour requires an explicit
-- theorem and is not inferred from common endpoints.
literalCMP98DyadicPrintedFactorSameObjectRound186Level : ProofLevel
literalCMP98DyadicPrintedFactorSameObjectRound186Level = conditional
