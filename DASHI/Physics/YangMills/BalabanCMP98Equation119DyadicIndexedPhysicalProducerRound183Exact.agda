{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119DyadicIndexedPhysicalProducerRound183Exact where

------------------------------------------------------------------------
-- ROUND183 A1 BIDI: DYADIC INDEXING IS CONSTRUCTION, NOT A WELD INPUT
--
-- Round180 still allowed callers to choose `coarseAtStep` and
-- `fineSiteAtPoint` independently.  Round182 already stores the actual positive
-- coarse bond, while the Eq. (119) source already stores the centred periodic
-- embedding.  On the literal dyadic carrier their types are exactly the CMP109
-- coarse-bond and fine-site carriers.
--
-- Therefore:
--
--   coarseAtStep   = source.coarseBond
--   fineSiteAtPoint = embed(source.minusEmbedding, point)
--
-- definitionally.  The strongest dyadic producer below retains only the actual
-- field/small-field selection and the substantive same-object theorem for the
-- transported relative group element.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicProjectionNormalizationExact as Dyadic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicPrintedPhysicalInstantiationExact as DyadicPrinted
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanCMP98Equation119DyadicPrintedYWeldRound180Exact as R180
import DASHI.Physics.YangMills.BalabanCMP98Equation119DyadicPhysicalStrongestProducerRound181Exact as R181
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveCoarseBondSourceRound182Exact as R182

record DyadicIndexedPhysicalRelativeInputs
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

    transportedRelativeIsLiteralContour : ∀ step point →
      Log.transportedRelativeBond
        (DyadicPrinted.principalLogMeaning inputs)
        (fieldAtStep step)
        (R182.coarseBond source step)
        (DyadicPrinted.crossingFineBond inputs
          (R182.coarseBond source step)
          (Embed.embed (R182.minusEmbedding source step) point))
      ≡ R155.relativeContourElement
          (R158.asRound152Source
            (R182.asCanonicalL13Equation119Source source))
          step point

open DyadicIndexedPhysicalRelativeInputs public

asRound180RelativeWeld :
  ∀ {coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier
      (Dyadic.dyadicFineN coarseN)
      (suc coarseN)
      Group group)
    (inputs : DyadicPrinted.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry) →
  DyadicIndexedPhysicalRelativeInputs source inputs →
  R180.CMP98CMP109DyadicRelativeWeld
    (R182.asCanonicalL13Equation119Source source)
    inputs
asRound180RelativeWeld source inputs indexed = record
  { R180.CMP98CMP109DyadicRelativeWeld.fieldAtStep =
      fieldAtStep indexed
  ; R180.CMP98CMP109DyadicRelativeWeld.coarseAtStep =
      R182.coarseBond source
  ; R180.CMP98CMP109DyadicRelativeWeld.fineSiteAtPoint =
      λ step point → Embed.embed (R182.minusEmbedding source step) point
  ; R180.CMP98CMP109DyadicRelativeWeld.physicalSmallFieldAtStep =
      physicalSmallFieldAtStep indexed
  ; R180.CMP98CMP109DyadicRelativeWeld.transportedRelativeIsLiteralContour =
      transportedRelativeIsLiteralContour indexed
  }

dyadicIndexedPhysicalOneStepDerivative :
  ∀ {coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier
      (Dyadic.dyadicFineN coarseN)
      (suc coarseN)
      Group group)
    (inputs : DyadicPrinted.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry)
    (indexed : DyadicIndexedPhysicalRelativeInputs source inputs) →
  R177.ExistingFederbushConventionFamily →
  R126.OneStepAveragingDerivative R178.su2AdditiveCarrier
dyadicIndexedPhysicalOneStepDerivative source inputs indexed family =
  R181.dyadicPhysicalOneStepDerivative
    (R182.asCanonicalL13Equation119Source source)
    inputs
    (asRound180RelativeWeld source inputs indexed)
    family

dyadicIndexedPhysicalMultiscaleDerivative :
  ∀ {coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier
      (Dyadic.dyadicFineN coarseN)
      (suc coarseN)
      Group group)
    (inputs : DyadicPrinted.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry)
    (indexed : DyadicIndexedPhysicalRelativeInputs source inputs) →
  R177.ExistingFederbushConventionFamily →
  Nat → R126.Operator R178.su2AdditiveCarrier
dyadicIndexedPhysicalMultiscaleDerivative source inputs indexed family =
  R181.dyadicPhysicalMultiscaleDerivative
    (R182.asCanonicalL13Equation119Source source)
    inputs
    (asRound180RelativeWeld source inputs indexed)
    family

cmp98Equation119DyadicIndexedPhysicalProducerRound183Level : ProofLevel
cmp98Equation119DyadicIndexedPhysicalProducerRound183Level = machineChecked

cmp98Equation119DyadicCoarseAndFineIndexingDerivedRound183Level : ProofLevel
cmp98Equation119DyadicCoarseAndFineIndexingDerivedRound183Level = machineChecked

-- The indexing freedom is gone.  On this route the remaining physical leaf is
-- now exactly the same-object equality between the dyadic physical transported
-- relative element and the literal CMP98 path-holonomy relative product, for the
-- selected field at each step.
literalCMP98DyadicTransportedRelativeSameObjectRound183Level : ProofLevel
literalCMP98DyadicTransportedRelativeSameObjectRound183Level = conditional
