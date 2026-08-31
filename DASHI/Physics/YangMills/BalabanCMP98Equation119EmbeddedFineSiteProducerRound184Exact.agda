{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119EmbeddedFineSiteProducerRound184Exact where

------------------------------------------------------------------------
-- ROUND184 A1 BIDI: THE DYADIC FINE SITE IS THE EMBEDDED CMP98 POINT
--
-- Round183 already uses one actual positive coarse bond on the CMP98 and CMP109
-- sides.  Its remaining `fineSiteAtPoint` field is likewise not independent on
-- the literal dyadic carrier: the Eq. (119) source already owns the centred
-- no-wrap embedding, whose output type is exactly the dyadic `FineSite`.
--
-- Hence
--
--   fineSiteAtPoint(step,x) = embed(minusEmbedding(step),x)
--
-- by construction.  The only pointwise physical leaf retained here is the
-- transported-relative group equality at that exact site.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicProjectionNormalizationExact as Dyadic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicPrintedPhysicalInstantiationExact as Printed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveCoarseBondSourceRound182Exact as R182
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveDyadicStrongestProducerRound183Exact as R183

record EmbeddedFineSiteRelativeWeld
    {coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier
      (Dyadic.dyadicFineN coarseN)
      (suc coarseN)
      Group group)
    (inputs : Printed.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry) : Set₁ where
  field
    fieldAtStep : Nat → Field

    physicalSmallFieldAtStep : ∀ step →
      Log.PhysicalSmallField
        (Printed.principalLogMeaning inputs)
        (fieldAtStep step)

    transportedRelativeIsLiteralContour : ∀ step point →
      Log.transportedRelativeBond
        (Printed.principalLogMeaning inputs)
        (fieldAtStep step)
        (R182.coarseBond source step)
        (Printed.crossingFineBond inputs
          (R182.coarseBond source step)
          (Embed.embed (R182.minusEmbedding source step) point))
      ≡ R155.relativeContourElement
          (R158.asRound152Source
            (R182.asCanonicalL13Equation119Source source))
          step point

open EmbeddedFineSiteRelativeWeld public

asPositiveDyadicRelativeWeld :
  ∀ {coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier
      (Dyadic.dyadicFineN coarseN)
      (suc coarseN)
      Group group)
    (inputs : Printed.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry) →
  EmbeddedFineSiteRelativeWeld source inputs →
  R183.PositiveDyadicRelativeWeld source inputs
asPositiveDyadicRelativeWeld source inputs weld = record
  { R183.PositiveDyadicRelativeWeld.fieldAtStep = fieldAtStep weld
  ; R183.PositiveDyadicRelativeWeld.fineSiteAtPoint =
      λ step point → Embed.embed (R182.minusEmbedding source step) point
  ; R183.PositiveDyadicRelativeWeld.physicalSmallFieldAtStep =
      physicalSmallFieldAtStep weld
  ; R183.PositiveDyadicRelativeWeld.transportedRelativeIsLiteralContour =
      transportedRelativeIsLiteralContour weld
  }

embeddedFineSiteOneStepDerivative :
  ∀ {coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier
      (Dyadic.dyadicFineN coarseN)
      (suc coarseN)
      Group group)
    (inputs : Printed.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry)
    (weld : EmbeddedFineSiteRelativeWeld source inputs) →
  R177.ExistingFederbushConventionFamily →
  R126.OneStepAveragingDerivative R178.su2AdditiveCarrier
embeddedFineSiteOneStepDerivative source inputs weld family =
  R183.positiveDyadicOneStepDerivative
    source inputs (asPositiveDyadicRelativeWeld source inputs weld) family

embeddedFineSiteMultiscaleDerivative :
  ∀ {coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier
      (Dyadic.dyadicFineN coarseN)
      (suc coarseN)
      Group group)
    (inputs : Printed.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry)
    (weld : EmbeddedFineSiteRelativeWeld source inputs) →
  R177.ExistingFederbushConventionFamily →
  Nat → R126.Operator R178.su2AdditiveCarrier
embeddedFineSiteMultiscaleDerivative source inputs weld family =
  R183.positiveDyadicMultiscaleDerivative
    source inputs (asPositiveDyadicRelativeWeld source inputs weld) family

cmp98Equation119EmbeddedFineSiteProducerRound184Level : ProofLevel
cmp98Equation119EmbeddedFineSiteProducerRound184Level = machineChecked

cmp98Equation119FineSiteIndexDerivedRound184Level : ProofLevel
cmp98Equation119FineSiteIndexDerivedRound184Level = machineChecked

literalCMP98DyadicTransportedRelativeSameObjectRound184Level : ProofLevel
literalCMP98DyadicTransportedRelativeSameObjectRound184Level = conditional
