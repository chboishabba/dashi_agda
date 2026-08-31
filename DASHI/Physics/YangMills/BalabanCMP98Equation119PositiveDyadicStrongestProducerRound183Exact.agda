{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveDyadicStrongestProducerRound183Exact where

------------------------------------------------------------------------
-- ROUND183 A1 BIDI: ONE POSITIVE COARSE BOND FOR BOTH CMP98 AND CMP109
--
-- R182 replaces independent Eq. (119) axis/orientation fields by an actual
-- repository `PositiveBond`.  The dyadic CMP109 physical owner is already
-- indexed by exactly `PositiveBond (suc coarseN)`.
--
-- Therefore the same positive coarse bond is now used on both sides:
--
--   * it generates the CMP98 canonical L=13 axis segment;
--   * it is the coarse bond passed to the existing dyadic physical principal
--     log and printed equation-(0.12) owner.
--
-- This removes `coarseAtStep` from the Round180 bridge.  The only remaining
-- pointwise physical weld is the actual group-valued relative object.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound177Exact as R177
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanCMP98Equation119DyadicPrintedYWeldRound180Exact as R180
import DASHI.Physics.YangMills.BalabanCMP98Equation119DyadicPhysicalStrongestProducerRound181Exact as R181
import DASHI.Physics.YangMills.BalabanCMP98Equation119PositiveCoarseBondSourceRound182Exact as R182
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicPrintedPhysicalInstantiationExact as Dyadic

record PositiveDyadicRelativeWeld
    {n coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n (suc coarseN) Group group)
    (inputs : Dyadic.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry) : Set₁ where
  field
    fieldAtStep : Nat → Field

    fineSiteAtPoint :
      Nat → Centered.CenteredBlockPoint4 6 → Dyadic.FineSite coarseN

    physicalSmallFieldAtStep : ∀ step →
      Log.PhysicalSmallField
        (Dyadic.principalLogMeaning inputs)
        (fieldAtStep step)

    transportedRelativeIsLiteralContour : ∀ step point →
      Log.transportedRelativeBond
        (Dyadic.principalLogMeaning inputs)
        (fieldAtStep step)
        (R182.coarseBond source step)
        (Dyadic.crossingFineBond inputs
          (R182.coarseBond source step)
          (fineSiteAtPoint step point))
      ≡ R155.relativeContourElement
          (R182.R158.asRound152Source
            (R182.asCanonicalL13Equation119Source source))
          step point

open PositiveDyadicRelativeWeld public

asRound180Weld :
  ∀ {n coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n (suc coarseN) Group group)
    (inputs : Dyadic.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry) →
  PositiveDyadicRelativeWeld source inputs →
  R180.CMP98CMP109DyadicRelativeWeld
    (R182.asCanonicalL13Equation119Source source) inputs
asRound180Weld source inputs weld = record
  { R180.CMP98CMP109DyadicRelativeWeld.fieldAtStep = fieldAtStep weld
  ; R180.CMP98CMP109DyadicRelativeWeld.coarseAtStep =
      R182.coarseBond source
  ; R180.CMP98CMP109DyadicRelativeWeld.fineSiteAtPoint = fineSiteAtPoint weld
  ; R180.CMP98CMP109DyadicRelativeWeld.physicalSmallFieldAtStep =
      physicalSmallFieldAtStep weld
  ; R180.CMP98CMP109DyadicRelativeWeld.transportedRelativeIsLiteralContour =
      transportedRelativeIsLiteralContour weld
  }

positiveDyadicOneStepDerivative :
  ∀ {n coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n (suc coarseN) Group group)
    (inputs : Dyadic.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry)
    (weld : PositiveDyadicRelativeWeld source inputs) →
  R177.ExistingFederbushConventionFamily →
  R126.OneStepAveragingDerivative R178.su2AdditiveCarrier
positiveDyadicOneStepDerivative source inputs weld family =
  R181.dyadicPhysicalOneStepDerivative
    (R182.asCanonicalL13Equation119Source source)
    inputs
    (asRound180Weld source inputs weld)
    family

positiveDyadicMultiscaleDerivative :
  ∀ {n coarseN Group group Field Scalar Radius Entry}
    (source : R182.PositiveCoarseBondEquation119Source
      R178.su2SignedCarrier n (suc coarseN) Group group)
    (inputs : Dyadic.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry)
    (weld : PositiveDyadicRelativeWeld source inputs) →
  R177.ExistingFederbushConventionFamily →
  Nat → R126.Operator R178.su2AdditiveCarrier
positiveDyadicMultiscaleDerivative source inputs weld family =
  R181.dyadicPhysicalMultiscaleDerivative
    (R182.asCanonicalL13Equation119Source source)
    inputs
    (asRound180Weld source inputs weld)
    family

cmp98Equation119PositiveDyadicStrongestProducerRound183Level : ProofLevel
cmp98Equation119PositiveDyadicStrongestProducerRound183Level = machineChecked

cmp98Equation119SamePositiveCoarseBondRound183Level : ProofLevel
cmp98Equation119SamePositiveCoarseBondRound183Level = machineChecked

-- Axis, orientation, and the CMP98->CMP109 coarse-bond index mapping are now
-- construction.  Remaining high-alpha seam: identify the existing dyadic
-- transported-relative group element with the literal closed path holonomy.
literalCMP98DyadicRelativeGroupWeldRound183Level : ProofLevel
literalCMP98DyadicRelativeGroupWeldRound183Level = conditional
