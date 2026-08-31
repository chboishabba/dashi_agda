{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119DyadicPrintedYWeldRound180Exact where

------------------------------------------------------------------------
-- ROUND180 A1 BIDI: LITERAL CMP98 Y_x = EXISTING PRINTED CMP109 PHYSICAL LOG
--
-- Primary sources:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", Commun. Math. Phys. 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- The existing dyadic printed-map owner already makes its transported log the
-- `physicalLog` from `PhysicalSU2PrincipalLogMeaning`, and already proves that
-- this physical log is exactly the anti-Hermitian coordinate of the printed
-- CMP109 equation-(0.12) relative product.
--
-- Round157 already proves that the SAME physical log equals the literal CMP98
-- principal coordinate once its transported-relative group element is the
-- literal path-holonomy product U(Gamma_{c,x}) U(c)^-1.
--
-- Hence the only bridge retained here is the group-level same-object theorem.
-- The equality of Lie coordinates is derived by composition; callers cannot
-- independently choose a CMP98 Y and a CMP109 printed logarithm.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanCMP98Equation119CanonicalCoarseSegmentRound158Exact as R158
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanCMP98Equation119ExistingPrincipalLogRound156Exact as R156
import DASHI.Physics.YangMills.BalabanCMP98Equation119PhysicalPrincipalImageRound157Exact as R157
import DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushSelectedCutProducerRound178Exact as R178
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PrintedPathFormulaExact as Printed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicPrintedPhysicalInstantiationExact as Dyadic

record CMP98CMP109DyadicRelativeWeld
    {n coarseN Group group Field Scalar Radius Entry}
    (source : R158.CanonicalL13Equation119Source
      R178.su2SignedCarrier n Group group)
    (inputs : Dyadic.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry) : Set₁ where
  field
    fieldAtStep : Nat → Field
    coarseAtStep : Nat → Dyadic.CoarseBond coarseN
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
        (coarseAtStep step)
        (Dyadic.crossingFineBond inputs
          (coarseAtStep step)
          (fineSiteAtPoint step point))
      ≡ R155.relativeContourElement
          (R158.asRound152Source source) step point

open CMP98CMP109DyadicRelativeWeld public

asRound157PhysicalBridge :
  ∀ {n coarseN Group group Field Scalar Radius Entry}
    (source : R158.CanonicalL13Equation119Source
      R178.su2SignedCarrier n Group group)
    (inputs : Dyadic.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry) →
  CMP98CMP109DyadicRelativeWeld source inputs →
  R157.CMP98RelativeContourPhysicalBridge
    (R158.asRound152Source source)
    (Dyadic.principalLogMeaning inputs)
asRound157PhysicalBridge source inputs weld = record
  { R157.CMP98RelativeContourPhysicalBridge.fieldAtStep =
      fieldAtStep weld
  ; R157.CMP98RelativeContourPhysicalBridge.coarseAtStep =
      coarseAtStep weld
  ; R157.CMP98RelativeContourPhysicalBridge.fineAtPoint =
      λ step point →
        Dyadic.crossingFineBond inputs
          (coarseAtStep weld step)
          (fineSiteAtPoint weld step point)
  ; R157.CMP98RelativeContourPhysicalBridge.physicalSmallFieldAtStep =
      physicalSmallFieldAtStep weld
  ; R157.CMP98RelativeContourPhysicalBridge.transportedRelativeIsLiteralContour =
      transportedRelativeIsLiteralContour weld
  }

cmp98PrincipalYIsPrintedCMP109RelativeLog :
  ∀ {n coarseN Group group Field Scalar Radius Entry}
    (source : R158.CanonicalL13Equation119Source
      R178.su2SignedCarrier n Group group)
    (inputs : Dyadic.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry)
    (weld : CMP98CMP109DyadicRelativeWeld source inputs)
    step point →
  R156.principalPointY
    (R158.asRound152Source source)
    (Log.chart (Dyadic.principalLogMeaning inputs))
    step point
  ≡ Printed.antiHermitianLogCoordinate
      (Dyadic.printedData inputs)
      (Printed.printedEquation012RelativeProduct
        (Dyadic.printedData inputs)
        (fieldAtStep weld step)
        (coarseAtStep weld step)
        (fineSiteAtPoint weld step point))
cmp98PrincipalYIsPrintedCMP109RelativeLog source inputs weld step point =
  trans
    (sym
      (R157.physicalLogEqualsPrincipalPointY
        (R158.asRound152Source source)
        (Dyadic.principalLogMeaning inputs)
        (asRound157PhysicalBridge source inputs weld)
        step point))
    (Dyadic.printedRelativeProductUsesPhysicalPrincipalLog inputs
      (fieldAtStep weld step)
      (coarseAtStep weld step)
      (fineSiteAtPoint weld step point))

cmp98LiteralRelativeElementIsCMP109PhysicalTransport :
  ∀ {n coarseN Group group Field Scalar Radius Entry}
    (source : R158.CanonicalL13Equation119Source
      R178.su2SignedCarrier n Group group)
    (inputs : Dyadic.DyadicCMP109PrintedPhysicalInputs
      coarseN Field Group Lie.SU2LieAlgebra Scalar Radius Entry)
    (weld : CMP98CMP109DyadicRelativeWeld source inputs)
    step point →
  R155.relativeContourElement
    (R158.asRound152Source source) step point
  ≡ Log.transportedRelativeBond
      (Dyadic.principalLogMeaning inputs)
      (fieldAtStep weld step)
      (coarseAtStep weld step)
      (Dyadic.crossingFineBond inputs
        (coarseAtStep weld step)
        (fineSiteAtPoint weld step point))
cmp98LiteralRelativeElementIsCMP109PhysicalTransport source inputs weld step point =
  sym (transportedRelativeIsLiteralContour weld step point)

cmp98Equation119DyadicPrintedYWeldRound180Level : ProofLevel
cmp98Equation119DyadicPrintedYWeldRound180Level = machineChecked

cmp98Equation119PrintedPhysicalLogSamePointYRound180Level : ProofLevel
cmp98Equation119PrintedPhysicalLogSamePointYRound180Level = machineChecked

-- The Lie-coordinate normalization between CMP98 Y_x and the existing printed
-- CMP109 relative log is downstream.  The surviving physical seam is the
-- group-level same-object identification of the two relative holonomies.
literalCMP98CMP109RelativeGroupSameObjectRound180Level : ProofLevel
literalCMP98CMP109RelativeGroupSameObjectRound180Level = conditional
