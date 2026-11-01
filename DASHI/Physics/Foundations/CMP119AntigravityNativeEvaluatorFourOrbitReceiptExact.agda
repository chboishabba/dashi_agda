{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityNativeEvaluatorFourOrbitReceiptExact where

------------------------------------------------------------------------
-- NO NEW GAUSSIAN BOX HYPOTHESES.
-- The same NativeSetoidLiteralEvaluatorSource fixes both its rich partition
-- and literal Wilson/FP/Haar evaluator.  The existing source evaluator's
-- four joint hypercubic orbit identities then exactly identify the rational
-- lower/upper receipt endpoints. The interaction is paid separately by the
-- existing signed quartic receipt; no arbitrary per-box enclosure is added.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (_+_)
import Real as Bishop
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Foundations.CMP119AntigravityP3GNativeSetoidLiteralEvaluatorExact as Native
import DASHI.Physics.Foundations.CMP119AntigravityRichRegularLiteralEvaluatorSameObjectExact as Receipt
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanLiteralOneLoopFourOrbitSameObjectExact as Four
import DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopOrbitSummedIntervalExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as Finite

module _
  {trajectory Mode Atom expressions ward scalarData
    finiteMode oneLoop remainder rich}
  (source : Native.NativeSetoidLiteralEvaluatorSource
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {expressions = expressions} {ward = ward} {scalarData = scalarData}
    finiteMode oneLoop remainder rich)
  where

  selectedLowerReceiptIsFourOrbits :
    ∀ k →
    Integral.boxLowerSum
      (Rich.regularBoxReceipts (Rich.partition rich k))
    ≡
      Orbit.oneOuterOrbitSum
        (Four.literalLowerContribution (Native.evaluatorAt source k))
      + Orbit.twoOuterOrbitSum
        (Four.literalLowerContribution (Native.evaluatorAt source k))
      + Orbit.threeOuterOrbitSum
        (Four.literalLowerContribution (Native.evaluatorAt source k))
      + Orbit.fourOuterOrbitSum
        (Four.literalLowerContribution (Native.evaluatorAt source k))
  selectedLowerReceiptIsFourOrbits k =
    Receipt.richLowerReceiptSumIsFourJointOrbits
      (Native.partitionSameEvaluator source k)

  selectedUpperReceiptIsFourOrbits :
    ∀ k →
    Integral.boxUpperSum
      (Rich.regularBoxReceipts (Rich.partition rich k))
    ≡
      Orbit.oneOuterOrbitSum
        (Four.literalUpperContribution (Native.evaluatorAt source k))
      + Orbit.twoOuterOrbitSum
        (Four.literalUpperContribution (Native.evaluatorAt source k))
      + Orbit.threeOuterOrbitSum
        (Four.literalUpperContribution (Native.evaluatorAt source k))
      + Orbit.fourOuterOrbitSum
        (Four.literalUpperContribution (Native.evaluatorAt source k))
  selectedUpperReceiptIsFourOrbits k =
    Receipt.richUpperReceiptSumIsFourJointOrbits
      (Native.partitionSameEvaluator source k)

-- The lower and upper sums are concrete selected-evaluator outputs,
-- not additional physical constants. The physical identification of
-- rich.partition with the generated evaluator remains an input to Native.
