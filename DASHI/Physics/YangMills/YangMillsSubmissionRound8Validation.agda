module DASHI.Physics.YangMills.YangMillsSubmissionRound8Validation where

open import Agda.Builtin.Nat using (Nat; suc)

import Real as BishopReal
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as ConcreteHalf
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfRadiusRatiosExact as ConcreteRatios
import DASHI.Physics.YangMills.BalabanBishopRatioMonotoneTermsExact as Ratio
import DASHI.Physics.YangMills.BalabanBishopSetoidRatioMonotoneExact as SetoidRatio
import DASHI.Physics.YangMills.BalabanBishopAlternatingFirstOmittedExact as Alternating
import DASHI.Physics.YangMills.BalabanBishopSetoidAlternatingFirstOmittedExact as SetoidAlternating
import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy as Entropy
import DASHI.Physics.YangMills.BalabanP06CanonicalAnimalConstantExact as P06
import DASHI.Physics.YangMills.BalabanP06A1A2A3InfluenceExact as A123
import DASHI.Physics.YangMills.BalabanClayGate4OscillationAnimalInfluenceExact as Influence
import DASHI.Physics.YangMills.BalabanP11PrefixTailMinimumExact as P11PrefixTail
import DASHI.Physics.YangMills.BalabanP11UniformAbsorptionReductionExact as P11
import DASHI.Physics.YangMills.BalabanStepVCanonicalAnimalMarginExact as Margin
import DASHI.Physics.YangMills.BalabanStepVGeometricInfluenceSummationExact as Summation
import DASHI.Physics.YangMills.YangMillsSubmissionRound8Ledger as Ledger
import DASHI.Physics.YangMills.YangMillsSubmissionRound8Receipt as Receipt
open import DASHI.Physics.YangMills.CompactLieProofLevel

concreteBishopHalfBallValidated :
  (value : BishopReal.ℝ) →
  BishopReal._≤_ (BishopReal.∣_∣ value) ConcreteHalf.bishopHalf →
  BishopReal._≤_
    (ConcreteHalf.bishopMagnitudeSquare value)
    ConcreteHalf.bishopQuarter
concreteBishopHalfBallValidated =
  ConcreteHalf.bishopHalfBallMagnitudeSquareBelowQuarter

concreteBishopRatioCertificateValidated :
  (value : BishopReal.ℝ) →
  BishopReal._≤_ (BishopReal.∣_∣ value) ConcreteHalf.bishopHalf →
  ConcreteRatios.ConcreteBishopHalfRadiusRatioCertificate value
concreteBishopRatioCertificateValidated =
  ConcreteRatios.concreteBishopHalfRadiusRatioCertificate

ratioMonotonicityReducerValidated :
  ∀ {Scalar : Set}
    {kernel : Ratio.OrderedRatioKernel Scalar} →
  (dataSet : Ratio.SuccessiveRatioTerms kernel) →
  ∀ index →
  Ratio.OrderedRatioKernel.LessEqual kernel
    (Ratio.SuccessiveRatioTerms.term dataSet (suc index))
    (Ratio.SuccessiveRatioTerms.term dataSet index)
ratioMonotonicityReducerValidated =
  Ratio.successiveRatioGivesDecreasing

bishopSetoidRatioReducerValidated :
  (dataSet :
    SetoidRatio.SetoidSuccessiveRatioTerms
      SetoidRatio.bishopSetoidOrderedRatioKernel) →
  ∀ index →
  BishopReal._≤_
    (SetoidRatio.SetoidSuccessiveRatioTerms.term dataSet (suc index))
    (SetoidRatio.SetoidSuccessiveRatioTerms.term dataSet index)
bishopSetoidRatioReducerValidated =
  SetoidRatio.bishopSuccessiveRatioGivesDecreasing

alternatingTailReducerValidated :
  ∀ {Scalar : Set}
    {kernel : Alternating.OrderedDifferenceKernel Scalar} →
  Alternating.AlternatingPartialSumBrackets kernel →
  Alternating.SignedFirstOmittedTail kernel
alternatingTailReducerValidated =
  Alternating.alternatingBracketsGiveFirstOmittedTail

bishopSetoidAlternatingTailValidated :
  (brackets :
    SetoidAlternating.SetoidAlternatingPartialSumBrackets
      SetoidAlternating.bishopSetoidOrderedDifferenceKernel) →
  SetoidAlternating.SetoidSignedFirstOmittedTail
    SetoidAlternating.bishopSetoidOrderedDifferenceKernel
bishopSetoidAlternatingTailValidated =
  SetoidAlternating.bishopAlternatingBracketsGiveFirstOmittedTail

canonicalP06ConstantValidated :
  (package : Entropy.P06ModelLeafDischargePackage) →
  P06.CanonicalP06AnimalConstantCertificate package
canonicalP06ConstantValidated =
  P06.canonicalP06AnimalConstantCertificate

p11PrefixTailReducerValidated :
  P11PrefixTail.P11PrefixTailMinimumInputs →
  P11.P11UniformAbsorptionInputs
p11PrefixTailReducerValidated =
  P11PrefixTail.p11UniformInputsFromPrefixTail

canonicalAnimalMarginValidated :
  ∀ {Bound : Set}
    {kernel : Margin.LogAnimalMarginKernel Bound}
    {package : Entropy.P06ModelLeafDischargePackage} →
  (kappa : Bound) →
  Margin.LogAnimalMarginKernel.StrictlyLess kernel
    (Margin.LogAnimalMarginKernel.logarithm kernel
      (Margin.LogAnimalMarginKernel.fromNat kernel
        (P06.canonicalAnimalConstant package)))
    kappa →
  Margin.CanonicalAnimalDecayMargin kernel package
canonicalAnimalMarginValidated =
  Margin.canonicalAnimalDecayMargin

geometricInfluenceCompositionValidated :
  ∀ {Scale Bound : Set}
    {algebra : Influence.InfluenceAlgebra Bound}
    {inputs :
      A123.PhysicalA1A2A3InfluenceInputs
        {Scale = Scale} {Bound = Bound} algebra} →
  Summation.GeometricInfluenceSummationKernel
    {Scale = Scale} {Bound = Bound} algebra inputs →
  Summation.UniformInfluenceBoundCertificate
    {Scale = Scale} {Bound = Bound} algebra
geometricInfluenceCompositionValidated =
  Summation.uniformInfluenceBoundFromGeometricSummation

round8LedgerValidated : Ledger.SubmissionRound8Ledger
round8LedgerValidated = Ledger.currentSubmissionRound8Ledger

round8ReceiptValidated : Receipt.SubmissionRound8Receipt
round8ReceiptValidated = Receipt.currentSubmissionRound8Receipt

submissionRound8ValidationLevel : ProofLevel
submissionRound8ValidationLevel = machineChecked
