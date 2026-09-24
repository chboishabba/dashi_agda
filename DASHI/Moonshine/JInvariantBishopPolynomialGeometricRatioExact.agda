module DASHI.Moonshine.JInvariantBishopPolynomialGeometricRatioExact where

------------------------------------------------------------------------
-- DEGREE-4 / DEGREE-6 POLYNOMIAL x GEOMETRIC ABSOLUTE CONVERGENCE
--
-- DASHI CONTRIBUTION / CROSS-POLLINATION
--
-- Combine:
--   * the literal Nat degree-4/6 successor envelopes;
--   * the generic Bishop Archimedean gap-absorption theorem; and
--   * Murray/Bishop's native ratio test.
--
-- For 0 <= r < s < 1 this proves absolute convergence of
--
--   n^4 r^n    and    n^6 r^n.
--
-- No logarithm, completed geometric-series formula, or Moonshine-specific
-- Cauchy axiom is assumed.  The larger ratio s is explicit; constructing it
-- from merely r < 1 is a separate small order lemma.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_; _⊔_)
import Data.Nat.Properties as NatP
open import Data.Integer.Base as ℤ using (+_)
open import Data.Rational.Unnormalised as ℚ using (_/_)
import Data.Rational.Unnormalised.Properties as ℚP
open import Data.Product.Base using (_,_; proj₁)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopArchimedeanLinearAbsorptionExact as Absorb
import DASHI.Analysis.BishopUnitIntervalMidpointExact as Midpoint
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as NatReal
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as DegreeOne
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as SeriesExt
import DASHI.Mathematics.NumberTheory.FiniteNatRationalEmbeddingExact as NatEmbed
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Power
import DASHI.Moonshine.JInvariantPolynomialSuccessorEnvelopeExact as Envelope

natPowerReal : Nat → Nat → BishopReal.ℝ
natPowerReal degree n =
  NatReal.natReal (Power.powNat n degree)

natRealAdd :
  ∀ left right →
  BishopReal._≃_
    (NatReal.natReal (left + right))
    (BishopReal._+_
      (NatReal.natReal left)
      (NatReal.natReal right))
natRealAdd left right =
  BishopP.≃-trans
    (BishopP.⋆-cong
      (NatEmbed.natAsRationalAdd left right))
    (BishopP.⋆-distrib-+
      (NatEmbed.natAsRational left)
      (NatEmbed.natAsRational right))

natRealMul :
  ∀ left right →
  BishopReal._≃_
    (NatReal.natReal (left * right))
    (BishopReal._*_
      (NatReal.natReal left)
      (NatReal.natReal right))
natRealMul left right =
  BishopP.≃-trans
    (BishopP.⋆-cong
      (NatEmbed.natAsRationalMul left right))
    (BishopP.⋆-distrib-*
      (NatEmbed.natAsRational left)
      (NatEmbed.natAsRational right))

natPowerRealNonnegative :
  ∀ degree n →
  BishopReal.NonNegative (natPowerReal degree n)
natPowerRealNonnegative degree n =
  DegreeOne.natRealNonnegative
    (Power.powNat n degree)

natPowerSuccessorExponent :
  ∀ degree n →
  BishopReal._≃_
    (natPowerReal (suc degree) n)
    (BishopReal._*_
      (NatReal.natReal n)
      (natPowerReal degree n))
natPowerSuccessorExponent degree n =
  natRealMul n (Power.powNat n degree)

embeddedDegreeFourEnvelope :
  ∀ n → 1 ≤ n →
  BishopReal._≤_
    (natPowerReal 4 (suc n))
    (BishopReal._+_
      (natPowerReal 4 n)
      (BishopReal._*_
        (NatReal.natReal 15)
        (natPowerReal 3 n)))
embeddedDegreeFourEnvelope n nPositive =
  let
    raw =
      Absorb.natRealMonotone
        (Envelope.degreeFourSuccessorEnvelope n nPositive)

    rightMeaning =
      BishopP.≃-trans
        (natRealAdd
          (Power.powNat n 4)
          (15 * Power.powNat n 3))
        (BishopP.+-cong
          BishopP.≃-refl
          (natRealMul 15 (Power.powNat n 3)))
  in
  BishopP.≤-respʳ-≃
    rightMeaning
    raw

embeddedDegreeSixEnvelope :
  ∀ n → 1 ≤ n →
  BishopReal._≤_
    (natPowerReal 6 (suc n))
    (BishopReal._+_
      (natPowerReal 6 n)
      (BishopReal._*_
        (NatReal.natReal 63)
        (natPowerReal 5 n)))
embeddedDegreeSixEnvelope n nPositive =
  let
    raw =
      Absorb.natRealMonotone
        (Envelope.degreeSixSuccessorEnvelope n nPositive)

    rightMeaning =
      BishopP.≃-trans
        (natRealAdd
          (Power.powNat n 6)
          (63 * Power.powNat n 5))
        (BishopP.+-cong
          BishopP.≃-refl
          (natRealMul 63 (Power.powNat n 5)))
  in
  BishopP.≤-respʳ-≃
    rightMeaning
    raw

degreeFourCutoff :
  ∀ {ratio largerRatio} →
  Absorb.BishopStrictRatioPair ratio largerRatio →
  Nat
degreeFourCutoff inputs =
  1 ⊔ Absorb.absorptionCutoff inputs 15

degreeSixCutoff :
  ∀ {ratio largerRatio} →
  Absorb.BishopStrictRatioPair ratio largerRatio →
  Nat
degreeSixCutoff inputs =
  1 ⊔ Absorb.absorptionCutoff inputs 63

cutoffPositive :
  ∀ {ratio largerRatio}
    (inputs : Absorb.BishopStrictRatioPair ratio largerRatio)
    coefficient n →
  (1 ⊔ Absorb.absorptionCutoff inputs coefficient) ≤ n →
  1 ≤ n
cutoffPositive inputs coefficient n cutoff≤n =
  NatP.≤-trans
    (NatP.m≤m⊔n 1
      (Absorb.absorptionCutoff inputs coefficient))
    cutoff≤n

absorptionCutoffBelow :
  ∀ {ratio largerRatio}
    (inputs : Absorb.BishopStrictRatioPair ratio largerRatio)
    coefficient n →
  (1 ⊔ Absorb.absorptionCutoff inputs coefficient) ≤ n →
  Absorb.absorptionCutoff inputs coefficient ≤ n
absorptionCutoffBelow inputs coefficient n cutoff≤n =
  NatP.≤-trans
    (NatP.n≤m⊔n 1
      (Absorb.absorptionCutoff inputs coefficient))
    cutoff≤n

scaledAbsorption :
  ∀ {ratio largerRatio}
    (inputs : Absorb.BishopStrictRatioPair ratio largerRatio)
    coefficient lowerDegree n →
  Absorb.absorptionCutoff inputs coefficient ≤ n →
  BishopReal._≤_
    (BishopReal._*_
      (natPowerReal lowerDegree n)
      (BishopReal._*_
        (NatReal.natReal coefficient)
        ratio))
    (BishopReal._*_
      (natPowerReal (suc lowerDegree) n)
      (Absorb.ratioGap inputs))
scaledAbsorption inputs coefficient lowerDegree n cutoff≤n =
  let
    raw =
      BishopP.*-monoˡ-≤-nonNeg
        (Absorb.eventualLinearGapAbsorption
          inputs coefficient n cutoff≤n)
        (natPowerRealNonnegative lowerDegree n)

    normalize =
      let open BishopP.ℝ-Solver
          nR = NatReal.natReal n
          lower = natPowerReal lowerDegree n
          gap = Absorb.ratioGap inputs
      in
      BishopP.≃-trans
        (solve 3
          (λ lower′ n′ gap′ →
            lower′ ⊗ (n′ ⊗ gap′)
            ⊜ (n′ ⊗ lower′) ⊗ gap′)
          BishopP.≃-refl lower nR gap)
        (BishopP.*-congʳ
          (BishopP.≃-symm
            (natPowerSuccessorExponent lowerDegree n)))
  in
  BishopP.≤-respʳ-≃ normalize raw

degreeFourCoefficientRatio :
  ∀ {ratio largerRatio}
    (inputs : Absorb.BishopStrictRatioPair ratio largerRatio)
    n →
  degreeFourCutoff inputs ≤ n →
  BishopReal._≤_
    (BishopReal._*_
      (natPowerReal 4 (suc n))
      ratio)
    (BishopReal._*_
      (natPowerReal 4 n)
      largerRatio)
degreeFourCoefficientRatio {ratio} {largerRatio} inputs n cutoff≤n =
  let
    nPositive = cutoffPositive inputs 15 n cutoff≤n
    absorptionIndex =
      absorptionCutoffBelow inputs 15 n cutoff≤n

    scaledEnvelope =
      BishopP.*-monoʳ-≤-nonNeg
        (embeddedDegreeFourEnvelope n nPositive)
        (BishopP.0≤x⇒nonNegx
          (Absorb.ratioNonnegative inputs))

    splitRight :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._+_
            (natPowerReal 4 n)
            (BishopReal._*_
              (NatReal.natReal 15)
              (natPowerReal 3 n)))
          ratio)
        (BishopReal._+_
          (BishopReal._*_
            (natPowerReal 4 n) ratio)
          (BishopReal._*_
            (natPowerReal 3 n)
            (BishopReal._*_
              (NatReal.natReal 15) ratio)))
    splitRight =
      let open BishopP.ℝ-Solver
      in solve 4
        (λ n4 n3 c r →
          (n4 ⊕ (c ⊗ n3)) ⊗ r
          ⊜ (n4 ⊗ r) ⊕ (n3 ⊗ (c ⊗ r)))
        BishopP.≃-refl
        (natPowerReal 4 n)
        (natPowerReal 3 n)
        (NatReal.natReal 15)
        ratio

    afterSplit =
      BishopP.≤-respʳ-≃ splitRight scaledEnvelope

    absorbed =
      scaledAbsorption inputs 15 3 n absorptionIndex

    afterAbsorption =
      BishopP.≤-trans
        afterSplit
        (BishopP.+-mono-≤
          (BishopP.≤-refl {x =
            BishopReal._*_
              (natPowerReal 4 n) ratio})
          absorbed)

    finalMeaning :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._*_
            (natPowerReal 4 n) ratio)
          (BishopReal._*_
            (natPowerReal 4 n)
            (Absorb.ratioGap inputs)))
        (BishopReal._*_
          (natPowerReal 4 n)
          largerRatio)
    finalMeaning =
      let open BishopP.ℝ-Solver
      in solve 3
        (λ n4 r s →
          (n4 ⊗ r) ⊕ (n4 ⊗ (s ⊖ r))
          ⊜ n4 ⊗ s)
        BishopP.≃-refl
        (natPowerReal 4 n)
        ratio largerRatio
  in
  BishopP.≤-respʳ-≃
    finalMeaning
    afterAbsorption

degreeSixCoefficientRatio :
  ∀ {ratio largerRatio}
    (inputs : Absorb.BishopStrictRatioPair ratio largerRatio)
    n →
  degreeSixCutoff inputs ≤ n →
  BishopReal._≤_
    (BishopReal._*_
      (natPowerReal 6 (suc n))
      ratio)
    (BishopReal._*_
      (natPowerReal 6 n)
      largerRatio)
degreeSixCoefficientRatio {ratio} {largerRatio} inputs n cutoff≤n =
  let
    nPositive = cutoffPositive inputs 63 n cutoff≤n
    absorptionIndex =
      absorptionCutoffBelow inputs 63 n cutoff≤n

    scaledEnvelope =
      BishopP.*-monoʳ-≤-nonNeg
        (embeddedDegreeSixEnvelope n nPositive)
        (BishopP.0≤x⇒nonNegx
          (Absorb.ratioNonnegative inputs))

    splitRight :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._+_
            (natPowerReal 6 n)
            (BishopReal._*_
              (NatReal.natReal 63)
              (natPowerReal 5 n)))
          ratio)
        (BishopReal._+_
          (BishopReal._*_
            (natPowerReal 6 n) ratio)
          (BishopReal._*_
            (natPowerReal 5 n)
            (BishopReal._*_
              (NatReal.natReal 63) ratio)))
    splitRight =
      let open BishopP.ℝ-Solver
      in solve 4
        (λ n6 n5 c r →
          (n6 ⊕ (c ⊗ n5)) ⊗ r
          ⊜ (n6 ⊗ r) ⊕ (n5 ⊗ (c ⊗ r)))
        BishopP.≃-refl
        (natPowerReal 6 n)
        (natPowerReal 5 n)
        (NatReal.natReal 63)
        ratio

    afterSplit =
      BishopP.≤-respʳ-≃ splitRight scaledEnvelope

    absorbed =
      scaledAbsorption inputs 63 5 n absorptionIndex

    afterAbsorption =
      BishopP.≤-trans
        afterSplit
        (BishopP.+-mono-≤
          (BishopP.≤-refl {x =
            BishopReal._*_
              (natPowerReal 6 n) ratio})
          absorbed)

    finalMeaning :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._*_
            (natPowerReal 6 n) ratio)
          (BishopReal._*_
            (natPowerReal 6 n)
            (Absorb.ratioGap inputs)))
        (BishopReal._*_
          (natPowerReal 6 n)
          largerRatio)
    finalMeaning =
      let open BishopP.ℝ-Solver
      in solve 3
        (λ n6 r s →
          (n6 ⊗ r) ⊕ (n6 ⊗ (s ⊖ r))
          ⊜ n6 ⊗ s)
        BishopP.≃-refl
        (natPowerReal 6 n)
        ratio largerRatio
  in
  BishopP.≤-respʳ-≃
    finalMeaning
    afterAbsorption

degreeFourTerm : BishopReal.ℝ → Nat → BishopReal.ℝ
degreeFourTerm ratio n =
  BishopReal._*_
    (natPowerReal 4 n)
    (BishopReal.pow ratio n)

degreeSixTerm : BishopReal.ℝ → Nat → BishopReal.ℝ
degreeSixTerm ratio n =
  BishopReal._*_
    (natPowerReal 6 n)
    (BishopReal.pow ratio n)

ratioAsUnitInterval :
  ∀ {ratio largerRatio} →
  Absorb.BishopStrictRatioPair ratio largerRatio →
  DegreeOne.BishopUnitIntervalRatio ratio
ratioAsUnitInterval inputs = record
  { ratioNonnegative = Absorb.ratioNonnegative inputs
  ; ratioBelowOne =
      BishopP.<-trans
        (Absorb.ratioBelowLargerRatio inputs)
        (Absorb.largerRatioBelowOne inputs)
  }

degreeFourTermNonnegative :
  ∀ {ratio largerRatio}
    (inputs : Absorb.BishopStrictRatioPair ratio largerRatio)
    n →
  BishopReal.NonNegative (degreeFourTerm ratio n)
degreeFourTermNonnegative inputs n =
  BishopP.nonNegx,y⇒nonNegx*y
    (natPowerRealNonnegative 4 n)
    (DegreeOne.ratioPowerNonnegative
      (ratioAsUnitInterval inputs) n)

degreeSixTermNonnegative :
  ∀ {ratio largerRatio}
    (inputs : Absorb.BishopStrictRatioPair ratio largerRatio)
    n →
  BishopReal.NonNegative (degreeSixTerm ratio n)
degreeSixTermNonnegative inputs n =
  BishopP.nonNegx,y⇒nonNegx*y
    (natPowerRealNonnegative 6 n)
    (DegreeOne.ratioPowerNonnegative
      (ratioAsUnitInterval inputs) n)

degreeFourTermRatio :
  ∀ {ratio largerRatio}
    (inputs : Absorb.BishopStrictRatioPair ratio largerRatio)
    n →
  degreeFourCutoff inputs ≤ n →
  BishopReal._≤_
    (degreeFourTerm ratio (suc n))
    (BishopReal._*_
      largerRatio
      (degreeFourTerm ratio n))
degreeFourTermRatio {ratio} {largerRatio} inputs n cutoff≤n =
  let
    powerNN =
      DegreeOne.ratioPowerNonnegative
        (ratioAsUnitInterval inputs) n

    scaled =
      BishopP.*-monoʳ-≤-nonNeg
        (degreeFourCoefficientRatio inputs n cutoff≤n)
        powerNN

    leftMeaning :
      BishopReal._≃_
        (degreeFourTerm ratio (suc n))
        (BishopReal._*_
          (BishopReal._*_
            (natPowerReal 4 (suc n))
            ratio)
          (BishopReal.pow ratio n))
    leftMeaning =
      let open BishopP.ℝ-Solver
      in solve 3
        (λ nextPoly r oldPower →
          nextPoly ⊗ (oldPower ⊗ r)
          ⊜ (nextPoly ⊗ r) ⊗ oldPower)
        BishopP.≃-refl
        (natPowerReal 4 (suc n))
        ratio
        (BishopReal.pow ratio n)

    rightMeaning :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._*_
            (natPowerReal 4 n)
            largerRatio)
          (BishopReal.pow ratio n))
        (BishopReal._*_
          largerRatio
          (degreeFourTerm ratio n))
    rightMeaning =
      let open BishopP.ℝ-Solver
      in solve 3
        (λ poly s oldPower →
          (poly ⊗ s) ⊗ oldPower
          ⊜ s ⊗ (poly ⊗ oldPower))
        BishopP.≃-refl
        (natPowerReal 4 n)
        largerRatio
        (BishopReal.pow ratio n)
  in
  BishopP.≤-respʳ-≃ rightMeaning
    (BishopP.≤-respˡ-≃ leftMeaning scaled)

degreeSixTermRatio :
  ∀ {ratio largerRatio}
    (inputs : Absorb.BishopStrictRatioPair ratio largerRatio)
    n →
  degreeSixCutoff inputs ≤ n →
  BishopReal._≤_
    (degreeSixTerm ratio (suc n))
    (BishopReal._*_
      largerRatio
      (degreeSixTerm ratio n))
degreeSixTermRatio {ratio} {largerRatio} inputs n cutoff≤n =
  let
    powerNN =
      DegreeOne.ratioPowerNonnegative
        (ratioAsUnitInterval inputs) n

    scaled =
      BishopP.*-monoʳ-≤-nonNeg
        (degreeSixCoefficientRatio inputs n cutoff≤n)
        powerNN

    leftMeaning :
      BishopReal._≃_
        (degreeSixTerm ratio (suc n))
        (BishopReal._*_
          (BishopReal._*_
            (natPowerReal 6 (suc n))
            ratio)
          (BishopReal.pow ratio n))
    leftMeaning =
      let open BishopP.ℝ-Solver
      in solve 3
        (λ nextPoly r oldPower →
          nextPoly ⊗ (oldPower ⊗ r)
          ⊜ (nextPoly ⊗ r) ⊗ oldPower)
        BishopP.≃-refl
        (natPowerReal 6 (suc n))
        ratio
        (BishopReal.pow ratio n)

    rightMeaning :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._*_
            (natPowerReal 6 n)
            largerRatio)
          (BishopReal.pow ratio n))
        (BishopReal._*_
          largerRatio
          (degreeSixTerm ratio n))
    rightMeaning =
      let open BishopP.ℝ-Solver
      in solve 3
        (λ poly s oldPower →
          (poly ⊗ s) ⊗ oldPower
          ⊜ s ⊗ (poly ⊗ oldPower))
        BishopP.≃-refl
        (natPowerReal 6 n)
        largerRatio
        (BishopReal.pow ratio n)
  in
  BishopP.≤-respʳ-≃ rightMeaning
    (BishopP.≤-respˡ-≃ leftMeaning scaled)

degreeFourAbsoluteTerm :
  ∀ {ratio largerRatio}
    (inputs : Absorb.BishopStrictRatioPair ratio largerRatio)
    n →
  BishopReal._≃_
    (BishopReal.∣ degreeFourTerm ratio n ∣)
    (degreeFourTerm ratio n)
degreeFourAbsoluteTerm inputs n =
  BishopP.nonNegx⇒∣x∣≃x
    (degreeFourTermNonnegative inputs n)

degreeSixAbsoluteTerm :
  ∀ {ratio largerRatio}
    (inputs : Absorb.BishopStrictRatioPair ratio largerRatio)
    n →
  BishopReal._≃_
    (BishopReal.∣ degreeSixTerm ratio n ∣)
    (degreeSixTerm ratio n)
degreeSixAbsoluteTerm inputs n =
  BishopP.nonNegx⇒∣x∣≃x
    (degreeSixTermNonnegative inputs n)

degreeFourSeriesConvergent :
  ∀ {ratio largerRatio}
    (inputs : Absorb.BishopStrictRatioPair ratio largerRatio) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf (degreeFourTerm ratio))
degreeFourSeriesConvergent {ratio} {largerRatio} inputs =
  let
    largerPositive =
      BishopP.≤-<-trans
        (Absorb.ratioNonnegative inputs)
        (Absorb.ratioBelowLargerRatio inputs)

    cutoff = degreeFourCutoff inputs
  in
  BishopSequence.proposition-3-6-1
    (largerPositive , Absorb.largerRatioBelowOne inputs)
    (cutoff , λ n successorCutoff≤n →
      let cutoff≤n =
            NatP.≤-trans
              (NatP.n≤1+n cutoff)
              successorCutoff≤n
          raw = degreeFourTermRatio inputs n cutoff≤n
      in
      BishopP.≤-respʳ-≃
        (BishopP.*-cong
          BishopP.≃-refl
          (BishopP.≃-symm
            (degreeFourAbsoluteTerm inputs n)))
        (BishopP.≤-respˡ-≃
          (degreeFourAbsoluteTerm inputs (suc n))
          raw))

degreeSixSeriesConvergent :
  ∀ {ratio largerRatio}
    (inputs : Absorb.BishopStrictRatioPair ratio largerRatio) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf (degreeSixTerm ratio))
degreeSixSeriesConvergent {ratio} {largerRatio} inputs =
  let
    largerPositive =
      BishopP.≤-<-trans
        (Absorb.ratioNonnegative inputs)
        (Absorb.ratioBelowLargerRatio inputs)

    cutoff = degreeSixCutoff inputs
  in
  BishopSequence.proposition-3-6-1
    (largerPositive , Absorb.largerRatioBelowOne inputs)
    (cutoff , λ n successorCutoff≤n →
      let cutoff≤n =
            NatP.≤-trans
              (NatP.n≤1+n cutoff)
              successorCutoff≤n
          raw = degreeSixTermRatio inputs n cutoff≤n
      in
      BishopP.≤-respʳ-≃
        (BishopP.*-cong
          BishopP.≃-refl
          (BishopP.≃-symm
            (degreeSixAbsoluteTerm inputs n)))
        (BishopP.≤-respˡ-≃
          (degreeSixAbsoluteTerm inputs (suc n))
          raw))

degreeFourAbsoluteConvergence :
  ∀ {ratio largerRatio}
    (inputs : Absorb.BishopStrictRatioPair ratio largerRatio) →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (degreeFourTerm ratio)
degreeFourAbsoluteConvergence inputs =
  let
    convergent = degreeFourSeriesConvergent inputs
    limit = proj₁ convergent
    partials =
      SeriesExt.seriesPartialSumsCongruent
        (degreeFourAbsoluteTerm inputs)
  in
  limit ,
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count-1) →
      BishopP.≃-symm (partials (suc count-1))})
    convergent

degreeSixAbsoluteConvergence :
  ∀ {ratio largerRatio}
    (inputs : Absorb.BishopStrictRatioPair ratio largerRatio) →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (degreeSixTerm ratio)
degreeSixAbsoluteConvergence inputs =
  let
    convergent = degreeSixSeriesConvergent inputs
    limit = proj₁ convergent
    partials =
      SeriesExt.seriesPartialSumsCongruent
        (degreeSixAbsoluteTerm inputs)
  in
  limit ,
  BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ {(suc count-1) →
      BishopP.≃-symm (partials (suc count-1))})
    convergent


------------------------------------------------------------------------
-- Canonical specialization: no explicit larger-ratio witness remains.

degreeFourUnitRatioAbsoluteConvergence :
  ∀ {ratio} →
  DegreeOne.BishopUnitIntervalRatio ratio →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (degreeFourTerm ratio)
degreeFourUnitRatioAbsoluteConvergence inputs =
  degreeFourAbsoluteConvergence
    (Midpoint.canonicalMidpointRatioPair inputs)

degreeSixUnitRatioAbsoluteConvergence :
  ∀ {ratio} →
  DegreeOne.BishopUnitIntervalRatio ratio →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (degreeSixTerm ratio)
degreeSixUnitRatioAbsoluteConvergence inputs =
  degreeSixAbsoluteConvergence
    (Midpoint.canonicalMidpointRatioPair inputs)
