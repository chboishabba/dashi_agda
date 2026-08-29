module DASHI.Physics.YangMills.BalabanYM4RowACanonicalSmallCouplingChoiceExact where

------------------------------------------------------------------------
-- ROW A: POSITIVE FLOOR + FINITE SOURCE CONSTANTS -> CANONICAL SMALL COUPLING
--
-- The preceding Row-A reduction shows that both positivity and shooting are
-- paid by a single inequality
--
--                  (C + L) gamma < b,
--
-- where b>0 is the literal Gaussian floor and C,L are finite nonnegative
-- interaction/sensitivity constants.  This file removes the last purely scalar
-- existential choice of gamma.
--
-- Put S=C+L and choose
--
--              gamma := b / (2 (S+1)).
--
-- Then S < 2(S+1), so S gamma < b.  All arithmetic is over exact rationals;
-- no floating-point search and no imported asymptotic small-o statement is used.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; Positive; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quot
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact as Cubic

record FiniteRowASourceConstants : Set where
  field
    gaussianFloor interactionConstant derivativeBound : ℚ
    gaussianFloorPositive : 0ℚ < gaussianFloor
    interactionConstantNonnegative : 0ℚ ≤ interactionConstant
    derivativeBoundNonnegative : 0ℚ ≤ derivativeBound

open FiniteRowASourceConstants public

sourceSlope : FiniteRowASourceConstants → ℚ
sourceSlope dataSet = interactionConstant dataSet + derivativeBound dataSet

sourceSlopeNonnegative :
  (dataSet : FiniteRowASourceConstants) → 0ℚ ≤ sourceSlope dataSet
sourceSlopeNonnegative dataSet =
  ℚP.+-mono-≤
    (interactionConstantNonnegative dataSet)
    (derivativeBoundNonnegative dataSet)

canonicalDenominator : FiniteRowASourceConstants → ℚ
canonicalDenominator dataSet =
  Cubic.twoℚ * (sourceSlope dataSet + 1ℚ)

sourceSlopePlusOnePositive :
  (dataSet : FiniteRowASourceConstants) →
  0ℚ < sourceSlope dataSet + 1ℚ
sourceSlopePlusOnePositive dataSet =
  let
    slopeNN = sourceSlopeNonnegative dataSet
    onePositive : 0ℚ < 1ℚ
    onePositive = ℚP.positive⁻¹ 1ℚ
  in
  ℚP.≤-<-trans slopeNN
    (subst
      (λ right → sourceSlope dataSet < right)
      (ℚRing.solve-∀ (sourceSlope dataSet))
      (ℚP.+-monoʳ-< (sourceSlope dataSet) onePositive))

canonicalDenominatorPositive :
  (dataSet : FiniteRowASourceConstants) →
  0ℚ < canonicalDenominator dataSet
canonicalDenominatorPositive dataSet =
  let
    twoPositive : 0ℚ < Cubic.twoℚ
    twoPositive = ℚP.positive⁻¹ Cubic.twoℚ

    instance
      twoPos : Positive Cubic.twoℚ
      twoPos = ℚ.positive twoPositive
      tailPos : Positive (sourceSlope dataSet + 1ℚ)
      tailPos = ℚ.positive (sourceSlopePlusOnePositive dataSet)
  in
  ℚP.positive⁻¹
    (Cubic.twoℚ * (sourceSlope dataSet + 1ℚ))

canonicalGamma : FiniteRowASourceConstants → ℚ
canonicalGamma dataSet =
  Quot.dividePositive
    (gaussianFloor dataSet)
    (canonicalDenominator dataSet)
    (canonicalDenominatorPositive dataSet)

canonicalGammaPositive :
  (dataSet : FiniteRowASourceConstants) → 0ℚ < canonicalGamma dataSet
canonicalGammaPositive dataSet =
  let
    b = gaussianFloor dataSet
    denominator = canonicalDenominator dataSet
    denominatorPositive = canonicalDenominatorPositive dataSet
    reciprocalPositive =
      Quot.positiveReciprocalPositive denominator denominatorPositive

    instance
      bPositive : Positive b
      bPositive = ℚ.positive (gaussianFloorPositive dataSet)
      reciprocalPos : Positive (Quot.positiveReciprocal denominator denominatorPositive)
      reciprocalPos = ℚ.positive reciprocalPositive
  in
  ℚP.positive⁻¹
    (b * Quot.positiveReciprocal denominator denominatorPositive)

sourceSlopeStrictlyBelowDenominator :
  (dataSet : FiniteRowASourceConstants) →
  sourceSlope dataSet < canonicalDenominator dataSet
sourceSlopeStrictlyBelowDenominator dataSet =
  let
    S = sourceSlope dataSet
    SNN = sourceSlopeNonnegative dataSet

    first : S < S + 1ℚ
    first =
      let onePositive : 0ℚ < 1ℚ
          onePositive = ℚP.positive⁻¹ 1ℚ
      in subst
        (λ left → left < S + 1ℚ)
        (ℚP.+-identityʳ S)
        (ℚP.+-monoʳ-< S onePositive)

    tailPositive = sourceSlopePlusOnePositive dataSet

    tailBelowTwiceTail :
      S + 1ℚ < Cubic.twoℚ * (S + 1ℚ)
    tailBelowTwiceTail =
      let
        oneBelowTwo : 1ℚ < Cubic.twoℚ
        oneBelowTwo = ℚP.<-respˡ-≡ (ℚP.*-identityˡ 1ℚ) (ℚP.positive⁻¹ 1ℚ)
      in
      let instance tailPos : Positive (S + 1ℚ); tailPos = ℚ.positive tailPositive
      in subst
        (λ left → left < Cubic.twoℚ * (S + 1ℚ))
        (ℚP.*-identityˡ (S + 1ℚ))
        (ℚP.*-monoˡ-<-pos (S + 1ℚ) oneBelowTwo)
  in
  ℚP.<-trans first tailBelowTwiceTail

sourceSlopeTimesCanonicalReciprocalBelowOne :
  (dataSet : FiniteRowASourceConstants) →
  sourceSlope dataSet
    * Quot.positiveReciprocal
        (canonicalDenominator dataSet)
        (canonicalDenominatorPositive dataSet)
  < 1ℚ
sourceSlopeTimesCanonicalReciprocalBelowOne dataSet =
  let
    D = canonicalDenominator dataSet
    Dpos = canonicalDenominatorPositive dataSet
    reciprocal = Quot.positiveReciprocal D Dpos
    reciprocalPos = Quot.positiveReciprocalPositive D Dpos

    scaled : sourceSlope dataSet * reciprocal < D * reciprocal
    scaled =
      let instance rPos : Positive reciprocal; rPos = ℚ.positive reciprocalPos
      in ℚP.*-monoʳ-<-pos reciprocal
        (sourceSlopeStrictlyBelowDenominator dataSet)
  in
  subst
    (λ right → sourceSlope dataSet * reciprocal < right)
    (Quot.positiveReciprocalRightInverse D Dpos)
    scaled

canonicalGammaPaysCombinedSmallness :
  (dataSet : FiniteRowASourceConstants) →
  sourceSlope dataSet * canonicalGamma dataSet
  < gaussianFloor dataSet
canonicalGammaPaysCombinedSmallness dataSet =
  let
    S = sourceSlope dataSet
    b = gaussianFloor dataSet
    D = canonicalDenominator dataSet
    Dpos = canonicalDenominatorPositive dataSet
    reciprocal = Quot.positiveReciprocal D Dpos

    ratioBelowOne : S * reciprocal < 1ℚ
    ratioBelowOne = sourceSlopeTimesCanonicalReciprocalBelowOne dataSet

    instance
      bPositive : Positive b
      bPositive = ℚ.positive (gaussianFloorPositive dataSet)

    scaled : b * (S * reciprocal) < b * 1ℚ
    scaled = ℚP.*-monoʳ-<-pos b ratioBelowOne
  in
  subst
    (λ left → left < b)
    (ℚRing.solve-∀ b S reciprocal)
    (subst
      (λ right → b * (S * reciprocal) < right)
      (ℚP.*-identityʳ b)
      scaled)

rowACanonicalSmallCouplingChoiceLevel : ProofLevel
rowACanonicalSmallCouplingChoiceLevel = machineChecked

rowACanonicalGammaPositiveLevel : ProofLevel
rowACanonicalGammaPositiveLevel = machineChecked

rowACanonicalGammaPaysCombinedGateLevel : ProofLevel
rowACanonicalGammaPaysCombinedGateLevel = machineChecked

-- Physical Row-A seam after this theorem: derive the literal positive Gaussian
-- floor b and finite nonnegative source constants C,L on the same source-native
-- trajectory.  The existence of a sufficiently small rational coupling cap is
-- no longer an independent analytic or numerical obligation.
literalRowAFiniteSourceConstantsLevel : ProofLevel
literalRowAFiniteSourceConstantsLevel = conditional
