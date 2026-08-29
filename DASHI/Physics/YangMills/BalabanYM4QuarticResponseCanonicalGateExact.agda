{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalGateExact where

------------------------------------------------------------------------
-- ROW A BIDI COLLAPSE: QUARTIC HISTORY INJECTION -> ONE SMALL-COUPLING GATE
--
-- Combine the forward quartic source budget with the backward shooting margin.
-- Let
--
--   m = b - C gamma,
--   s_j <= D g_j^4,
--   response coefficient = R,
--   gamma_tube <= gamma.
--
-- The cubic telescope and response-kernel potential give
--
--   q_history <= 2 R [D gamma (2 gamma_tube / m)].
--
-- Multiplying by the SAME positive shooting margin cancels the reciprocal:
--
--   m q_history <= 4 R D gamma gamma_tube
--                 <= 4 R D gamma^2.
--
-- Therefore, when 0 <= gamma <= 1, the honest augmented shooting gate follows
-- from the single LINEARIZED source smallness condition
--
--            (C + L + 4 R D) gamma < b.
--
-- This is the bidirectional payoff: backwards we only pay the actual contraction
-- margin; forwards the already-proved positive drift converts quartic history
-- injection into a quadratic debt, which is absorbed by the same small-coupling
-- choice.  No separate cumulative-q theorem or arbitrary S_total remains.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _≤_; _<_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quot
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanYM4BetaResponseKernelSummationExact as Kernel
import DASHI.Physics.YangMills.BalabanYM4QuarticSourceSensitivityBudgetExact as Quartic
import DASHI.Physics.YangMills.BalabanYM4RowAAugmentedShootingGateExact as Aug

fourℚ : ℚ
fourℚ = Geo.twoℚ * Geo.twoℚ

mulNN : ∀ {left right : ℚ} → 0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
mulNN {left} {right} leftNN rightNN =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = ℚ.nonNegative leftNN
      rightNonnegative : NonNegative right
      rightNonnegative = ℚ.nonNegative rightNN
  in
  ℚP.nonNegative⁻¹ (left * right)

record QuarticResponseCanonicalGate
    {kernel : Kernel.GeometricBetaResponseKernel}
    {cutoff : Agda.Builtin.Nat.Nat}
    (quartic : Quartic.QuarticSourceSensitivityData kernel cutoff) : Set₁ where
  field
    gaussianFloor interactionConstant localDerivative : ℚ

    interactionConstantNonnegative : 0ℚ ≤ interactionConstant
    localDerivativeNonnegative : 0ℚ ≤ localDerivative

    couplingCapAtMostOne : Quartic.couplingCap quartic ≤ 1ℚ
    tubeBelowCouplingCap :
      Direct.tubeWidth (Quartic.direct quartic) ≤ Quartic.couplingCap quartic

    marginExact :
      Direct.marginConstant (Quartic.direct quartic)
      ≡ gaussianFloor
          - interactionConstant * Quartic.couplingCap quartic

    derivativeExact :
      Direct.derivativeBound (Quartic.direct quartic) ≡ localDerivative

    linearizedCombinedSmallness :
      (interactionConstant + localDerivative
        + fourℚ * Kernel.responseCoefficient kernel
            * Quartic.sourceCoefficient quartic)
        * Quartic.couplingCap quartic
      < gaussianFloor

open QuarticResponseCanonicalGate public

quarticResponseHistoryConstant :
  ∀ {kernel cutoff}
    (quartic : Quartic.QuarticSourceSensitivityData kernel cutoff) → ℚ
quarticResponseHistoryConstant {kernel} quartic =
  Geo.twoℚ * Kernel.responseCoefficient kernel
    * Quartic.quarticSourceTotal quartic

quarticResponseHistoryConstantNonnegative :
  ∀ {kernel cutoff}
    (quartic : Quartic.QuarticSourceSensitivityData kernel cutoff) →
  0ℚ ≤ quarticResponseHistoryConstant quartic
quarticResponseHistoryConstantNonnegative {kernel} quartic =
  let
    twoNN = ℚP.+-mono-≤ Geo.oneNonnegativeProof Geo.oneNonnegativeProof
    firstNN = mulNN twoNN (Kernel.responseCoefficientNonnegative kernel)
  in
  mulNN firstNN (Quartic.quarticSourceTotalNonnegative quartic)

marginTimesHistoryExact :
  ∀ {kernel cutoff}
    (quartic : Quartic.QuarticSourceSensitivityData kernel cutoff) →
  Direct.marginConstant (Quartic.direct quartic)
    * quarticResponseHistoryConstant quartic
  ≡ fourℚ * Kernel.responseCoefficient kernel
      * Quartic.sourceCoefficient quartic
      * Quartic.couplingCap quartic
      * Direct.tubeWidth (Quartic.direct quartic)
marginTimesHistoryExact {kernel} quartic =
  let
    margin = Direct.marginConstant (Quartic.direct quartic)
    inv = Quartic.marginReciprocal quartic
    R = Kernel.responseCoefficient kernel
    D = Quartic.sourceCoefficient quartic
    gamma = Quartic.couplingCap quartic
    tube = Direct.tubeWidth (Quartic.direct quartic)

    reciprocal : margin * inv ≡ 1ℚ
    reciprocal = Quot.positiveReciprocalRightInverse
      margin (Direct.marginPositive (Quartic.direct quartic))
  in
  trans
    (ℚRing.solve-∀ margin inv R D gamma tube Geo.twoℚ)
    (trans
      (cong (λ selected →
        fourℚ * R * D * gamma * (selected * tube)) reciprocal)
      (ℚRing.solve-∀ fourℚ R D gamma tube))

marginTimesHistoryBelowQuadratic :
  ∀ {kernel cutoff}
    {quartic : Quartic.QuarticSourceSensitivityData kernel cutoff}
    (dataSet : QuarticResponseCanonicalGate quartic) →
  Direct.marginConstant (Quartic.direct quartic)
    * quarticResponseHistoryConstant quartic
  ≤ fourℚ * Kernel.responseCoefficient kernel
      * Quartic.sourceCoefficient quartic
      * (Quartic.couplingCap quartic * Quartic.couplingCap quartic)
marginTimesHistoryBelowQuadratic {kernel} {quartic = quartic} dataSet =
  let
    R = Kernel.responseCoefficient kernel
    D = Quartic.sourceCoefficient quartic
    gamma = Quartic.couplingCap quartic
    tube = Direct.tubeWidth (Quartic.direct quartic)

    fourNN : 0ℚ ≤ fourℚ
    fourNN = mulNN
      (ℚP.+-mono-≤ Geo.oneNonnegativeProof Geo.oneNonnegativeProof)
      (ℚP.+-mono-≤ Geo.oneNonnegativeProof Geo.oneNonnegativeProof)
    coefficientNN : 0ℚ ≤ fourℚ * R * D * gamma
    coefficientNN = mulNN
      (mulNN (mulNN fourNN (Kernel.responseCoefficientNonnegative kernel))
        (Quartic.sourceCoefficientNonnegative quartic))
      (Quartic.couplingCapNonnegative quartic)

    scaled = Norm.scaleNonnegative
      (fourℚ * R * D * gamma)
      coefficientNN
      (tubeBelowCouplingCap dataSet)
  in
  subst
    (λ left → left ≤ fourℚ * R * D * (gamma * gamma))
    (marginTimesHistoryExact quartic)
    (subst
      (λ right → fourℚ * R * D * gamma * tube ≤ right)
      (ℚRing.solve-∀ fourℚ R D gamma)
      scaled)

gammaSquareBelowGamma :
  ∀ {kernel cutoff}
    {quartic : Quartic.QuarticSourceSensitivityData kernel cutoff}
    (dataSet : QuarticResponseCanonicalGate quartic) →
  Quartic.couplingCap quartic * Quartic.couplingCap quartic
  ≤ Quartic.couplingCap quartic
gammaSquareBelowGamma {quartic = quartic} dataSet =
  let
    gamma = Quartic.couplingCap quartic
    scaled = Norm.scaleNonnegative gamma
      (Quartic.couplingCapNonnegative quartic)
      (couplingCapAtMostOne dataSet)
  in
  subst
    (λ right → gamma * gamma ≤ right)
    (ℚP.*-identityʳ gamma)
    scaled

quadraticHistoryBelowLinearHistory :
  ∀ {kernel cutoff}
    {quartic : Quartic.QuarticSourceSensitivityData kernel cutoff}
    (dataSet : QuarticResponseCanonicalGate quartic) →
  fourℚ * Kernel.responseCoefficient kernel
      * Quartic.sourceCoefficient quartic
      * (Quartic.couplingCap quartic * Quartic.couplingCap quartic)
  ≤ (fourℚ * Kernel.responseCoefficient kernel
      * Quartic.sourceCoefficient quartic)
      * Quartic.couplingCap quartic
quadraticHistoryBelowLinearHistory {kernel} {quartic = quartic} dataSet =
  let
    fourNN : 0ℚ ≤ fourℚ
    fourNN = mulNN
      (ℚP.+-mono-≤ Geo.oneNonnegativeProof Geo.oneNonnegativeProof)
      (ℚP.+-mono-≤ Geo.oneNonnegativeProof Geo.oneNonnegativeProof)
    scaleNN = mulNN
      (mulNN fourNN (Kernel.responseCoefficientNonnegative kernel))
      (Quartic.sourceCoefficientNonnegative quartic)
  in
  Norm.scaleNonnegative
    (fourℚ * Kernel.responseCoefficient kernel
      * Quartic.sourceCoefficient quartic)
    scaleNN
    (gammaSquareBelowGamma dataSet)

localPlusHistoryBelowLinearBudget :
  ∀ {kernel cutoff}
    {quartic : Quartic.QuarticSourceSensitivityData kernel cutoff}
    (dataSet : QuarticResponseCanonicalGate quartic) →
  Direct.derivativeBound (Quartic.direct quartic)
      * Direct.tubeWidth (Quartic.direct quartic)
    + Direct.marginConstant (Quartic.direct quartic)
      * quarticResponseHistoryConstant quartic
  ≤ (localDerivative dataSet
      + fourℚ * Kernel.responseCoefficient kernel
          * Quartic.sourceCoefficient quartic)
      * Quartic.couplingCap quartic
localPlusHistoryBelowLinearBudget {kernel} {quartic = quartic} dataSet =
  let
    L = localDerivative dataSet
    gamma = Quartic.couplingCap quartic

    local :
      Direct.derivativeBound (Quartic.direct quartic)
        * Direct.tubeWidth (Quartic.direct quartic)
      ≤ L * gamma
    local = subst
      (λ left → left * Direct.tubeWidth (Quartic.direct quartic) ≤ L * gamma)
      (derivativeExact dataSet)
      (Norm.scaleNonnegative L
        (localDerivativeNonnegative dataSet)
        (tubeBelowCouplingCap dataSet))

    history = ℚP.≤-trans
      (marginTimesHistoryBelowQuadratic dataSet)
      (quadraticHistoryBelowLinearHistory dataSet)

    added = ℚP.+-mono-≤ local history
  in
  subst
    (λ right →
      Direct.derivativeBound (Quartic.direct quartic)
          * Direct.tubeWidth (Quartic.direct quartic)
        + Direct.marginConstant (Quartic.direct quartic)
          * quarticResponseHistoryConstant quartic
      ≤ right)
    (ℚRing.solve-∀
      L fourℚ
      (Kernel.responseCoefficient kernel)
      (Quartic.sourceCoefficient quartic)
      gamma)
    added

linearBudgetBelowMargin :
  ∀ {kernel cutoff}
    {quartic : Quartic.QuarticSourceSensitivityData kernel cutoff}
    (dataSet : QuarticResponseCanonicalGate quartic) →
  (localDerivative dataSet
      + fourℚ * Kernel.responseCoefficient kernel
          * Quartic.sourceCoefficient quartic)
      * Quartic.couplingCap quartic
  < Direct.marginConstant (Quartic.direct quartic)
linearBudgetBelowMargin {kernel} {quartic = quartic} dataSet =
  let
    C = interactionConstant dataSet
    L = localDerivative dataSet
    E = fourℚ * Kernel.responseCoefficient kernel
      * Quartic.sourceCoefficient quartic
    gamma = Quartic.couplingCap quartic
    b = gaussianFloor dataSet

    combined = linearizedCombinedSmallness dataSet
    shifted = ℚP.+-monoʳ-< (-(C * gamma)) combined
  in
  subst
    (λ left → left < Direct.marginConstant (Quartic.direct quartic))
    (ℚRing.solve-∀ C L E gamma)
    (subst
      (λ right →
        ((C + L + E) * gamma) + (-(C * gamma)) < right)
      (sym (marginExact dataSet))
      shifted)

augmentedQuarticResponseGate :
  ∀ {kernel cutoff}
    {quartic : Quartic.QuarticSourceSensitivityData kernel cutoff}
    (dataSet : QuarticResponseCanonicalGate quartic) →
  Direct.derivativeBound (Quartic.direct quartic)
      * Direct.tubeWidth (Quartic.direct quartic)
    + Direct.marginConstant (Quartic.direct quartic)
      * quarticResponseHistoryConstant quartic
  < Direct.marginConstant (Quartic.direct quartic)
augmentedQuarticResponseGate dataSet =
  ℚP.≤-<-trans
    (localPlusHistoryBelowLinearBudget dataSet)
    (linearBudgetBelowMargin dataSet)

asAugmentedShootingSensitivityData :
  ∀ {kernel cutoff}
    {quartic : Quartic.QuarticSourceSensitivityData kernel cutoff} →
  QuarticResponseCanonicalGate quartic →
  Aug.AugmentedShootingSensitivityData cutoff
asAugmentedShootingSensitivityData {quartic = quartic} dataSet = record
  { Aug.AugmentedShootingSensitivityData.direct = Quartic.direct quartic
  ; Aug.AugmentedShootingSensitivityData.historyConstant =
      quarticResponseHistoryConstant quartic
  ; Aug.AugmentedShootingSensitivityData.historyConstantNonnegative =
      quarticResponseHistoryConstantNonnegative quartic
  ; Aug.AugmentedShootingSensitivityData.augmentedContractionGate =
      augmentedQuarticResponseGate dataSet
  }

rowAQuarticResponseMarginCancellationLevel : ProofLevel
rowAQuarticResponseMarginCancellationLevel = machineChecked

rowAQuarticResponseSingleLinearGateLevel : ProofLevel
rowAQuarticResponseSingleLinearGateLevel = machineChecked

rowAQuarticResponseToAugmentedShootingLevel : ProofLevel
rowAQuarticResponseToAugmentedShootingLevel = machineChecked

-- The source-facing leaf is now particularly small: instantiate the literal
-- geometric response kernel and prove the direct history injection is quartic
-- (or sharper).  Once the same trajectory also supplies b,C,L and gamma<=1,
-- one finite constant package pays the complete shooting sensitivity gate.
literalRowAQuarticResponseKernelInstantiationLevel : ProofLevel
literalRowAQuarticResponseKernelInstantiationLevel = conditional
