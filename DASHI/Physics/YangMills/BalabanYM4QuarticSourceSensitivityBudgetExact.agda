{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4QuarticSourceSensitivityBudgetExact where

------------------------------------------------------------------------
-- ROW A FORWARD PRODUCER: QUARTIC SOURCE SENSITIVITY -> FINITE S_TOTAL
--
-- The backwards response-kernel consumer asks only for a cutoff-uniform bound
-- on the direct source sensitivities s_j.  If the literal differentiated
-- interaction gives the natural irrelevant/source suppression
--
--                  s_j <= D g_j^4,
--
-- and the Row-A trajectory lies in 0 <= g_j <= gamma, then
--
--                  s_j <= D gamma g_j^3.
--
-- The already-owned cubic telescope gives
--
--          b_* sum_{j<K} g_j^3 <= 2 gamma_tube.
--
-- Therefore
--
--   sum_{j<K} s_j
--     <= D gamma (2 gamma_tube / b_*),
--
-- uniformly for K <= cutoff.  This is exactly the S_total requested by the
-- response-kernel route; summability is a consequence of the positive Row-A
-- drift rather than a new hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕP
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quot
import DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact as Cubic
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanYM4BetaResponseKernelSummationExact as Kernel
import DASHI.Physics.YangMills.BalabanYM4FiniteBetaResponseKernelBudgetExact as Finite

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

power4 : ℚ → ℚ
power4 g = Cubic.cube g * g

record QuarticSourceSensitivityData
    (kernel : Kernel.GeometricBetaResponseKernel)
    (cutoff : Nat) : Set₁ where
  field
    direct : Direct.CumulativeSensitivityData cutoff

    sourceCoefficient couplingCap : ℚ
    sourceCoefficientNonnegative : 0ℚ ≤ sourceCoefficient
    couplingCapNonnegative : 0ℚ ≤ couplingCap
    tubeWidthNonnegative : 0ℚ ≤ Direct.tubeWidth direct

    couplingNonnegative : ∀ j → 0ℚ ≤ Direct.coupling direct j
    couplingBelowCap : ∀ j → j ℕ.< cutoff →
      Direct.coupling direct j ≤ couplingCap

    sourceQuartic : ∀ j → j ℕ.< cutoff →
      Kernel.sourceSensitivity kernel j
      ≤ sourceCoefficient * power4 (Direct.coupling direct j)

open QuarticSourceSensitivityData public

cubeNonnegative :
  ∀ {kernel cutoff}
    (dataSet : QuarticSourceSensitivityData kernel cutoff) j →
  0ℚ ≤ Cubic.cube (Direct.coupling (direct dataSet) j)
cubeNonnegative dataSet j =
  let
    g = Direct.coupling (direct dataSet) j
    gNN = couplingNonnegative dataSet j
  in
  mulNN (mulNN gNN gNN) gNN

quarticBelowCapTimesCube :
  ∀ {kernel cutoff}
    (dataSet : QuarticSourceSensitivityData kernel cutoff)
    j → j ℕ.< cutoff →
  power4 (Direct.coupling (direct dataSet) j)
  ≤ couplingCap dataSet * Cubic.cube (Direct.coupling (direct dataSet) j)
quarticBelowCapTimesCube dataSet j j< =
  let
    g = Direct.coupling (direct dataSet) j
    cubeNN = cubeNonnegative dataSet j
    scaled : Cubic.cube g * g ≤ Cubic.cube g * couplingCap dataSet
    scaled = Norm.scaleNonnegative
      (Cubic.cube g) cubeNN (couplingBelowCap dataSet j j<)
  in
  subst
    (λ right → power4 g ≤ right)
    (ℚP.*-comm (Cubic.cube g) (couplingCap dataSet))
    scaled

sourceBelowCapTimesCube :
  ∀ {kernel cutoff}
    (dataSet : QuarticSourceSensitivityData kernel cutoff)
    j → j ℕ.< cutoff →
  Kernel.sourceSensitivity kernel j
  ≤ (sourceCoefficient dataSet * couplingCap dataSet)
      * Cubic.cube (Direct.coupling (direct dataSet) j)
sourceBelowCapTimesCube dataSet j j< =
  let
    D = sourceCoefficient dataSet
    first = sourceQuartic dataSet j j<
    scaled = Norm.scaleNonnegative
      D (sourceCoefficientNonnegative dataSet)
      (quarticBelowCapTimesCube dataSet j j<)
  in
  ℚP.≤-trans first
    (subst
      (λ right →
        D * power4 (Direct.coupling (direct dataSet) j) ≤ right)
      (ℚRing.solve-∀
        D (couplingCap dataSet)
        (Cubic.cube (Direct.coupling (direct dataSet) j)))
      scaled)

sourcePartialBelowCapTimesCubes :
  ∀ {kernel cutoff}
    (dataSet : QuarticSourceSensitivityData kernel cutoff)
    K → K ℕ.≤ cutoff →
  Kernel.sum₀ (Kernel.sourceSensitivity kernel) K
  ≤ (sourceCoefficient dataSet * couplingCap dataSet)
      * Cubic.sumCubes (Direct.coupling (direct dataSet)) K
sourcePartialBelowCapTimesCubes dataSet zero K≤ =
  subst
    (λ right → 0ℚ ≤ right)
    (sym (ℚP.*-zeroʳ (sourceCoefficient dataSet * couplingCap dataSet)))
    ℚP.≤-refl
sourcePartialBelowCapTimesCubes {kernel} dataSet (suc n) sucN≤ =
  let
    n<cutoff : n ℕ.< _
    n<cutoff = sucN≤

    previous = sourcePartialBelowCapTimesCubes
      dataSet n (ℕP.<⇒≤ n<cutoff)
    current = sourceBelowCapTimesCube dataSet n n<cutoff
    added = ℚP.+-mono-≤ previous current
  in
  subst
    (λ right →
      Kernel.sum₀ (Kernel.sourceSensitivity kernel) (suc n) ≤ right)
    (ℚRing.solve-∀
      (sourceCoefficient dataSet)
      (couplingCap dataSet)
      (Cubic.sumCubes (Direct.coupling (direct dataSet)) n)
      (Cubic.cube (Direct.coupling (direct dataSet) n)))
    added

marginReciprocal :
  ∀ {kernel cutoff} →
  QuarticSourceSensitivityData kernel cutoff → ℚ
marginReciprocal dataSet =
  Quot.positiveReciprocal
    (Direct.marginConstant (direct dataSet))
    (Direct.marginPositive (direct dataSet))

cubicSumUniform :
  ∀ {kernel cutoff}
    (dataSet : QuarticSourceSensitivityData kernel cutoff)
    K → K ℕ.≤ cutoff →
  Cubic.sumCubes (Direct.coupling (direct dataSet)) K
  ≤ marginReciprocal dataSet
      * (Cubic.twoℚ * Direct.tubeWidth (direct dataSet))
cubicSumUniform dataSet K K≤ =
  let
    margin = Direct.marginConstant (direct dataSet)
    inv = marginReciprocal dataSet
    sum = Cubic.sumCubes (Direct.coupling (direct dataSet)) K
    upper = Cubic.twoℚ * Direct.tubeWidth (direct dataSet)

    invNN : 0ℚ ≤ inv
    invNN = ℚP.<⇒≤
      (Quot.positiveReciprocalPositive margin (Direct.marginPositive (direct dataSet)))

    scaled : inv * (margin * sum) ≤ inv * upper
    scaled = Norm.scaleNonnegative inv invNN
      (Direct.cubicSumBound (direct dataSet) K K≤)

    rightInverse : margin * inv ≡ Data.Rational.Base.1ℚ
    rightInverse = Quot.positiveReciprocalRightInverse
      margin (Direct.marginPositive (direct dataSet))

    leftIdentity : inv * (margin * sum) ≡ sum
    leftIdentity =
      trans
        (ℚRing.solve-∀ inv margin sum)
        (trans
          (cong (_* sum) rightInverse)
          (ℚP.*-identityˡ sum))
  in
  subst
    (λ left → left ≤ inv * upper)
    leftIdentity
    scaled

quarticSourceTotal :
  ∀ {kernel cutoff} →
  QuarticSourceSensitivityData kernel cutoff → ℚ
quarticSourceTotal dataSet =
  (sourceCoefficient dataSet * couplingCap dataSet)
    * (marginReciprocal dataSet
      * (Cubic.twoℚ * Direct.tubeWidth (direct dataSet)))

quarticSourceTotalNonnegative :
  ∀ {kernel cutoff}
    (dataSet : QuarticSourceSensitivityData kernel cutoff) →
  0ℚ ≤ quarticSourceTotal dataSet
quarticSourceTotalNonnegative dataSet =
  let
    firstNN = mulNN
      (sourceCoefficientNonnegative dataSet)
      (couplingCapNonnegative dataSet)
    invNN = ℚP.<⇒≤
      (Quot.positiveReciprocalPositive
        (Direct.marginConstant (direct dataSet))
        (Direct.marginPositive (direct dataSet)))
    twoNN : 0ℚ ≤ Cubic.twoℚ
    twoNN = ℚP.nonNegative⁻¹ Cubic.twoℚ
    upperNN = mulNN twoNN (tubeWidthNonnegative dataSet)
    secondNN = mulNN invNN upperNN
  in
  mulNN firstNN secondNN

sourcePartialUniform :
  ∀ {kernel cutoff}
    (dataSet : QuarticSourceSensitivityData kernel cutoff)
    K → K ℕ.≤ cutoff →
  Kernel.sum₀ (Kernel.sourceSensitivity kernel) K
  ≤ quarticSourceTotal dataSet
sourcePartialUniform dataSet K K≤ =
  let
    first = sourcePartialBelowCapTimesCubes dataSet K K≤
    scale = sourceCoefficient dataSet * couplingCap dataSet
    scaleNN = mulNN
      (sourceCoefficientNonnegative dataSet)
      (couplingCapNonnegative dataSet)
    second = Norm.scaleNonnegative scale scaleNN
      (cubicSumUniform dataSet K K≤)
  in
  ℚP.≤-trans first second

asFiniteSourceSensitivityBudget :
  ∀ {kernel cutoff} →
  QuarticSourceSensitivityData kernel cutoff →
  Finite.FiniteSourceSensitivityBudget kernel cutoff
asFiniteSourceSensitivityBudget dataSet = record
  { Finite.FiniteSourceSensitivityBudget.totalSourceSensitivity =
      quarticSourceTotal dataSet
  ; Finite.FiniteSourceSensitivityBudget.totalSourceSensitivityNonnegative =
      quarticSourceTotalNonnegative dataSet
  ; Finite.FiniteSourceSensitivityBudget.sourcePartialBelowTotal =
      sourcePartialUniform dataSet
  }

quarticSourceSensitivityToFiniteBudgetLevel : ProofLevel
quarticSourceSensitivityToFiniteBudgetLevel = machineChecked

-- Physical source leaf: prove the literal preceding-history injection into the
-- irrelevant/polymer response is O(g_j^4) (or sharper) on the same analytic
-- trajectory.  The finite S_total is then generated by the already-proved Row-A
-- positive drift and tube, with no extra summability hypothesis.
literalQuarticHistoryInjectionSensitivityLevel : ProofLevel
literalQuarticHistoryInjectionSensitivityLevel = conditional
