{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact where

------------------------------------------------------------------------
-- LITERAL FINITE YM MEASURE -> CYLINDER NUMERATOR ALGEBRA
--
-- On the physical carrier, cylinder observables are literal functions on the
-- finite configuration space.  Haar-integral linearity plus positivity of the
-- density derives the unnormalized numerator algebra used by the normalized
-- cylinder-limit theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; _≤ℝ_;
   ≤ℝ-refl; mulMonotoneNonnegative;
   mulZeroˡ; mulZeroʳ; mulOneʳ;
   *-assoc; *-comm; *-distribˡ-+)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

zeroObservable :
  ∀ {Configuration} → Configuration → ℝ
zeroObservable _ = 0ℝ

oneObservable :
  ∀ {Configuration} → Configuration → ℝ
oneObservable _ = 1ℝ

addObservable :
  ∀ {Configuration} →
  (Configuration → ℝ) →
  (Configuration → ℝ) →
  Configuration → ℝ
addObservable left right configuration =
  left configuration +ℝ right configuration

scaleObservable :
  ∀ {Configuration} →
  ℝ →
  (Configuration → ℝ) →
  Configuration → ℝ
scaleObservable scalar observable configuration =
  scalar *ℝ observable configuration

PointwiseNonnegative :
  ∀ {Configuration} →
  (Configuration → ℝ) → Set
PointwiseNonnegative observable =
  ∀ configuration → 0ℝ ≤ℝ observable configuration

record PhysicalFiniteMeasureIntegrationLaws
    {Configuration : Set}
    (measure :
      Physical.PhysicalFiniteYMMeasure Configuration ℝ) : Set₁ where
  field
    densityNonnegative :
      ∀ configuration →
      0ℝ ≤ℝ Physical.density measure configuration

    haarIntegralCongruent :
      ∀ left right →
      (∀ configuration → left configuration ≡ right configuration) →
      Physical.haarIntegral measure left
      ≡ Physical.haarIntegral measure right

    haarIntegralZero :
      Physical.haarIntegral measure zeroObservable ≡ 0ℝ

    haarIntegralAdd :
      ∀ left right →
      Physical.haarIntegral measure (addObservable left right)
      ≡
      Physical.haarIntegral measure left
        +ℝ Physical.haarIntegral measure right

    haarIntegralScale :
      ∀ scalar observable →
      Physical.haarIntegral measure
        (scaleObservable scalar observable)
      ≡
      scalar *ℝ Physical.haarIntegral measure observable

    haarIntegralPositive :
      ∀ observable →
      PointwiseNonnegative observable →
      0ℝ ≤ℝ Physical.haarIntegral measure observable

    partitionFunctionIsDensityIntegral :
      Physical.partitionFunction measure
      ≡
      Physical.haarIntegral measure
        (Physical.density measure)

open PhysicalFiniteMeasureIntegrationLaws public

unnormalizedNumerator :
  ∀ {Configuration} →
  Physical.PhysicalFiniteYMMeasure Configuration ℝ →
  (Configuration → ℝ) → ℝ
unnormalizedNumerator measure observable =
  Physical.haarIntegral measure
    (λ configuration →
      Physical.density measure configuration
      *ℝ observable configuration)

densityTimesZero :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ)
    configuration →
  Physical.density measure configuration
    *ℝ zeroObservable configuration
  ≡ 0ℝ
densityTimesZero measure configuration =
  mulZeroʳ (Physical.density measure configuration)

densityTimesOne :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ)
    configuration →
  Physical.density measure configuration
    *ℝ oneObservable configuration
  ≡ Physical.density measure configuration
densityTimesOne measure configuration =
  mulOneʳ (Physical.density measure configuration)

densityTimesAdd :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ)
    left right configuration →
  Physical.density measure configuration
    *ℝ addObservable left right configuration
  ≡
  addObservable
    (λ x → Physical.density measure x *ℝ left x)
    (λ x → Physical.density measure x *ℝ right x)
    configuration
densityTimesAdd measure left right configuration =
  *-distribˡ-+
    (Physical.density measure configuration)
    (left configuration)
    (right configuration)

densityTimesScale :
  ∀ {Configuration}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ)
    scalar observable configuration →
  Physical.density measure configuration
    *ℝ scaleObservable scalar observable configuration
  ≡
  scaleObservable scalar
    (λ x → Physical.density measure x *ℝ observable x)
    configuration
densityTimesScale measure scalar observable configuration =
  trans
    (*-assoc
      (Physical.density measure configuration)
      scalar
      (observable configuration))
    (trans
      (cong
        (λ coefficient →
          coefficient *ℝ observable configuration)
        (*-comm
          (Physical.density measure configuration)
          scalar))
      (sym
        (*-assoc
          scalar
          (Physical.density measure configuration)
          (observable configuration))))

densityTimesNonnegativeObservable :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ} →
  PhysicalFiniteMeasureIntegrationLaws measure →
  (observable : Configuration → ℝ) →
  PointwiseNonnegative observable →
  PointwiseNonnegative
    (λ configuration →
      Physical.density measure configuration
      *ℝ observable configuration)
densityTimesNonnegativeObservable laws observable observableNN configuration =
  subst
    (λ lower →
      lower
      ≤ℝ
      Physical.density _ configuration
        *ℝ observable configuration)
    (mulZeroˡ 0ℝ)
    (mulMonotoneNonnegative
      (densityNonnegative laws configuration)
      ≤ℝ-refl
      (observableNN configuration)
      ≤ℝ-refl)

numeratorZero :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (laws : PhysicalFiniteMeasureIntegrationLaws measure) →
  unnormalizedNumerator measure zeroObservable ≡ 0ℝ
numeratorZero {measure = measure} laws =
  trans
    (haarIntegralCongruent laws
      (λ configuration →
        Physical.density measure configuration
          *ℝ zeroObservable configuration)
      zeroObservable
      (densityTimesZero measure))
    (haarIntegralZero laws)

numeratorOneIsPartitionFunction :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (laws : PhysicalFiniteMeasureIntegrationLaws measure) →
  unnormalizedNumerator measure oneObservable
  ≡ Physical.partitionFunction measure
numeratorOneIsPartitionFunction {measure = measure} laws =
  trans
    (haarIntegralCongruent laws
      (λ configuration →
        Physical.density measure configuration
          *ℝ oneObservable configuration)
      (Physical.density measure)
      (densityTimesOne measure))
    (sym (partitionFunctionIsDensityIntegral laws))

numeratorAdd :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (laws : PhysicalFiniteMeasureIntegrationLaws measure)
    left right →
  unnormalizedNumerator measure (addObservable left right)
  ≡
  unnormalizedNumerator measure left
    +ℝ unnormalizedNumerator measure right
numeratorAdd {measure = measure} laws left right =
  trans
    (haarIntegralCongruent laws
      (λ configuration →
        Physical.density measure configuration
          *ℝ addObservable left right configuration)
      (addObservable
        (λ x → Physical.density measure x *ℝ left x)
        (λ x → Physical.density measure x *ℝ right x))
      (densityTimesAdd measure left right))
    (haarIntegralAdd laws
      (λ x → Physical.density measure x *ℝ left x)
      (λ x → Physical.density measure x *ℝ right x))

numeratorScale :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (laws : PhysicalFiniteMeasureIntegrationLaws measure)
    scalar observable →
  unnormalizedNumerator measure (scaleObservable scalar observable)
  ≡
  scalar *ℝ unnormalizedNumerator measure observable
numeratorScale {measure = measure} laws scalar observable =
  trans
    (haarIntegralCongruent laws
      (λ configuration →
        Physical.density measure configuration
          *ℝ scaleObservable scalar observable configuration)
      (scaleObservable scalar
        (λ x →
          Physical.density measure x *ℝ observable x))
      (densityTimesScale measure scalar observable))
    (haarIntegralScale laws scalar
      (λ x → Physical.density measure x *ℝ observable x))

numeratorPositive :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (laws : PhysicalFiniteMeasureIntegrationLaws measure)
    observable →
  PointwiseNonnegative observable →
  0ℝ ≤ℝ unnormalizedNumerator measure observable
numeratorPositive laws observable observableNN =
  haarIntegralPositive laws _
    (densityTimesNonnegativeObservable laws observable observableNN)

physicalFiniteMeasureCylinderAlgebraCompilerLevel : ProofLevel
physicalFiniteMeasureCylinderAlgebraCompilerLevel = machineChecked

-- Actual finite-measure inputs: positivity and Haar integration laws.
literalFiniteHaarIntegrationLawsLevel : ProofLevel
literalFiniteHaarIntegrationLawsLevel = conditional
