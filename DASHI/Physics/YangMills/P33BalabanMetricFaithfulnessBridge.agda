module DASHI.Physics.YangMills.P33BalabanMetricFaithfulnessBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String using (String)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _≤ℝ_
  ; _<ℝ_
  ; _+ℝ_
  )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    to : A → B
    from : B → A

record P33BalabanMetricObjectAdapter (Polymer Edge : Set) : Set₁ where
  field
    BalabanLocalMetric :
      ℕ → Polymer → Edge → ℝ

    BalabanBackgroundMetric :
      ℕ → Edge → ℝ

    BalabanMetricPerturbation :
      ℕ → Polymer → Edge → ℝ

    BalabanSmallFieldRegularity :
      ℕ → Polymer → Set

    BalabanLinkWeight :
      ℕ → Edge → ℝ

record P33BalabanSourceAnchor : Set₁ where
  field
    sourceName :
      String

    theoremSpan :
      String

    objectDefinitionsSpan :
      String

    normalizationConvention :
      String

    parserReceipt :
      String

    noClayPromotion :
      clayYangMillsPromoted ≡ false

record P33BalabanMetricFaithfulnessBridge
  (Polymer Edge : Set)
  (SmallFieldRegularity : ℕ → Polymer → Set)
  (localMetric : ℕ → Polymer → Edge → ℝ)
  (backgroundMetric : ℕ → Edge → ℝ)
  (perturbation : ℕ → Polymer → Edge → ℝ)
  (linkWeight : ℕ → Edge → ℝ)
  : Set₁ where
  field
    objectAdapter :
      P33BalabanMetricObjectAdapter Polymer Edge

    localMetric-agrees-with-Balaban :
      ∀ k X e →
      localMetric k X e ≡
      P33BalabanMetricObjectAdapter.BalabanLocalMetric objectAdapter k X e

    backgroundMetric-agrees-with-Balaban :
      ∀ k e →
      backgroundMetric k e ≡
      P33BalabanMetricObjectAdapter.BalabanBackgroundMetric objectAdapter k e

    perturbation-agrees-with-Balaban :
      ∀ k X e →
      perturbation k X e ≡
      P33BalabanMetricObjectAdapter.BalabanMetricPerturbation objectAdapter k X e

    smallFieldRegularity-agrees-with-Balaban :
      ∀ k X →
      SmallFieldRegularity k X ↔
      P33BalabanMetricObjectAdapter.BalabanSmallFieldRegularity objectAdapter k X

    linkWeight-agrees-with-Balaban :
      ∀ k e →
      linkWeight k e ≡
      P33BalabanMetricObjectAdapter.BalabanLinkWeight objectAdapter k e

data SourceBackedMetricFaithfulnessCandidate : Set where
  sourceBackedMetricFaithfulnessCandidate :
    SourceBackedMetricFaithfulnessCandidate

record P33BalabanMetricFaithfulnessReceipt
  (Polymer Edge : Set)
  (SmallFieldRegularity : ℕ → Polymer → Set)
  (localMetric : ℕ → Polymer → Edge → ℝ)
  (backgroundMetric : ℕ → Edge → ℝ)
  (perturbation : ℕ → Polymer → Edge → ℝ)
  (linkWeight : ℕ → Edge → ℝ)
  : Set₁ where
  field
    anchor :
      P33BalabanSourceAnchor

    bridge :
      P33BalabanMetricFaithfulnessBridge
        Polymer
        Edge
        SmallFieldRegularity
        localMetric
        backgroundMetric
        perturbation
        linkWeight

    status :
      SourceBackedMetricFaithfulnessCandidate

    noClayPromotion :
      clayYangMillsPromoted ≡ false

record P33PerturbationStabilityKernel
  (Polymer Edge : Set)
  (SmallFieldRegularity : ℕ → Polymer → Set)
  (isEdgeOf : Edge → ℕ → Polymer → Set)
  (localMetric : ℕ → Polymer → Edge → ℝ)
  (backgroundMetric : ℕ → Edge → ℝ)
  (perturbation : ℕ → Polymer → Edge → ℝ)
  (supEdgePerturbation : ℕ → Polymer → ℝ)
  (ε-real-const : ℝ)
  (m-background : ℝ)
  (admissibleScale : ℕ → Set)
  (linkWeight : ℕ → Edge → ℝ)
  : Set₁ where
  field
    metricDecomposition :
      ∀ k X e →
      localMetric k X e
        ≡ backgroundMetric k e
        +ℝ perturbation k X e

    smallFieldControlsPerturbation :
      ∀ k X →
      SmallFieldRegularity k X →
      supEdgePerturbation k X ≤ℝ ε-real-const

    backgroundMetricUniformlyPositive :
      ∀ k e →
      admissibleScale k →
      m-background ≤ℝ backgroundMetric k e

    perturbationBelowMargin :
      ε-real-const <ℝ m-background

    linkWeightComparableToMetric :
      ∀ k X e →
      isEdgeOf e k X →
      localMetric k X e ≤ℝ linkWeight k e

record P33BalabanMetricDischarge
  (Polymer Edge : Set)
  (SmallFieldRegularity : ℕ → Polymer → Set)
  (isEdgeOf : Edge → ℕ → Polymer → Set)
  (localMetric : ℕ → Polymer → Edge → ℝ)
  (backgroundMetric : ℕ → Edge → ℝ)
  (perturbation : ℕ → Polymer → Edge → ℝ)
  (supEdgePerturbation : ℕ → Polymer → ℝ)
  (ε-real-const : ℝ)
  (m-background : ℝ)
  (admissibleScale : ℕ → Set)
  (linkWeight : ℕ → Edge → ℝ)
  : Set₁ where
  field
    faithfulnessReceipt :
      P33BalabanMetricFaithfulnessReceipt
        Polymer
        Edge
        SmallFieldRegularity
        localMetric
        backgroundMetric
        perturbation
        linkWeight

    perturbationKernel :
      P33PerturbationStabilityKernel
        Polymer
        Edge
        SmallFieldRegularity
        isEdgeOf
        localMetric
        backgroundMetric
        perturbation
        supEdgePerturbation
        ε-real-const
        m-background
        admissibleScale
        linkWeight

    noClayPromotion :
      clayYangMillsPromoted ≡ false
