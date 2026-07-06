module DASHI.Physics.YangMills.P33BalabanMetricFaithfulnessBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.String using (String)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; absℝ
  ; -ℝ_
  ; _≤ℝ_
  ; _<ℝ_
  ; _+ℝ_
  ; _-ℝ_
  )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
import DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility as Anisotropic

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

record P33ActualBalabanPerturbationKernel
  (Polymer Edge : Set)
  (BalabanSmallFieldRegularity : ℕ → Polymer → Set)
  (BalabanLocalMetric : ℕ → Polymer → Edge → ℝ)
  (BalabanBackgroundMetric : ℕ → Edge → ℝ)
  (BalabanMetricPerturbation : ℕ → Polymer → Edge → ℝ)
  (BalabanSupEdgePerturbation : ℕ → Polymer → ℝ)
  (ε-real-const : ℝ)
  : Set₁ where
  field
    balabanMetricDecomposition :
      ∀ k X e →
      BalabanLocalMetric k X e
        ≡ BalabanBackgroundMetric k e
        +ℝ BalabanMetricPerturbation k X e

    balabanSmallFieldPerturbationBound :
      ∀ k X →
      BalabanSmallFieldRegularity k X →
      BalabanSupEdgePerturbation k X ≤ℝ ε-real-const

record P33ActualBalabanPositivityKernel
  (Polymer Edge : Set)
  (BalabanBackgroundMetric : ℕ → Edge → ℝ)
  (BalabanAdmissibleScale : ℕ → Set)
  (ε-real-const : ℝ)
  (m-background : ℝ)
  : Set₁ where
  field
    balabanBackgroundMetricUniformPositive :
      ∀ k e →
      BalabanAdmissibleScale k →
      m-background ≤ℝ BalabanBackgroundMetric k e

    balabanPerturbationBelowMargin :
      ε-real-const <ℝ m-background

record P33ActualBalabanLinkComparisonKernel
  (Polymer Edge : Set)
  (BalabanLocalMetric : ℕ → Polymer → Edge → ℝ)
  (BalabanLinkWeight : ℕ → Edge → ℝ)
  (BalabanIsEdgeOf : Edge → ℕ → Polymer → Set)
  : Set₁ where
  field
    balabanLinkWeightComparison :
      ∀ k X e →
      BalabanIsEdgeOf e k X →
      BalabanLocalMetric k X e ≤ℝ BalabanLinkWeight k e

record P33ActualBalabanDiameterDominationKernel
  (Polymer : Set)
  (ordinaryDiameter : ℕ → Polymer → ℝ)
  (weightedDiameter : ℕ → Polymer → ℝ)
  : Set₁ where
  field
    balabanDiameterDomination :
      ∀ k X →
      ordinaryDiameter k X ≤ℝ weightedDiameter k X

record P33ActualBalabanMetricSourceTheorem
  (Polymer Edge : Set)
  (BalabanSmallFieldRegularity : ℕ → Polymer → Set)
  (BalabanLocalMetric : ℕ → Polymer → Edge → ℝ)
  (BalabanBackgroundMetric : ℕ → Edge → ℝ)
  (BalabanMetricPerturbation : ℕ → Polymer → Edge → ℝ)
  (BalabanSupEdgePerturbation : ℕ → Polymer → ℝ)
  (BalabanAdmissibleScale : ℕ → Set)
  (BalabanLinkWeight : ℕ → Edge → ℝ)
  (BalabanIsEdgeOf : Edge → ℕ → Polymer → Set)
  (ordinaryDiameter : ℕ → Polymer → ℝ)
  (weightedDiameter : ℕ → Polymer → ℝ)
  (ε-real-const : ℝ)
  (m-background : ℝ)
  : Set₁ where
  field
    sourceAnchor :
      P33BalabanSourceAnchor

    perturbationKernel :
      P33ActualBalabanPerturbationKernel
        Polymer
        Edge
        BalabanSmallFieldRegularity
        BalabanLocalMetric
        BalabanBackgroundMetric
        BalabanMetricPerturbation
        BalabanSupEdgePerturbation
        ε-real-const

    positivityKernel :
      P33ActualBalabanPositivityKernel
        Polymer
        Edge
        BalabanBackgroundMetric
        BalabanAdmissibleScale
        ε-real-const
        m-background

    linkComparisonKernel :
      P33ActualBalabanLinkComparisonKernel
        Polymer
        Edge
        BalabanLocalMetric
        BalabanLinkWeight
        BalabanIsEdgeOf

    diameterDominationKernel :
      P33ActualBalabanDiameterDominationKernel
        Polymer
        ordinaryDiameter
        weightedDiameter

record P33BalabanDashiMetricAgreement
  (Polymer Edge : Set)
  (SmallFieldRegularity : ℕ → Polymer → Set)
  (localMetric : ℕ → Polymer → Edge → ℝ)
  (backgroundMetric : ℕ → Edge → ℝ)
  (perturbation : ℕ → Polymer → Edge → ℝ)
  (linkWeight : ℕ → Edge → ℝ)
  (ordinaryDiameter : ℕ → Polymer → ℝ)
  (weightedDiameter : ℕ → Polymer → ℝ)
  (BalabanSmallFieldRegularity : ℕ → Polymer → Set)
  (BalabanLocalMetric : ℕ → Polymer → Edge → ℝ)
  (BalabanBackgroundMetric : ℕ → Edge → ℝ)
  (BalabanMetricPerturbation : ℕ → Polymer → Edge → ℝ)
  (BalabanLinkWeight : ℕ → Edge → ℝ)
  (BalabanOrdinaryDiameter : ℕ → Polymer → ℝ)
  (BalabanWeightedDiameter : ℕ → Polymer → ℝ)
  : Set₁ where
  field
    objectAdapter :
      P33BalabanMetricObjectAdapter Polymer Edge

    localMetricAgreement :
      ∀ k X e →
      localMetric k X e ≡ BalabanLocalMetric k X e

    backgroundMetricAgreement :
      ∀ k e →
      backgroundMetric k e ≡ BalabanBackgroundMetric k e

    perturbationAgreement :
      ∀ k X e →
      perturbation k X e ≡ BalabanMetricPerturbation k X e

    smallFieldRegularityAgreement :
      ∀ k X →
      SmallFieldRegularity k X ↔ BalabanSmallFieldRegularity k X

    linkWeightAgreement :
      ∀ k e →
      linkWeight k e ≡ BalabanLinkWeight k e

    ordinaryDiameterAgreement :
      ∀ k X →
      ordinaryDiameter k X ≡ BalabanOrdinaryDiameter k X

    weightedDiameterAgreement :
      ∀ k X →
      weightedDiameter k X ≡ BalabanWeightedDiameter k X

record P33BalabanSourceMetricTheorem
  (Polymer Edge : Set)
  (BalabanSmallFieldRegularity : ℕ → Polymer → Set)
  (BalabanLocalMetric : ℕ → Polymer → Edge → ℝ)
  (BalabanBackgroundMetric : ℕ → Edge → ℝ)
  (BalabanMetricPerturbation : ℕ → Polymer → Edge → ℝ)
  (BalabanSupEdgePerturbation : ℕ → Polymer → ℝ)
  (BalabanAdmissibleScale : ℕ → Set)
  (BalabanLinkWeight : ℕ → Edge → ℝ)
  (BalabanIsEdgeOf : Edge → ℕ → Polymer → Set)
  (ε-real-const : ℝ)
  (m-background : ℝ)
  : Set₁ where
  field
    metricDecomposition :
      ∀ k X e →
      BalabanLocalMetric k X e
        ≡ BalabanBackgroundMetric k e
        +ℝ BalabanMetricPerturbation k X e

    smallFieldControlsPerturbation :
      ∀ k X →
      BalabanSmallFieldRegularity k X →
      BalabanSupEdgePerturbation k X ≤ℝ ε-real-const

    backgroundMetricUniformlyPositive :
      ∀ k e →
      BalabanAdmissibleScale k →
      m-background ≤ℝ BalabanBackgroundMetric k e

    perturbationBelowMargin :
      ε-real-const <ℝ m-background

    linkWeightComparableToMetric :
      ∀ k X e →
      BalabanIsEdgeOf e k X →
      BalabanLocalMetric k X e ≤ℝ BalabanLinkWeight k e

P33BalabanDashiMetricAgreementFromFaithfulnessBridge :
  ∀
    {Polymer Edge : Set}
    {SmallFieldRegularity : ℕ → Polymer → Set}
    {localMetric : ℕ → Polymer → Edge → ℝ}
    {backgroundMetric : ℕ → Edge → ℝ}
    {perturbation : ℕ → Polymer → Edge → ℝ}
    {linkWeight : ℕ → Edge → ℝ}
    {ordinaryDiameter weightedDiameter : ℕ → Polymer → ℝ} →
  (bridge :
    P33BalabanMetricFaithfulnessBridge
      Polymer
      Edge
      SmallFieldRegularity
      localMetric
      backgroundMetric
      perturbation
      linkWeight) →
  (ordinaryDiameterAgreement :
    ∀ k X →
    ordinaryDiameter k X ≡ ordinaryDiameter k X) →
  (weightedDiameterAgreement :
    ∀ k X →
    weightedDiameter k X ≡ weightedDiameter k X) →
  P33BalabanDashiMetricAgreement
    Polymer
    Edge
    SmallFieldRegularity
    localMetric
    backgroundMetric
    perturbation
    linkWeight
    ordinaryDiameter
    weightedDiameter
    (P33BalabanMetricObjectAdapter.BalabanSmallFieldRegularity
      (P33BalabanMetricFaithfulnessBridge.objectAdapter bridge))
    (P33BalabanMetricObjectAdapter.BalabanLocalMetric
      (P33BalabanMetricFaithfulnessBridge.objectAdapter bridge))
    (P33BalabanMetricObjectAdapter.BalabanBackgroundMetric
      (P33BalabanMetricFaithfulnessBridge.objectAdapter bridge))
    (P33BalabanMetricObjectAdapter.BalabanMetricPerturbation
      (P33BalabanMetricFaithfulnessBridge.objectAdapter bridge))
    (P33BalabanMetricObjectAdapter.BalabanLinkWeight
      (P33BalabanMetricFaithfulnessBridge.objectAdapter bridge))
    ordinaryDiameter
    weightedDiameter
P33BalabanDashiMetricAgreementFromFaithfulnessBridge
  bridge
  ordinaryDiameterAgreement
  weightedDiameterAgreement = record
  { objectAdapter =
      P33BalabanMetricFaithfulnessBridge.objectAdapter bridge
  ; localMetricAgreement =
      P33BalabanMetricFaithfulnessBridge.localMetric-agrees-with-Balaban bridge
  ; backgroundMetricAgreement =
      P33BalabanMetricFaithfulnessBridge.backgroundMetric-agrees-with-Balaban bridge
  ; perturbationAgreement =
      P33BalabanMetricFaithfulnessBridge.perturbation-agrees-with-Balaban bridge
  ; smallFieldRegularityAgreement =
      P33BalabanMetricFaithfulnessBridge.smallFieldRegularity-agrees-with-Balaban bridge
  ; linkWeightAgreement =
      P33BalabanMetricFaithfulnessBridge.linkWeight-agrees-with-Balaban bridge
  ; ordinaryDiameterAgreement = ordinaryDiameterAgreement
  ; weightedDiameterAgreement = weightedDiameterAgreement
  }

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

record P33BalabanSourceReconstructionKernel
  (Polymer Edge : Set)
  (SmallFieldRegularity : ℕ → Polymer → Set)
  (isEdgeOf : Edge → ℕ → Polymer → Set)
  (localMetric : ℕ → Polymer → Edge → ℝ)
  (backgroundMetric : ℕ → Edge → ℝ)
  (perturbation : ℕ → Polymer → Edge → ℝ)
  (supEdgePerturbation : ℕ → Polymer → ℝ)
  (admissibleScale : ℕ → Set)
  (linkWeight : ℕ → Edge → ℝ)
  (ε-real-const : ℝ)
  (m-background : ℝ)
  : Set₁ where
  field
    sourceAnchor :
      P33BalabanSourceAnchor

    sourceMetricTheorem :
      P33BalabanSourceMetricTheorem
        Polymer
        Edge
        SmallFieldRegularity
        localMetric
        backgroundMetric
        perturbation
        supEdgePerturbation
        admissibleScale
        linkWeight
        isEdgeOf
        ε-real-const
        m-background

    faithfulnessReceipt :
      P33BalabanMetricFaithfulnessReceipt
        Polymer
        Edge
        SmallFieldRegularity
        localMetric
        backgroundMetric
        perturbation
        linkWeight

    metricDischarge :
      P33BalabanMetricDischarge
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

P33BalabanSourceMetricTheoremFromPerturbationKernel :
  ∀
    {Polymer Edge : Set}
    {SmallFieldRegularity : ℕ → Polymer → Set}
    {isEdgeOf : Edge → ℕ → Polymer → Set}
    {localMetric : ℕ → Polymer → Edge → ℝ}
    {backgroundMetric : ℕ → Edge → ℝ}
    {perturbation : ℕ → Polymer → Edge → ℝ}
    {supEdgePerturbation : ℕ → Polymer → ℝ}
    {ε-real-const m-background : ℝ}
    {admissibleScale : ℕ → Set}
    {linkWeight : ℕ → Edge → ℝ} →
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
    linkWeight →
  P33BalabanSourceMetricTheorem
    Polymer
    Edge
    SmallFieldRegularity
    localMetric
    backgroundMetric
    perturbation
    supEdgePerturbation
    admissibleScale
    linkWeight
    isEdgeOf
    ε-real-const
    m-background
P33BalabanSourceMetricTheoremFromPerturbationKernel kernel = record
  { metricDecomposition =
      P33PerturbationStabilityKernel.metricDecomposition kernel
  ; smallFieldControlsPerturbation =
      P33PerturbationStabilityKernel.smallFieldControlsPerturbation kernel
  ; backgroundMetricUniformlyPositive =
      P33PerturbationStabilityKernel.backgroundMetricUniformlyPositive kernel
  ; perturbationBelowMargin =
      P33PerturbationStabilityKernel.perturbationBelowMargin kernel
  ; linkWeightComparableToMetric =
      P33PerturbationStabilityKernel.linkWeightComparableToMetric kernel
  }

P33ActualBalabanMetricSourceTheoremFromPerturbationKernel :
  ∀
    {Polymer Edge : Set}
    {SmallFieldRegularity : ℕ → Polymer → Set}
    {isEdgeOf : Edge → ℕ → Polymer → Set}
    {localMetric : ℕ → Polymer → Edge → ℝ}
    {backgroundMetric : ℕ → Edge → ℝ}
    {perturbation : ℕ → Polymer → Edge → ℝ}
    {supEdgePerturbation : ℕ → Polymer → ℝ}
    {admissibleScale : ℕ → Set}
    {linkWeight : ℕ → Edge → ℝ}
    {ordinaryDiameter weightedDiameter : ℕ → Polymer → ℝ}
    {ε-real-const m-background : ℝ} →
  (sourceAnchor : P33BalabanSourceAnchor) →
  (kernel :
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
      linkWeight) →
  (diameterDomination :
    ∀ k X →
    ordinaryDiameter k X ≤ℝ weightedDiameter k X) →
  P33ActualBalabanMetricSourceTheorem
    Polymer
    Edge
    SmallFieldRegularity
    localMetric
    backgroundMetric
    perturbation
    supEdgePerturbation
    admissibleScale
    linkWeight
    isEdgeOf
    ordinaryDiameter
    weightedDiameter
    ε-real-const
    m-background
P33ActualBalabanMetricSourceTheoremFromPerturbationKernel
  sourceAnchor
  kernel
  diameterDomination = record
  { sourceAnchor = sourceAnchor
  ; perturbationKernel = record
      { balabanMetricDecomposition =
          P33PerturbationStabilityKernel.metricDecomposition kernel
      ; balabanSmallFieldPerturbationBound =
          P33PerturbationStabilityKernel.smallFieldControlsPerturbation kernel
      }
  ; positivityKernel = record
      { balabanBackgroundMetricUniformPositive =
          P33PerturbationStabilityKernel.backgroundMetricUniformlyPositive kernel
      ; balabanPerturbationBelowMargin =
          P33PerturbationStabilityKernel.perturbationBelowMargin kernel
      }
  ; linkComparisonKernel = record
      { balabanLinkWeightComparison =
          P33PerturbationStabilityKernel.linkWeightComparableToMetric kernel
      }
  ; diameterDominationKernel = record
      { balabanDiameterDomination = diameterDomination
      }
  }

P33BalabanSourceMetricTheoremFromActualBalaban :
  ∀
    {Polymer Edge : Set}
    {SmallFieldRegularity : ℕ → Polymer → Set}
    {localMetric : ℕ → Polymer → Edge → ℝ}
    {backgroundMetric : ℕ → Edge → ℝ}
    {perturbation : ℕ → Polymer → Edge → ℝ}
    {supEdgePerturbation : ℕ → Polymer → ℝ}
    {admissibleScale : ℕ → Set}
    {linkWeight : ℕ → Edge → ℝ}
    {isEdgeOf : Edge → ℕ → Polymer → Set}
    {ordinaryDiameter weightedDiameter : ℕ → Polymer → ℝ}
    {ε-real-const m-background : ℝ} →
  P33ActualBalabanMetricSourceTheorem
    Polymer
    Edge
    SmallFieldRegularity
    localMetric
    backgroundMetric
    perturbation
    supEdgePerturbation
    admissibleScale
    linkWeight
    isEdgeOf
    ordinaryDiameter
    weightedDiameter
    ε-real-const
    m-background →
  P33BalabanSourceMetricTheorem
    Polymer
    Edge
    SmallFieldRegularity
    localMetric
    backgroundMetric
    perturbation
    supEdgePerturbation
    admissibleScale
    linkWeight
    isEdgeOf
    ε-real-const
    m-background
P33BalabanSourceMetricTheoremFromActualBalaban theorem = record
  { metricDecomposition =
      P33ActualBalabanPerturbationKernel.balabanMetricDecomposition
        (P33ActualBalabanMetricSourceTheorem.perturbationKernel theorem)
  ; smallFieldControlsPerturbation =
      P33ActualBalabanPerturbationKernel.balabanSmallFieldPerturbationBound
        (P33ActualBalabanMetricSourceTheorem.perturbationKernel theorem)
  ; backgroundMetricUniformlyPositive =
      P33ActualBalabanPositivityKernel.balabanBackgroundMetricUniformPositive
        (P33ActualBalabanMetricSourceTheorem.positivityKernel theorem)
  ; perturbationBelowMargin =
      P33ActualBalabanPositivityKernel.balabanPerturbationBelowMargin
        (P33ActualBalabanMetricSourceTheorem.positivityKernel theorem)
  ; linkWeightComparableToMetric =
      P33ActualBalabanLinkComparisonKernel.balabanLinkWeightComparison
        (P33ActualBalabanMetricSourceTheorem.linkComparisonKernel theorem)
  }

P33BalabanSourceReconstructionKernelFromPieces :
  ∀
    {Polymer Edge : Set}
    {SmallFieldRegularity : ℕ → Polymer → Set}
    {isEdgeOf : Edge → ℕ → Polymer → Set}
    {localMetric : ℕ → Polymer → Edge → ℝ}
    {backgroundMetric : ℕ → Edge → ℝ}
    {perturbation : ℕ → Polymer → Edge → ℝ}
    {supEdgePerturbation : ℕ → Polymer → ℝ}
    {admissibleScale : ℕ → Set}
    {linkWeight : ℕ → Edge → ℝ}
    {ε-real-const m-background : ℝ} →
  (sourceAnchor : P33BalabanSourceAnchor) →
  (sourceMetricTheorem :
    P33BalabanSourceMetricTheorem
      Polymer
      Edge
      SmallFieldRegularity
      localMetric
      backgroundMetric
      perturbation
      supEdgePerturbation
      admissibleScale
      linkWeight
      isEdgeOf
      ε-real-const
      m-background) →
  (metricDischarge :
    P33BalabanMetricDischarge
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
      linkWeight) →
  P33BalabanSourceReconstructionKernel
    Polymer
    Edge
    SmallFieldRegularity
    isEdgeOf
    localMetric
    backgroundMetric
    perturbation
    supEdgePerturbation
    admissibleScale
    linkWeight
    ε-real-const
    m-background
P33BalabanSourceReconstructionKernelFromPieces
  sourceAnchor
  sourceMetricTheorem
  metricDischarge = record
  { sourceAnchor = sourceAnchor
  ; sourceMetricTheorem = sourceMetricTheorem
  ; faithfulnessReceipt =
      P33BalabanMetricDischarge.faithfulnessReceipt metricDischarge
  ; metricDischarge = metricDischarge
  ; noClayPromotion = refl
  }

P33BalabanSourceReconstructionKernelFromActualBalaban :
  ∀
    {Polymer Edge : Set}
    {SmallFieldRegularity : ℕ → Polymer → Set}
    {isEdgeOf : Edge → ℕ → Polymer → Set}
    {localMetric : ℕ → Polymer → Edge → ℝ}
    {backgroundMetric : ℕ → Edge → ℝ}
    {perturbation : ℕ → Polymer → Edge → ℝ}
    {supEdgePerturbation : ℕ → Polymer → ℝ}
    {admissibleScale : ℕ → Set}
    {linkWeight : ℕ → Edge → ℝ}
    {ordinaryDiameter weightedDiameter : ℕ → Polymer → ℝ}
    {ε-real-const m-background : ℝ} →
  (sourceTheorem :
    P33ActualBalabanMetricSourceTheorem
      Polymer
      Edge
      SmallFieldRegularity
      localMetric
      backgroundMetric
      perturbation
      supEdgePerturbation
      admissibleScale
      linkWeight
      isEdgeOf
      ordinaryDiameter
      weightedDiameter
      ε-real-const
      m-background) →
  (metricDischarge :
    P33BalabanMetricDischarge
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
      ) →
  P33BalabanSourceReconstructionKernel
    Polymer
    Edge
    SmallFieldRegularity
    isEdgeOf
    localMetric
    backgroundMetric
    perturbation
    supEdgePerturbation
    admissibleScale
    linkWeight
    ε-real-const
    m-background
P33BalabanSourceReconstructionKernelFromActualBalaban
  sourceTheorem
  metricDischarge =
  P33BalabanSourceReconstructionKernelFromPieces
    (P33ActualBalabanMetricSourceTheorem.sourceAnchor sourceTheorem)
    (P33BalabanSourceMetricTheoremFromActualBalaban sourceTheorem)
    metricDischarge

P33LocalMetricPositiveFromKernel :
  ∀
    {Polymer Edge : Set}
    {SmallFieldRegularity : ℕ → Polymer → Set}
    {isEdgeOf : Edge → ℕ → Polymer → Set}
    {localMetric : ℕ → Polymer → Edge → ℝ}
    {backgroundMetric : ℕ → Edge → ℝ}
    {perturbation : ℕ → Polymer → Edge → ℝ}
    {supEdgePerturbation : ℕ → Polymer → ℝ}
    {ε-real-const m-background : ℝ}
    {admissibleScale : ℕ → Set}
    {linkWeight : ℕ → Edge → ℝ} →
  (kernel :
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
      linkWeight) →
  (pointwiseAbsPerturbation :
    ∀ k X e →
    isEdgeOf e k X →
    absℝ (perturbation k X e) ≤ℝ supEdgePerturbation k X) →
  ∀ k X e →
  SmallFieldRegularity k X →
  admissibleScale k →
  isEdgeOf e k X →
  0ℝ <ℝ localMetric k X e
P33LocalMetricPositiveFromKernel {backgroundMetric = backgroundMetric} {perturbation = perturbation} {ε-real-const = ε-real-const} {m-background = m-background} kernel pointwiseAbsPerturbation k X e sf scale edge
  rewrite
    P33PerturbationStabilityKernel.metricDecomposition kernel k X e =
      Anisotropic.P33BackgroundPlusSmallPerturbationPositive
        (backgroundMetric k e)
        (perturbation k X e)
        ε-real-const
        m-background
        (P33PerturbationStabilityKernel.backgroundMetricUniformlyPositive
          kernel k e scale)
        (Anisotropic.≤ℝ-trans
          (pointwiseAbsPerturbation k X e edge)
          (P33PerturbationStabilityKernel.smallFieldControlsPerturbation
            kernel k X sf))
        (P33PerturbationStabilityKernel.perturbationBelowMargin kernel)

P33MetricCarriesUniformFloorFromKernel :
  ∀
    {Polymer Edge : Set}
    {SmallFieldRegularity : ℕ → Polymer → Set}
    {isEdgeOf : Edge → ℕ → Polymer → Set}
    {localMetric : ℕ → Polymer → Edge → ℝ}
    {backgroundMetric : ℕ → Edge → ℝ}
    {perturbation : ℕ → Polymer → Edge → ℝ}
    {supEdgePerturbation : ℕ → Polymer → ℝ}
    {ε-real-const m-background : ℝ}
    {admissibleScale : ℕ → Set}
    {linkWeight : ℕ → Edge → ℝ} →
  (kernel :
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
      linkWeight) →
  (pointwiseAbsPerturbation :
    ∀ k X e →
    isEdgeOf e k X →
    absℝ (perturbation k X e) ≤ℝ supEdgePerturbation k X) →
  ∀ k X e →
  SmallFieldRegularity k X →
  admissibleScale k →
  isEdgeOf e k X →
  m-background -ℝ ε-real-const ≤ℝ localMetric k X e
P33MetricCarriesUniformFloorFromKernel kernel pointwiseAbsPerturbation k X e sf scale edge
  rewrite
    P33PerturbationStabilityKernel.metricDecomposition kernel k X e =
      Anisotropic.minus-lower-plus-lower
        (P33PerturbationStabilityKernel.backgroundMetricUniformlyPositive
          kernel k e scale)
        (Anisotropic.abs-bound-gives-lower
          (Anisotropic.≤ℝ-trans
            (pointwiseAbsPerturbation k X e edge)
            (P33PerturbationStabilityKernel.smallFieldControlsPerturbation
              kernel k X sf)))

P33LinkWeightCarriesUniformFloorFromKernel :
  ∀
    {Polymer Edge : Set}
    {SmallFieldRegularity : ℕ → Polymer → Set}
    {isEdgeOf : Edge → ℕ → Polymer → Set}
    {localMetric : ℕ → Polymer → Edge → ℝ}
    {backgroundMetric : ℕ → Edge → ℝ}
    {perturbation : ℕ → Polymer → Edge → ℝ}
    {supEdgePerturbation : ℕ → Polymer → ℝ}
    {ε-real-const m-background : ℝ}
    {admissibleScale : ℕ → Set}
    {linkWeight : ℕ → Edge → ℝ} →
  (kernel :
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
      linkWeight) →
  (pointwiseAbsPerturbation :
    ∀ k X e →
    isEdgeOf e k X →
    absℝ (perturbation k X e) ≤ℝ supEdgePerturbation k X) →
  ∀ k X e →
  SmallFieldRegularity k X →
  admissibleScale k →
  isEdgeOf e k X →
  m-background -ℝ ε-real-const ≤ℝ linkWeight k e
P33LinkWeightCarriesUniformFloorFromKernel kernel pointwiseAbsPerturbation k X e sf scale edge =
  Anisotropic.≤ℝ-trans
    (P33MetricCarriesUniformFloorFromKernel
      kernel pointwiseAbsPerturbation k X e sf scale edge)
    (P33PerturbationStabilityKernel.linkWeightComparableToMetric
      kernel k X e edge)

P33LinkWeightPositiveFromKernel :
  ∀
    {Polymer Edge : Set}
    {SmallFieldRegularity : ℕ → Polymer → Set}
    {isEdgeOf : Edge → ℕ → Polymer → Set}
    {localMetric : ℕ → Polymer → Edge → ℝ}
    {backgroundMetric : ℕ → Edge → ℝ}
    {perturbation : ℕ → Polymer → Edge → ℝ}
    {supEdgePerturbation : ℕ → Polymer → ℝ}
    {ε-real-const m-background : ℝ}
    {admissibleScale : ℕ → Set}
    {linkWeight : ℕ → Edge → ℝ} →
  (kernel :
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
      linkWeight) →
  (pointwiseAbsPerturbation :
    ∀ k X e →
    isEdgeOf e k X →
    absℝ (perturbation k X e) ≤ℝ supEdgePerturbation k X) →
  ∀ k X e →
  SmallFieldRegularity k X →
  admissibleScale k →
  isEdgeOf e k X →
  0ℝ <ℝ linkWeight k e
P33LinkWeightPositiveFromKernel kernel pointwiseAbsPerturbation k X e sf scale edge =
  Anisotropic.positive-from-lower-bound
    (Anisotropic.positive-minus-margin
      (P33PerturbationStabilityKernel.perturbationBelowMargin kernel))
    (P33LinkWeightCarriesUniformFloorFromKernel
      kernel pointwiseAbsPerturbation k X e sf scale edge)
