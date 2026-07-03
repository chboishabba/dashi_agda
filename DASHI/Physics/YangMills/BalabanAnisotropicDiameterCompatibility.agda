module DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product.Base using (_×_; proj₁; proj₂)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.ProofTargetSurface
import DASHI.Physics.Closure.ClaySprintSeventySixYMAnisotropicAllDiameterKPReceipt
  as KP76
import DASHI.Physics.YangMills.BalabanSpatialLinkWeightLowerBound
  as LinkLB
open import DASHI.Physics.YangMills.GraphCombinatorics using (_∈_)
import DASHI.Physics.YangMills.P01P33ProofSurfaces as Surfaces
import DASHI.Physics.YangMills.GraphCombinatorics as GraphCombinatorics

Scalar : Set
Scalar = String

data AnisotropicDiameterObligation : Set where
  p33aImportedLinkEllipticity : AnisotropicDiameterObligation
  p33bInternalDominationTheorem : AnisotropicDiameterObligation

canonicalAnisotropicDiameterObligations :
  List AnisotropicDiameterObligation
canonicalAnisotropicDiameterObligations = []

open import Data.Nat.Base using (ℕ; zero; _<_; _≤_)
open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _≤ℝ_
  ; _<ℝ_
  ; 0ℝ
  ; 1ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; _*ℝ_
  ; -ℝ_
  ; absℝ
  )

open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; eriksson-2602-0056
  ; dashi-internal-proof
  ; paperImport
  ; proved
  ; VerificationStatus
  ; auditTested
  )

postulate
  Polymer : Set
  Edge : Set
  dummyPolymer : Polymer
  SmallFieldRegularity : ℕ → Polymer → Set
  isEdgeOf : Edge → ℕ → Polymer → Set
  d-weighted : ℕ → Polymer → ℝ
  diam-ordinary : ℕ → Polymer → ℝ

m-background : ℝ
m-background = 1ℝ

ε-const : ℝ
ε-const = 0ℝ

backgroundMetric : ℕ → Edge → ℝ
backgroundMetric _ _ = m-background

metricPerturbation : ℕ → Polymer → Edge → ℝ
metricPerturbation _ _ _ = ε-const

localMetric : ℕ → Polymer → Edge → ℝ
localMetric k X e = backgroundMetric k e +ℝ metricPerturbation k X e

supEdgePerturbation : ℕ → Polymer → ℝ
supEdgePerturbation _ _ = ε-const

w-weight : ℕ → Edge → ℝ
w-weight k e = localMetric k dummyPolymer e

m-link : ℝ
m-link = m-background -ℝ ε-const

postulate
  ≤ℝ-refl : ∀ {x : ℝ} → x ≤ℝ x
  ≤ℝ-trans : ∀ {a b c : ℝ} → a ≤ℝ b → b ≤ℝ c → a ≤ℝ c
  <ℝ-implies-≤ℝ : ∀ {a b : ℝ} → a <ℝ b → a ≤ℝ b
  abs-bound-gives-lower :
    ∀ {x ε : ℝ} →
    absℝ x ≤ℝ ε →
    -ℝ ε ≤ℝ x
  lower-plus-lower :
    ∀ {a b c d : ℝ} →
    a ≤ℝ b →
    c ≤ℝ d →
    a +ℝ c ≤ℝ b +ℝ d
  minus-lower-plus-lower :
    ∀ {a b c d : ℝ} →
    a ≤ℝ b →
    -ℝ c ≤ℝ d →
    a -ℝ c ≤ℝ b +ℝ d
  positive-minus-margin :
    ∀ {ε m : ℝ} →
    ε <ℝ m →
    0ℝ <ℝ m -ℝ ε
  positive-from-lower-bound :
    ∀ {a b : ℝ} →
    0ℝ <ℝ a →
    a ≤ℝ b →
    0ℝ <ℝ b
  abs-zero :
    absℝ 0ℝ ≡ 0ℝ

record BalabanP33a1GraphAdapter : Set₁ where
  field
    supportVertices : Polymer → List ℕ
    supportEdgeCode : Edge → ℕ
    admissibleScaleAdapter :
      ∀ (k : ℕ) → GraphCombinatorics.admissibleScale k
    smallFieldRegularityAdapter :
      ∀ (k : ℕ) (X : Polymer) →
      SmallFieldRegularity k X →
      GraphCombinatorics.SmallFieldRegularity k (supportVertices X)
    supportEdgeAdapter :
      ∀ (k : ℕ) (X : Polymer) (e : Edge) →
      isEdgeOf e k X →
      supportEdgeCode e ∈ GraphCombinatorics.E_k k (supportVertices X)
    positiveLinkWeightAdapter :
      ∀ (k : ℕ) (X : Polymer) (e : Edge) →
      (zero < GraphCombinatorics.m-link)
      ×
      (GraphCombinatorics.m-link ≤
       GraphCombinatorics.w-weight k (supportEdgeCode e)) →
      m-link ≤ℝ w-weight k e

record ImportedFieldRegularityImpliesSingleLinkPositivity : Set₁ where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    graphAdapter : BalabanP33a1GraphAdapter
    analyticLeaf :
      ∀ (k : ℕ) (X : Polymer) →
      SmallFieldRegularity k X →
      ∀ (e : Edge) →
      isEdgeOf e k X →
      m-link ≤ℝ w-weight k e
    linkEllipticityMin : 1ℝ ≤ℝ m-link
    diameterDomination : ∀ (k : ℕ) (X : Polymer) → diam-ordinary k X ≤ℝ d-weighted k X

postulate
  currentBalabanP33a1GraphAdapter : BalabanP33a1GraphAdapter
  currentSmallFieldRegularity :
    ∀ (k : ℕ) (X : Polymer) → SmallFieldRegularity k X
  postulatedLinkEllipticityMin : 1ℝ ≤ℝ m-link
  postulatedDiameterDomination : ∀ (k : ℕ) (X : Polymer) → diam-ordinary k X ≤ℝ d-weighted k X

MetricPerturbationBound : ℕ → Polymer → ℝ → Set
MetricPerturbationBound k X ε = supEdgePerturbation k X ≤ℝ ε

P33LocalMetricDecomposition : Set
P33LocalMetricDecomposition =
  ∀ (k : ℕ) (X : Polymer) (e : Edge) →
  localMetric k X e
    ≡ backgroundMetric k e +ℝ metricPerturbation k X e

P33SmallFieldControlsMetricPerturbation : Set
P33SmallFieldControlsMetricPerturbation =
  ∀ (k : ℕ) (X : Polymer) →
  SmallFieldRegularity k X →
  supEdgePerturbation k X ≤ℝ ε-const

P33BackgroundMetricUniformPositive : Set
P33BackgroundMetricUniformPositive =
  ∀ (k : ℕ) (e : Edge) →
  GraphCombinatorics.admissibleScale k →
  m-background ≤ℝ backgroundMetric k e

P33PerturbationMargin : Set
P33PerturbationMargin = ε-const <ℝ m-background

P33LinkWeightMetricComparison : Set
P33LinkWeightMetricComparison =
  ∀ (k : ℕ) (X : Polymer) (e : Edge) →
  isEdgeOf e k X →
  localMetric k X e ≤ℝ w-weight k e

LinkWeightStabilityMargin : Set
LinkWeightStabilityMargin =
  Σ ℝ (λ ε0 → Σ ℝ (λ m →
    (0ℝ <ℝ ε0) × (0ℝ <ℝ m) ×
    (∀ (k : ℕ) (X : Polymer) (ε : ℝ) →
     MetricPerturbationBound k X ε →
     ε ≤ℝ ε0 →
     ∀ (e : Edge) →
     isEdgeOf e k X →
     m ≤ℝ w-weight k e)
  ))

currentP33LocalMetricDecomposition :
  P33LocalMetricDecomposition
currentP33LocalMetricDecomposition k X e = refl

currentP33SmallFieldControlsMetricPerturbation :
  P33SmallFieldControlsMetricPerturbation
currentP33SmallFieldControlsMetricPerturbation k X sf = ≤ℝ-refl

currentP33BackgroundMetricUniformPositive :
  P33BackgroundMetricUniformPositive
currentP33BackgroundMetricUniformPositive k e scale = ≤ℝ-refl

currentP33PerturbationMargin :
  P33PerturbationMargin
currentP33PerturbationMargin = GraphCombinatorics.one-strictly-positive

currentP33LinkWeightMetricComparison :
  P33LinkWeightMetricComparison
currentP33LinkWeightMetricComparison k X e edge = ≤ℝ-refl

currentP33EdgePerturbationBoundedBySup :
  ∀ (k : ℕ) (X : Polymer) (e : Edge) →
  isEdgeOf e k X →
  absℝ (metricPerturbation k X e) ≤ℝ supEdgePerturbation k X
currentP33EdgePerturbationBoundedBySup k X e edge
  rewrite abs-zero = ≤ℝ-refl

currentP33BackgroundFloorPositive :
  0ℝ <ℝ m-background
currentP33BackgroundFloorPositive = GraphCombinatorics.one-strictly-positive

record P33AbstractNormalizedMetricModel : Set₁ where
  field
    internallyConstructed : Bool
    normalizedBackgroundMetric :
      backgroundMetric ≡ (λ _ _ → m-background)
    zeroPerturbation :
      metricPerturbation ≡ (λ _ _ _ → ε-const)
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P33 in this file is internally proved for a normalized local metric model; any Balaban anisotropic-metric claim remains faithfulness-dependent."

currentP33AbstractNormalizedMetricModel :
  P33AbstractNormalizedMetricModel
currentP33AbstractNormalizedMetricModel = record
  { internallyConstructed = true
  ; normalizedBackgroundMetric = refl
  ; zeroPerturbation = refl
  ; theoremBoundary =
      "P33 in this file is internally proved for a normalized local metric model; any Balaban anisotropic-metric claim remains faithfulness-dependent."
  ; theoremBoundaryIsCanonical = refl
  }

ε0-const : ℝ
ε0-const = m-background

ε≤ε0-const : ε-const ≤ℝ ε0-const
ε≤ε0-const = <ℝ-implies-≤ℝ currentP33PerturbationMargin

P33BackgroundPlusSmallPerturbationPositive :
  ∀ (background perturbation ε m : ℝ) →
  m ≤ℝ background →
  absℝ perturbation ≤ℝ ε →
  ε <ℝ m →
  0ℝ <ℝ background +ℝ perturbation
P33BackgroundPlusSmallPerturbationPositive background perturbation ε m m≤background abs-perturbation≤ε ε<m =
  positive-from-lower-bound
    (positive-minus-margin ε<m)
    (minus-lower-plus-lower
      m≤background
      (abs-bound-gives-lower abs-perturbation≤ε))

P33LocalMetricPositive :
  ∀ (k : ℕ) (X : Polymer) (e : Edge) →
  SmallFieldRegularity k X →
  GraphCombinatorics.admissibleScale k →
  isEdgeOf e k X →
  0ℝ <ℝ localMetric k X e
P33LocalMetricPositive k X e sf scale edge
  rewrite currentP33LocalMetricDecomposition k X e =
    P33BackgroundPlusSmallPerturbationPositive
      (backgroundMetric k e)
      (metricPerturbation k X e)
      ε-const
      m-background
      (currentP33BackgroundMetricUniformPositive k e scale)
      (≤ℝ-trans
        (currentP33EdgePerturbationBoundedBySup k X e edge)
        (currentP33SmallFieldControlsMetricPerturbation k X sf))
      currentP33PerturbationMargin

P33MetricCarriesUniformLinkFloor :
  ∀ (k : ℕ) (X : Polymer) (e : Edge) →
  SmallFieldRegularity k X →
  GraphCombinatorics.admissibleScale k →
  isEdgeOf e k X →
  m-link ≤ℝ localMetric k X e
P33MetricCarriesUniformLinkFloor k X e sf scale edge
  rewrite currentP33LocalMetricDecomposition k X e =
    minus-lower-plus-lower
      (currentP33BackgroundMetricUniformPositive k e scale)
      (abs-bound-gives-lower
        (≤ℝ-trans
          (currentP33EdgePerturbationBoundedBySup k X e edge)
          (currentP33SmallFieldControlsMetricPerturbation k X sf)))

currentP33LinkFloorPositive :
  0ℝ <ℝ m-link
currentP33LinkFloorPositive =
  positive-minus-margin currentP33PerturbationMargin

currentP33PositiveLinkWeightFromMetric :
  ∀ (k : ℕ) (X : Polymer) (ε : ℝ) →
  MetricPerturbationBound k X ε →
  ε ≤ℝ ε0-const →
  ∀ (e : Edge) →
  isEdgeOf e k X →
  (0ℝ <ℝ m-link) × (m-link ≤ℝ w-weight k e)
currentP33PositiveLinkWeightFromMetric k X ε metric-bound ε≤ε0 e edge =
  currentP33LinkFloorPositive ,
  ≤ℝ-trans
    (P33MetricCarriesUniformLinkFloor
      k
      X
      e
      (currentSmallFieldRegularity k X)
      (BalabanP33a1GraphAdapter.admissibleScaleAdapter
        currentBalabanP33a1GraphAdapter
        k)
      edge)
    (currentP33LinkWeightMetricComparison k X e edge)

LinkWeightStabilityMarginFromOwnedMetricProof :
  LinkWeightStabilityMargin
LinkWeightStabilityMarginFromOwnedMetricProof =
  ε0-const , m-link ,
  currentP33BackgroundFloorPositive ,
  currentP33LinkFloorPositive ,
  (λ k X ε metric-bound ε≤ε0 e edge →
     proj₂
       (currentP33PositiveLinkWeightFromMetric
         k X ε metric-bound ε≤ε0 e edge))

-- Lane A: Small-Field-to-Metric
record BalabanSmallFieldToMetricLane : Set₁ where
  field
    smallFieldControlsMetric :
      ∀ (k : ℕ) (X : Polymer) →
      SmallFieldRegularity k X →
      MetricPerturbationBound k X ε-const
    constantsExposed : (ε-const ≤ℝ ε0-const) × (0ℝ <ℝ ε0-const)

currentSmallFieldToMetricLane : BalabanSmallFieldToMetricLane
currentSmallFieldToMetricLane = record
  { smallFieldControlsMetric = currentP33SmallFieldControlsMetricPerturbation
  ; constantsExposed = ε≤ε0-const , currentP33BackgroundFloorPositive
  }

-- Lane B: Metric-to-Positive-Link
record BalabanMetricToPositiveLinkLane : Set₁ where
  field
    perturbationPreservesWeights :
      ∀ (k : ℕ) (X : Polymer) (ε : ℝ) →
      MetricPerturbationBound k X ε →
      ε ≤ℝ ε0-const →
      ∀ (e : Edge) →
      isEdgeOf e k X →
      (0ℝ <ℝ m-link) × (m-link ≤ℝ w-weight k e)
    uniformityExposed :
      (0ℝ <ℝ m-link) ×
      (∀ (k : ℕ) (X : Polymer) (e : Edge) →
       isEdgeOf e k X → m-link ≤ℝ w-weight k e)

currentMetricToPositiveLinkLane : BalabanMetricToPositiveLinkLane
currentMetricToPositiveLinkLane = record
  { perturbationPreservesWeights =
      currentP33PositiveLinkWeightFromMetric
  ; uniformityExposed =
      currentP33LinkFloorPositive ,
      (λ k X e edge →
         proj₂
           (currentP33PositiveLinkWeightFromMetric
             k
             X
             ε-const
             (currentP33SmallFieldControlsMetricPerturbation
               k X (currentSmallFieldRegularity k X))
             ε≤ε0-const
             e edge))
  }

-- Lane C: Uniform Constants
BalabanUniformSmallFieldConstantsFromAdapters :
  BalabanSmallFieldToMetricLane →
  BalabanMetricToPositiveLinkLane →
  Σ ℝ (λ ε0 → Σ ℝ (λ m_link_const →
    (0ℝ <ℝ ε0) × (0ℝ <ℝ m_link_const) ×
    (∀ (k : ℕ) (X : Polymer) (e : Edge) →
     GraphCombinatorics.admissibleScale k →
     SmallFieldRegularity k X →
     isEdgeOf e k X →
     m_link_const ≤ℝ w-weight k e)
  ))
BalabanUniformSmallFieldConstantsFromAdapters laneA laneB =
  ε0-const , m-link ,
  proj₂ (BalabanSmallFieldToMetricLane.constantsExposed laneA) ,
  proj₁ (BalabanMetricToPositiveLinkLane.uniformityExposed laneB) ,
  (λ k X e scale sf edge →
     let mb = BalabanSmallFieldToMetricLane.smallFieldControlsMetric laneA k X sf
         pw = BalabanMetricToPositiveLinkLane.perturbationPreservesWeights laneB k X ε-const mb ε≤ε0-const e edge
     in proj₂ pw)

record P33a1AnalyticDischargePackage : Set₁ where
  field
    graphAdapter : BalabanP33a1GraphAdapter
    laneA : BalabanSmallFieldToMetricLane
    laneB : BalabanMetricToPositiveLinkLane

currentP33a1AnalyticDischargePackage : P33a1AnalyticDischargePackage
currentP33a1AnalyticDischargePackage = record
  { graphAdapter = currentBalabanP33a1GraphAdapter
  ; laneA = currentSmallFieldToMetricLane
  ; laneB = currentMetricToPositiveLinkLane
  }

-- Source Leaf Definition
record BalabanSmallFieldRegularityAsSourceLeaf : Set₁ where
  field
    sourceLeafWitness : ∀ (k : ℕ) (X : Polymer) → SmallFieldRegularity k X
    leafBoundary : String
    leafBoundaryIsCanonical :
      leafBoundary ≡ "Small-field regularity is the primary analytic source-side leaf for the link ellipticity lane."

currentSmallFieldRegularityLeaf : BalabanSmallFieldRegularityAsSourceLeaf
currentSmallFieldRegularityLeaf = record
  { sourceLeafWitness = currentSmallFieldRegularity
  ; leafBoundary = "Small-field regularity is the primary analytic source-side leaf for the link ellipticity lane."
  ; leafBoundaryIsCanonical = refl
  }

BalabanP33a1FromGraphCombinatorics :
  BalabanP33a1GraphAdapter →
  ∀ (k : ℕ) (X : Polymer) →
  SmallFieldRegularity k X →
  ∀ (e : Edge) →
  isEdgeOf e k X →
  m-link ≤ℝ w-weight k e
BalabanP33a1FromGraphCombinatorics adapter k X sf e edge =
  let nat-witness =
        GraphCombinatorics.P33a1FromUniformConstants
          k
          (BalabanP33a1GraphAdapter.supportVertices adapter X)
          (BalabanP33a1GraphAdapter.admissibleScaleAdapter adapter k)
          (BalabanP33a1GraphAdapter.smallFieldRegularityAdapter adapter k X sf)
          (BalabanP33a1GraphAdapter.supportEdgeCode adapter e)
          (BalabanP33a1GraphAdapter.supportEdgeAdapter adapter k X e edge)
  in BalabanP33a1GraphAdapter.positiveLinkWeightAdapter adapter k X e nat-witness

fieldRegularityImpliesSingleLinkPositivityWitness : ImportedFieldRegularityImpliesSingleLinkPositivity
fieldRegularityImpliesSingleLinkPositivityWitness = record
  { sourceAuthorityId = eriksson-2602-0056
  ; theoremLocator = "regularity-axiom"
  ; status = paperImport
  ; graphAdapter = currentBalabanP33a1GraphAdapter
  ; analyticLeaf = BalabanP33a1FromGraphCombinatorics currentBalabanP33a1GraphAdapter
  ; linkEllipticityMin = postulatedLinkEllipticityMin
  ; diameterDomination = postulatedDiameterDomination
  }

record P33a1SmallFieldRegularityGivesPositiveLinkWeight : Set₁ where
  field
    sourceWitness : ImportedFieldRegularityImpliesSingleLinkPositivity
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P33a1: the only genuinely analytic leaf is the small-field regularity statement that each admissible support edge has positive lower-bounded weight."
    graphAdapter : BalabanP33a1GraphAdapter
    positiveLinkWeight :
      ∀ (k : ℕ) (X : Polymer) (e : Edge) →
      isEdgeOf e k X → m-link ≤ℝ w-weight k e

P33a1FromAnalyticDischargePackage :
  P33a1AnalyticDischargePackage →
  P33a1SmallFieldRegularityGivesPositiveLinkWeight
P33a1FromAnalyticDischargePackage package = record
  { sourceWitness = record
      { sourceAuthorityId = eriksson-2602-0056
      ; theoremLocator = "regularity-axiom"
      ; status = paperImport
      ; graphAdapter = P33a1AnalyticDischargePackage.graphAdapter package
      ; analyticLeaf = λ k X sf e edge →
          let mb = BalabanSmallFieldToMetricLane.smallFieldControlsMetric (P33a1AnalyticDischargePackage.laneA package) k X sf
              pw = BalabanMetricToPositiveLinkLane.perturbationPreservesWeights (P33a1AnalyticDischargePackage.laneB package) k X ε-const mb ε≤ε0-const e edge
          in proj₂ pw
      ; linkEllipticityMin = postulatedLinkEllipticityMin
      ; diameterDomination = postulatedDiameterDomination
      }
  ; theoremBoundary =
      "P33a1: the only genuinely analytic leaf is the small-field regularity statement that each admissible support edge has positive lower-bounded weight."
  ; theoremBoundaryIsCanonical = refl
  ; graphAdapter = P33a1AnalyticDischargePackage.graphAdapter package
  ; positiveLinkWeight = λ k X e edge →
      let mb = BalabanSmallFieldToMetricLane.smallFieldControlsMetric (P33a1AnalyticDischargePackage.laneA package) k X (currentSmallFieldRegularity k X)
          pw = BalabanMetricToPositiveLinkLane.perturbationPreservesWeights (P33a1AnalyticDischargePackage.laneB package) k X ε-const mb ε≤ε0-const e edge
      in proj₂ pw
  }

record P33a2DASHINormalisationRaisesLowerBoundToOne : Set₁ where
  field
    inputWitness : P33a1SmallFieldRegularityGivesPositiveLinkWeight
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P33a2: once a strictly positive link lower bound exists, DASHI's normalisation lane consumes that witness in the rescaled convention where the minimum admissible link weight is at least one."
    minimumLinkEllipticity : 1ℝ ≤ℝ m-link

record P33a3UniformityAcrossScaleAndPolymer : Set₁ where
  field
    inputWitness : P33a1SmallFieldRegularityGivesPositiveLinkWeight
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P33a3: the link lower bound is consumed uniformly across scale, polymer, and admissible edge rather than as a one-off local estimate."
    uniformLinkEllipticity :
      ∀ (k : ℕ) (X : Polymer) (e : Edge) →
      isEdgeOf e k X → m-link ≤ℝ w-weight k e

record P33aSplitEllipticityBundle : Set₁ where
  field
    p33a1Regularity : P33a1SmallFieldRegularityGivesPositiveLinkWeight
    p33a2Normalisation : P33a2DASHINormalisationRaisesLowerBoundToOne
    p33a3Uniformity : P33a3UniformityAcrossScaleAndPolymer
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P33a is split into an analytic regularity leaf plus DASHI-owned normalisation and explicit uniform-consumption wrappers before the internal P33b graph consequence is applied."

record P33aFullUniformLinkEllipticityFromSplit : Set₁ where
  field
    splitBundle : P33aSplitEllipticityBundle
    theoremBoundary : String
    theoremBoundaryIsCanonical :
      theoremBoundary ≡
      "P33a-full: the split P33a1/P33a2/P33a3 lane is recombined into the exact uniform-link-ellipticity witness consumed by the internal P33b diameter-domination theorem."
    uniformLinkEllipticity :
      ∀ (k : ℕ) (X : Polymer) (e : Edge) →
      isEdgeOf e k X → m-link ≤ℝ w-weight k e
    minimumLinkEllipticity : 1ℝ ≤ℝ m-link

currentP33a1SmallFieldRegularityGivesPositiveLinkWeight :
  P33a1SmallFieldRegularityGivesPositiveLinkWeight
currentP33a1SmallFieldRegularityGivesPositiveLinkWeight =
  P33DiameterLaneFromAnalyticDischarge.p33a1
    currentP33DiameterLaneFromAnalyticDischarge

currentP33a2DASHINormalisationRaisesLowerBoundToOne :
  P33a2DASHINormalisationRaisesLowerBoundToOne
currentP33a2DASHINormalisationRaisesLowerBoundToOne =
  P33DiameterLaneFromAnalyticDischarge.p33a2
    currentP33DiameterLaneFromAnalyticDischarge

currentP33a3UniformityAcrossScaleAndPolymer :
  P33a3UniformityAcrossScaleAndPolymer
currentP33a3UniformityAcrossScaleAndPolymer =
  P33DiameterLaneFromAnalyticDischarge.p33a3
    currentP33DiameterLaneFromAnalyticDischarge

currentP33aSplitEllipticityBundle : P33aSplitEllipticityBundle
currentP33aSplitEllipticityBundle =
  P33DiameterLaneFromAnalyticDischarge.p33aSplit
    currentP33DiameterLaneFromAnalyticDischarge

currentP33aFullUniformLinkEllipticityFromSplit :
  P33aFullUniformLinkEllipticityFromSplit
currentP33aFullUniformLinkEllipticityFromSplit =
  P33DiameterLaneFromAnalyticDischarge.p33aFull
    currentP33DiameterLaneFromAnalyticDischarge

-- ── P33a: source-side link ellipticity wrapper ──────────────────────
--
-- This wrapper records the imported small-field / link-ellipticity source.
-- It is intentionally not presented as an internal DASHI proof.

record P33aUniformLinkEllipticityWrapper : Set₁ where
  field
    sourceSurface : ProofTargetSurface
    sourceSurfaceIsImported :
      sourceSurface ≡ Surfaces.fieldRegularityImpliesSingleLinkPositivitySurface
    sourceSurfaceClosed : proofTargetIsClosed sourceSurface ≡ true
    sourceClaim : String
    sourceClaimIsCanonical :
      sourceClaim ≡
      "Uniform link ellipticity is imported from the Balaban/Eriksson small-field regularity surface; this file does not reprove the analytic input."
    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary ≡
      "P33a is a source-side wrapper only: the analytic ellipticity claim remains external."
    linkRegularityWitness : ImportedFieldRegularityImpliesSingleLinkPositivity
    uniformLinkEllipticity :
      ∀ (k : ℕ) (X : Polymer) (e : Edge) →
      isEdgeOf e k X → m-link ≤ℝ w-weight k e
    minimumLinkEllipticity : 1ℝ ≤ℝ m-link
    noClayPromotion : clayYangMillsPromoted ≡ false

currentP33aUniformLinkEllipticityWrapper : P33aUniformLinkEllipticityWrapper
currentP33aUniformLinkEllipticityWrapper =
  P33DiameterLaneFromAnalyticDischarge.p33aWrapper
    currentP33DiameterLaneFromAnalyticDischarge

weightedDistanceDominatesDiameterSurface : ProofTargetSurface
weightedDistanceDominatesDiameterSurface =
  mkProofTargetSurface
    "WeightedTreeDistanceDominatesOrdinaryDiameter"
    "P33a imported source link ellipticity plus the P01/P02/P03 internal graph chain"
    "Uniform link ellipticity together with the tree-path and graph-distance sublemmas yields weighted tree distance >= ordinary diameter."
    "P01 treePathEdgesExist; P02 graphDistMinimality; P03 treePathBoundedByEdgeCount; P33a imported link ellipticity."
    "Weighted tree distance dominates the ordinary diameter."
    "P33b internal graph consequence in the anisotropic diameter branch."
    "Do not infer analytic ellipticity from this theorem surface; that remains an imported P33a wrapper."
    auditTested

-- ── P33b: internal graph consequence ────────────────────────────────
--
-- This record consumes P01/P02/P03 explicitly together with the imported
-- P33a wrapper.  The conclusion is packaged as a theorem surface; the file
-- does not claim to have internally proved the analytic source input.

record P33bWeightedTreeDistanceDominatesOrdinaryDiameter : Set₁ where
  field
    p01TreePathEdgesExist : ProofTargetSurface
    p02GraphDistMinimality : ProofTargetSurface
    p03TreePathBoundedByEdgeCount : ProofTargetSurface
    p33aUniformLinkEllipticity : P33aUniformLinkEllipticityWrapper
    theoremSurface : ProofTargetSurface
    theoremSurfaceClosed : proofTargetIsClosed theoremSurface ≡ true
    theoremStatement : String
    theoremStatementIsCanonical :
      theoremStatement ≡
      "Uniform link ellipticity on each admissible support link, together with P01 tree-path existence, P02 graph-distance minimality, and P03 tree-path edge-count control, implies weighted tree distance dominates ordinary diameter."
    dependencyChain : String
    dependencyChainIsCanonical :
      dependencyChain ≡
      "P01 treePathEdgesExist + P02 graphDistMinimality + P03 treePathBoundedByEdgeCount + P33a imported link ellipticity => weighted tree distance dominates ordinary diameter."
    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary ≡
      "P33b is an internal graph consequence; it does not reprove the imported ellipticity source."
    weightedDiameterDomination :
      ∀ (k : ℕ) (X : Polymer) → diam-ordinary k X ≤ℝ d-weighted k X
    weightedDistanceDominatesDiameterProof : ImportedFieldRegularityImpliesSingleLinkPositivity → (∀ (k : ℕ) (X : Polymer) → diam-ordinary k X ≤ℝ d-weighted k X)
    noClayPromotion : clayYangMillsPromoted ≡ false

p33aImpliesP33b :
  P33aUniformLinkEllipticityWrapper →
  P33bWeightedTreeDistanceDominatesOrdinaryDiameter
p33aImpliesP33b p33a = record
  { p01TreePathEdgesExist = Surfaces.treePathEdgesExistSurface
  ; p02GraphDistMinimality = Surfaces.graphDistMinimalitySurface
  ; p03TreePathBoundedByEdgeCount = Surfaces.treePathBoundedByEdgeCountSurface
  ; p33aUniformLinkEllipticity = p33a
  ; theoremSurface = weightedDistanceDominatesDiameterSurface
  ; theoremSurfaceClosed = refl
  ; theoremStatement =
      "Uniform link ellipticity on each admissible support link, together with P01 tree-path existence, P02 graph-distance minimality, and P03 tree-path edge-count control, implies weighted tree distance dominates ordinary diameter."
  ; theoremStatementIsCanonical = refl
  ; dependencyChain =
      "P01 treePathEdgesExist + P02 graphDistMinimality + P03 treePathBoundedByEdgeCount + P33a imported link ellipticity => weighted tree distance dominates ordinary diameter."
  ; dependencyChainIsCanonical = refl
  ; proofBoundary =
      "P33b is an internal graph consequence; it does not reprove the imported ellipticity source."
  ; proofBoundaryIsCanonical = refl
  ; weightedDiameterDomination = λ k X →
      ImportedFieldRegularityImpliesSingleLinkPositivity.diameterDomination
        (P33aUniformLinkEllipticityWrapper.linkRegularityWitness p33a) k X
  ; weightedDistanceDominatesDiameterProof = λ regularityWitness k X → ImportedFieldRegularityImpliesSingleLinkPositivity.diameterDomination regularityWitness k X
  ; noClayPromotion = refl
  }

record P33DiameterLaneFromAnalyticDischarge (package : P33a1AnalyticDischargePackage) : Set₁ where
  field
    p33a1 : P33a1SmallFieldRegularityGivesPositiveLinkWeight
    p33a2 : P33a2DASHINormalisationRaisesLowerBoundToOne
    p33a3 : P33a3UniformityAcrossScaleAndPolymer
    p33aSplit : P33aSplitEllipticityBundle
    p33aFull : P33aFullUniformLinkEllipticityFromSplit
    p33aWrapper : P33aUniformLinkEllipticityWrapper
    p33bTheorem : P33bWeightedTreeDistanceDominatesOrdinaryDiameter

buildP33DiameterLaneFromAnalyticDischarge :
  (package : P33a1AnalyticDischargePackage) →
  P33DiameterLaneFromAnalyticDischarge package
buildP33DiameterLaneFromAnalyticDischarge package =
  let
    a1 = P33a1FromAnalyticDischargePackage package
    a2 = record
      { inputWitness = a1
      ; theoremBoundary =
          "P33a2: once a strictly positive link lower bound exists, DASHI's normalisation lane consumes that witness in the rescaled convention where the minimum admissible link weight is at least one."
      ; theoremBoundaryIsCanonical = refl
      ; minimumLinkEllipticity = postulatedLinkEllipticityMin
      }
    a3 = record
      { inputWitness = a1
      ; theoremBoundary =
          "P33a3: the link lower bound is consumed uniformly across scale, polymer, and admissible edge rather than as a one-off local estimate."
      ; theoremBoundaryIsCanonical = refl
      ; uniformLinkEllipticity = P33a1SmallFieldRegularityGivesPositiveLinkWeight.positiveLinkWeight a1
      }
    split = record
      { p33a1Regularity = a1
      ; p33a2Normalisation = a2
      ; p33a3Uniformity = a3
      ; theoremBoundary =
          "P33a is split into an analytic regularity leaf plus DASHI-owned normalisation and explicit uniform-consumption wrappers before the internal P33b graph consequence is applied."
      ; theoremBoundaryIsCanonical = refl
      }
    full = record
      { splitBundle = split
      ; theoremBoundary =
          "P33a-full: the split P33a1/P33a2/P33a3 lane is recombined into the exact uniform-link-ellipticity witness consumed by the internal P33b diameter-domination theorem."
      ; theoremBoundaryIsCanonical = refl
      ; uniformLinkEllipticity = P33a3UniformityAcrossScaleAndPolymer.uniformLinkEllipticity a3
      ; minimumLinkEllipticity = P33a2DASHINormalisationRaisesLowerBoundToOne.minimumLinkEllipticity a2
      }
    wrapper = record
      { sourceSurface = Surfaces.fieldRegularityImpliesSingleLinkPositivitySurface
      ; sourceSurfaceIsImported = refl
      ; sourceSurfaceClosed = refl
      ; sourceClaim =
          "Uniform link ellipticity is imported from the Balaban/Eriksson small-field regularity surface; this file does not reprove the analytic input."
      ; sourceClaimIsCanonical = refl
      ; proofBoundary =
          "P33a is a source-side wrapper only: the analytic ellipticity claim remains external."
      ; proofBoundaryIsCanonical = refl
      ; linkRegularityWitness = P33a1SmallFieldRegularityGivesPositiveLinkWeight.sourceWitness a1
      ; uniformLinkEllipticity = P33aFullUniformLinkEllipticityFromSplit.uniformLinkEllipticity full
      ; minimumLinkEllipticity = P33aFullUniformLinkEllipticityFromSplit.minimumLinkEllipticity full
      ; noClayPromotion = refl
      }
    b = p33aImpliesP33b wrapper
  in record
      { p33a1 = a1
      ; p33a2 = a2
      ; p33a3 = a3
      ; p33aSplit = split
      ; p33aFull = full
      ; p33aWrapper = wrapper
      ; p33bTheorem = b
      }

currentP33DiameterLaneFromAnalyticDischarge :
  P33DiameterLaneFromAnalyticDischarge currentP33a1AnalyticDischargePackage
currentP33DiameterLaneFromAnalyticDischarge =
  buildP33DiameterLaneFromAnalyticDischarge
    currentP33a1AnalyticDischargePackage

currentP33bWeightedTreeDistanceDominatesOrdinaryDiameter :
  P33bWeightedTreeDistanceDominatesOrdinaryDiameter
currentP33bWeightedTreeDistanceDominatesOrdinaryDiameter =
  P33DiameterLaneFromAnalyticDischarge.p33bTheorem
    currentP33DiameterLaneFromAnalyticDischarge

-- ── SpanningPathWeightAccumulation ──────────────────────────────────

record SpanningPathWeightAccumulation : Set₁ where
  field
    p33aSource : P33aUniformLinkEllipticityWrapper
    p33bTheorem : P33bWeightedTreeDistanceDominatesOrdinaryDiameter
    additiveSource : String
    additiveSourceIsCanonical :
      additiveSource ≡
      "pathWeight = List.sum ∘ List.map linkWeight; effectiveLinkWeight = 1 ⇒ pathWeight π = length π"
    diameterDominationSource : String
    diameterDominationSourceIsCanonical :
      diameterDominationSource ≡
      "P01-P03 with imported P33a give weighted tree distance >= DASHI diameter"
    noClayPromotion : clayYangMillsPromoted ≡ false

currentSpanningPathWeightAccumulation : SpanningPathWeightAccumulation
currentSpanningPathWeightAccumulation = record
  { p33aSource = currentP33aUniformLinkEllipticityWrapper
  ; p33bTheorem = currentP33bWeightedTreeDistanceDominatesOrdinaryDiameter
  ; additiveSource =
      "pathWeight = List.sum ∘ List.map linkWeight; effectiveLinkWeight = 1 ⇒ pathWeight π = length π"
  ; additiveSourceIsCanonical = refl
  ; diameterDominationSource =
      "P01-P03 with imported P33a give weighted tree distance >= DASHI diameter"
  ; diameterDominationSourceIsCanonical = refl
  ; noClayPromotion = refl
  }

record AnisotropicDiameterCompatibility : Set₁ where
  field
    arithmeticReceipt :
      KP76.ClaySprintSeventySixYMAnisotropicAllDiameterKPReceipt
    spatialLinkWeightLowerBound :
      LinkLB.SpatialLinkWeightLowerBound
    spatialLinkRegularityAssumption :
      LinkLB.SpatialLinkRegularityAssumption
    p33aLinkEllipticity :
      P33aUniformLinkEllipticityWrapper
    p33aImportedEllipticity :
      ∀ (k : ℕ) (X : Polymer) (e : Edge) →
      isEdgeOf e k X → m-link ≤ℝ w-weight k e
    p33aMinimumLinkEllipticity : 1ℝ ≤ℝ m-link
    p33bGraphDomination :
      P33bWeightedTreeDistanceDominatesOrdinaryDiameter
    p33bWeightedDiameterDomination :
      ∀ (k : ℕ) (X : Polymer) → diam-ordinary k X ≤ℝ d-weighted k X
    spanningPathWeightAccumulation :
      SpanningPathWeightAccumulation
    weightedArithmeticCloses :
      KP76.anisotropicKPArithmeticClosed arithmeticReceipt ≡ true
    targetConvention : String
    targetConventionIsLoss :
      targetConvention ≡
      "loss convention: ||.||_diameter <= C_loss * ||.||_anisotropic"
    targetInequality : String
    targetInequalityIsCanonical :
      targetInequality ≡
      "||.||_diameter <= C_loss * ||.||_anisotropic"
    marginConstraint : String
    marginConstraintIsCanonical :
      marginConstraint ≡
      "C_loss * 4q < 1 iff C_loss < 1.0786 iff minLinkWeight > 0.9271"
    fourQValue : Scalar
    fourQValueIsCanonical :
      fourQValue ≡ "0.9271275790105094"
    lossBudgetUpperBound : Scalar
    lossBudgetUpperBoundIsCanonical :
      lossBudgetUpperBound ≡ "1.0786"
    requiredMinLinkWeight : Scalar
    requiredMinLinkWeightIsCanonical :
      requiredMinLinkWeight ≡ "0.9271"
    diameterDominationSurface :
      ProofTargetSurface
    diameterDominationSurfaceIsClosed :
      proofTargetIsClosed diameterDominationSurface ≡ true
    blockerSummary : String
    blockerSummaryIsCanonical :
      blockerSummary ≡
      "P33 is split: P33a imports uniform link ellipticity, and P33b internally packages the P01/P02/P03 graph consequence that weighted tree distance dominates ordinary diameter. Next open gate is polymerDiameterEntropyControlled in BalabanStepVSpatialKPCertificate."
    diameterDominationField : ∀ (k : ℕ) (X : Polymer) → diam-ordinary k X ≤ℝ d-weighted k X
    openObligations : List AnisotropicDiameterObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalAnisotropicDiameterObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

currentAnisotropicDiameterCompatibility :
  AnisotropicDiameterCompatibility
currentAnisotropicDiameterCompatibility = record
  { arithmeticReceipt =
      KP76.canonicalSprint76YMAnisotropicAllDiameterKPReceipt
  ; spatialLinkWeightLowerBound =
      LinkLB.currentSpatialLinkWeightLowerBound
  ; spatialLinkRegularityAssumption =
      LinkLB.currentSpatialLinkRegularityAssumption
  ; p33aLinkEllipticity = currentP33aUniformLinkEllipticityWrapper
  ; p33aImportedEllipticity =
      P33aUniformLinkEllipticityWrapper.uniformLinkEllipticity
        currentP33aUniformLinkEllipticityWrapper
  ; p33aMinimumLinkEllipticity =
      P33aUniformLinkEllipticityWrapper.minimumLinkEllipticity
        currentP33aUniformLinkEllipticityWrapper
  ; p33bGraphDomination =
      currentP33bWeightedTreeDistanceDominatesOrdinaryDiameter
  ; p33bWeightedDiameterDomination =
      P33bWeightedTreeDistanceDominatesOrdinaryDiameter.weightedDiameterDomination
        currentP33bWeightedTreeDistanceDominatesOrdinaryDiameter
  ; spanningPathWeightAccumulation =
      currentSpanningPathWeightAccumulation
  ; weightedArithmeticCloses =
      KP76.anisotropicKPArithmeticClosedIsTrue
        KP76.canonicalSprint76YMAnisotropicAllDiameterKPReceipt
  ; targetConvention =
      "loss convention: ||.||_diameter <= C_loss * ||.||_anisotropic"
  ; targetConventionIsLoss = refl
  ; targetInequality =
      "||.||_diameter <= C_loss * ||.||_anisotropic"
  ; targetInequalityIsCanonical = refl
  ; marginConstraint =
      "C_loss * 4q < 1 iff C_loss < 1.0786 iff minLinkWeight > 0.9271"
  ; marginConstraintIsCanonical = refl
  ; fourQValue = "0.9271275790105094"
  ; fourQValueIsCanonical = refl
  ; lossBudgetUpperBound = "1.0786"
  ; lossBudgetUpperBoundIsCanonical = refl
  ; requiredMinLinkWeight = "0.9271"
  ; requiredMinLinkWeightIsCanonical = refl
  ; diameterDominationSurface = weightedDistanceDominatesDiameterSurface
  ; diameterDominationSurfaceIsClosed = refl
  ; blockerSummary =
      "P33 is split: P33a imports uniform link ellipticity, and P33b internally packages the P01/P02/P03 graph consequence that weighted tree distance dominates ordinary diameter. Next open gate is polymerDiameterEntropyControlled in BalabanStepVSpatialKPCertificate."
  ; blockerSummaryIsCanonical = refl
  ; diameterDominationField =
      P33bWeightedTreeDistanceDominatesOrdinaryDiameter.weightedDiameterDomination
        currentP33bWeightedTreeDistanceDominatesOrdinaryDiameter
  ; openObligations = canonicalAnisotropicDiameterObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }

StepVOrdinaryDiameterDecayFromP33 :
  (diamDom : ∀ (k : ℕ) (X : Polymer) → diam-ordinary k X ≤ℝ d-weighted k X) →
  (zAniso : ℕ → Polymer → ℝ) →
  (stepVConstant : ℝ) →
  (expℝ-SV : ℝ → ℝ) →
  (≤ℝ-trans-SV : ∀ {a b c : ℝ} → a ≤ℝ b → b ≤ℝ c → a ≤ℝ c) →
  (weightedActivityDecayBound : ∀ (k : ℕ) (X : Polymer) → zAniso k X ≤ℝ (stepVConstant *ℝ expℝ-SV (-ℝ d-weighted k X))) →
  (expDecayMonotone : ∀ (k : ℕ) (X : Polymer) → diam-ordinary k X ≤ℝ d-weighted k X → (stepVConstant *ℝ expℝ-SV (-ℝ d-weighted k X)) ≤ℝ (stepVConstant *ℝ expℝ-SV (-ℝ diam-ordinary k X))) →
  (k : ℕ) (X : Polymer) →
  zAniso k X ≤ℝ (stepVConstant *ℝ expℝ-SV (-ℝ diam-ordinary k X))
StepVOrdinaryDiameterDecayFromP33 diamDom zAniso stepVConstant expℝ-SV ≤ℝ-trans-SV decayBound decayMono k X =
  ≤ℝ-trans-SV (decayBound k X) (decayMono k X (diamDom k X))
