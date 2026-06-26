module DASHI.Physics.YangMills.GraphCoreLemmaQueue where

-- Proof-replacement lemma queue for Sprints 1–2.
-- Implements P01–P03 graph-core lemmas and the internal composition half
-- of P33b, without pretending that the analytic P33a input is solved here.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; _≤ℝ_; _<ℝ_; 0ℝ; 1ℝ; _*ℝ_; -ℝ_)

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.YangMills.YMSupportGraphDistance as GraphDist
import DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility as ADC

lemmaP01-1-treePathExists :
  ∀ (u v : Support.Link) →
  GraphDist.Path GraphDist.currentFiniteSupportGraph
lemmaP01-1-treePathExists = GraphDist.ymTreePath

lemmaP01-2-spanningTreePathValid :
  ∀ (u v : Support.Link) →
  GraphDist.Path.valid (GraphDist.ymTreePath u v) ≡ true
lemmaP01-2-spanningTreePathValid =
  GraphDist.ImportedTreePathRealisationAxiomValid

lemmaP01-3a-treePathStart :
  ∀ (u v : Support.Link) →
  GraphDist.Path.start (GraphDist.ymTreePath u v) ≡ u
lemmaP01-3a-treePathStart =
  GraphDist.ImportedTreePathRealisationAxiomStart

lemmaP01-3b-treePathFinish :
  ∀ (u v : Support.Link) →
  GraphDist.Path.finish (GraphDist.ymTreePath u v) ≡ v
lemmaP01-3b-treePathFinish =
  GraphDist.ImportedTreePathRealisationAxiomFinish

lemmaP02-1-graphDistIsMinimum :
  ∀ (u v : Support.Link) →
  (p : GraphDist.Path GraphDist.currentFiniteSupportGraph) →
  GraphDist.Path.start p ≡ u →
  GraphDist.Path.finish p ≡ v →
  GraphDist.Path.valid p ≡ true →
  GraphDist.ymGraphDist u v ≤ GraphDist.Path.pathLength p
lemmaP02-1-graphDistIsMinimum u v p pstart pfinish pvalid =
  GraphDist.ImportedFiniteGraphDistanceAxiom p pstart pfinish pvalid

lemmaP02-2-treePathDominatesGraphDist :
  ∀ (u v : Support.Link) →
  GraphDist.ymGraphDist u v ≤
  GraphDist.Path.pathLength (GraphDist.ymTreePath u v)
lemmaP02-2-treePathDominatesGraphDist u v =
  lemmaP02-1-graphDistIsMinimum u v
    (GraphDist.ymTreePath u v)
    (lemmaP01-3a-treePathStart u v)
    (lemmaP01-3b-treePathFinish u v)
    (lemmaP01-2-spanningTreePathValid u v)

postulate
  ymDiameter : ℕ
  ymDiameterU : Support.Link
  ymDiameterV : Support.Link
  lemmaP03-1-diameterRealisingPairExists :
    GraphDist.ymGraphDist ymDiameterU ymDiameterV ≡ ymDiameter

lemmaP03-2-anyPathDominatesDiameter :
  ∀ (p : GraphDist.Path GraphDist.currentFiniteSupportGraph) →
  GraphDist.Path.start p ≡ ymDiameterU →
  GraphDist.Path.finish p ≡ ymDiameterV →
  GraphDist.Path.valid p ≡ true →
  ymDiameter ≤ GraphDist.Path.pathLength p
lemmaP03-2-anyPathDominatesDiameter p pstart pfinish pvalid =
  subst
    (λ n → n ≤ GraphDist.Path.pathLength p)
    lemmaP03-1-diameterRealisingPairExists
    (lemmaP02-1-graphDistIsMinimum ymDiameterU ymDiameterV p pstart pfinish pvalid)

postulate
  lemmaP33b-1-pathWeightLowerBound :
    ∀ (k : ℕ) (X : ADC.Polymer) →
    (∀ (e : ADC.Edge) → ADC.isEdgeOf e k X → ADC.m-link ≤ℝ ADC.w-weight k e) →
    ADC.m-link *ℝ 1ℝ ≤ℝ ADC.d-weighted k X

  lemmaP33b-2-mLinkGe1-dominates :
    1ℝ ≤ℝ ADC.m-link →
    ∀ (k : ℕ) (X : ADC.Polymer) →
    ADC.diam-ordinary k X ≤ℝ ADC.m-link *ℝ 1ℝ

  expℝ : ℝ → ℝ

  lemmaP33b-4-expAntitone :
    ∀ (κ a b : ℝ) →
    0ℝ <ℝ κ →
    b ≤ℝ a →
    expℝ (-ℝ (κ *ℝ a)) ≤ℝ expℝ (-ℝ (κ *ℝ b))

  ≤ℝ-trans : ∀ {a b c : ℝ} → a ≤ℝ b → b ≤ℝ c → a ≤ℝ c

lemmaP33b-3-weightedTreeDistDominatesDiam :
  ∀ (k : ℕ) (X : ADC.Polymer) →
  (∀ (e : ADC.Edge) → ADC.isEdgeOf e k X → ADC.m-link ≤ℝ ADC.w-weight k e) →
  1ℝ ≤ℝ ADC.m-link →
  ADC.diam-ordinary k X ≤ℝ ADC.d-weighted k X
lemmaP33b-3-weightedTreeDistDominatesDiam k X ellipticity mLinkBound =
  ≤ℝ-trans
    (lemmaP33b-2-mLinkGe1-dominates mLinkBound k X)
    (lemmaP33b-1-pathWeightLowerBound k X ellipticity)

lemmaP33b-5-anisotropicDecayDominatedByDiameterDecay :
  ∀ (k : ℕ) (X : ADC.Polymer) (κ : ℝ) →
  0ℝ <ℝ κ →
  (∀ (e : ADC.Edge) → ADC.isEdgeOf e k X → ADC.m-link ≤ℝ ADC.w-weight k e) →
  1ℝ ≤ℝ ADC.m-link →
  expℝ (-ℝ (κ *ℝ ADC.d-weighted k X)) ≤ℝ
  expℝ (-ℝ (κ *ℝ ADC.diam-ordinary k X))
lemmaP33b-5-anisotropicDecayDominatedByDiameterDecay k X κ κPos ellipticity mLinkBound =
  lemmaP33b-4-expAntitone κ (ADC.d-weighted k X) (ADC.diam-ordinary k X)
    κPos
    (lemmaP33b-3-weightedTreeDistDominatesDiam k X ellipticity mLinkBound)

record P33bDiameterDominationBundle : Set where
  field
    linkEllipticityHypothesis :
      ∀ (k : ℕ) (X : ADC.Polymer) (e : ADC.Edge) →
      ADC.isEdgeOf e k X →
      ADC.m-link ≤ℝ ADC.w-weight k e
    mLinkBoundHypothesis :
      1ℝ ≤ℝ ADC.m-link
    diameterDomination :
      ∀ (k : ℕ) (X : ADC.Polymer) →
      ADC.diam-ordinary k X ≤ℝ ADC.d-weighted k X
    proofStructure : String
    proofStructureIsCanonical :
      proofStructure ≡
      "P33b constructed from: P33b.1 (path weight LB, postulated ℝ analytic) + P33b.2 (m_link≥1 scaling, postulated) + composition gives diam ≤ d-weighted. Analytic inputs remain postulated; the logical composition is internal."
    noClayPromotion : clayYangMillsPromoted ≡ false

currentP33bDiameterDominationBundle : P33bDiameterDominationBundle
currentP33bDiameterDominationBundle = record
  { linkEllipticityHypothesis = ADC.postulatedLinkEllipticity
  ; mLinkBoundHypothesis = ADC.postulatedLinkEllipticityMin
  ; diameterDomination = λ k X →
      lemmaP33b-3-weightedTreeDistDominatesDiam k X
        (ADC.postulatedLinkEllipticity k X)
        ADC.postulatedLinkEllipticityMin
  ; proofStructure =
      "P33b constructed from: P33b.1 (path weight LB, postulated ℝ analytic) + P33b.2 (m_link≥1 scaling, postulated) + composition gives diam ≤ d-weighted. Analytic inputs remain postulated; the logical composition is internal."
  ; proofStructureIsCanonical = refl
  ; noClayPromotion = refl
  }
