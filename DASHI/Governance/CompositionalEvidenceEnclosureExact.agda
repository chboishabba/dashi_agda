module DASHI.Governance.CompositionalEvidenceEnclosureExact where

------------------------------------------------------------------------
-- SOURCE / CROSS-POLLINATION CALIBRATION
--
-- Authors: Ramon E. Moore; R. Baker Kearfott; Michael J. Cloud.
-- Title: "Introduction to Interval Analysis".
-- Publisher: SIAM, 2009.
-- DOI: 10.1137/1.9780898717716.
--
-- The source supplies interval/enclosure vocabulary.  The abstract ordered
-- evidence carrier and compositional theorem below are DASHI constructions.
--
-- Internal producer pollen:
--   * YM PR #554 replaces opaque target receipts with local enclosures and
--     proves the target bound compositionally;
--   * governance currently has evidence gates and epistemic trits, but should
--     not invent scalar credibility scores merely to mimic numerical analysis.
--
-- Accordingly this module requires a case-specific ordered evidence carrier.
-- It does NOT impose an order on EpistemicTrit and does NOT assign empirical
-- probabilities or credibility numbers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

record OrderedEvidence : Set₁ where
  constructor orderedEvidence
  field
    Level : Set
    _≤E_ : Level → Level → Set
    reflexive : (x : Level) → x ≤E x
    transitive :
      ∀ {x y z} → x ≤E y → y ≤E z → x ≤E z

open OrderedEvidence public

record EvidenceEnclosure
  (O : OrderedEvidence)
  (actual : Level O) : Set where
  constructor evidenceEnclosure
  field
    lower upper : Level O
    lowerSound : _≤E_ O lower actual
    upperSound : _≤E_ O actual upper

open EvidenceEnclosure public

record MonotoneEvidenceAggregator
  (O : OrderedEvidence) : Set₁ where
  constructor monotoneEvidenceAggregator
  field
    combine : Level O → Level O → Level O
    monotone :
      ∀ {leftLow leftHigh rightLow rightHigh} →
      _≤E_ O leftLow leftHigh →
      _≤E_ O rightLow rightHigh →
      _≤E_ O
        (combine leftLow rightLow)
        (combine leftHigh rightHigh)

open MonotoneEvidenceAggregator public

combineEnclosures :
  ∀ {O : OrderedEvidence}
    (A : MonotoneEvidenceAggregator O)
    {leftActual rightActual : Level O} →
  EvidenceEnclosure O leftActual →
  EvidenceEnclosure O rightActual →
  EvidenceEnclosure O (combine A leftActual rightActual)
combineEnclosures A leftBox rightBox =
  evidenceEnclosure
    (combine A (lower leftBox) (lower rightBox))
    (combine A (upper leftBox) (upper rightBox))
    (monotone A (lowerSound leftBox) (lowerSound rightBox))
    (monotone A (upperSound leftBox) (upperSound rightBox))

record CompositionalEvidenceReceipt
  (O : OrderedEvidence) : Set₁ where
  constructor compositionalEvidenceReceipt
  field
    aggregator : MonotoneEvidenceAggregator O
    localEvidenceConstructed : Bool
    aggregateBoundSuppliedAsIndependentTargetReceipt : Bool

canonicalCompositionalBoundaryReceipt :
  ∀ {O : OrderedEvidence} →
  MonotoneEvidenceAggregator O →
  CompositionalEvidenceReceipt O
canonicalCompositionalBoundaryReceipt aggregator =
  compositionalEvidenceReceipt aggregator true false

------------------------------------------------------------------------
-- Exact Nat regression: [1,3] encloses 2 and [2,4] encloses 3.  Monotone
-- addition derives [3,7] around the aggregate value 5.
------------------------------------------------------------------------

natEvidenceOrder : OrderedEvidence
natEvidenceOrder =
  orderedEvidence
    Nat
    _≤_
    (λ x → ≤-refl)
    (λ lower middle → ≤-trans lower middle)

natAdditionAggregator : MonotoneEvidenceAggregator natEvidenceOrder
natAdditionAggregator =
  monotoneEvidenceAggregator
    _+_
    (λ left right → +-mono-≤ left right)

twoBox : EvidenceEnclosure natEvidenceOrder 2
twoBox =
  evidenceEnclosure
    1
    3
    (s≤s z≤n)
    (s≤s (s≤s z≤n))

threeBox : EvidenceEnclosure natEvidenceOrder 3
threeBox =
  evidenceEnclosure
    2
    4
    (s≤s (s≤s z≤n))
    (s≤s (s≤s (s≤s z≤n)))

fiveBox : EvidenceEnclosure natEvidenceOrder 5
fiveBox = combineEnclosures natAdditionAggregator twoBox threeBox

fiveBoxLowerIsThree : lower fiveBox ≡ 3
fiveBoxLowerIsThree = refl

fiveBoxUpperIsSeven : upper fiveBox ≡ 7
fiveBoxUpperIsSeven = refl

record EvidenceEnclosureBoundary : Set where
  constructor evidenceEnclosureBoundary
  field
    localBoundsCanComposeWithoutTargetReceipt : Bool
    epistemicTritHasCanonicalNumericOrderHere : Bool
    enclosureEqualsProbabilityInterval : Bool
    caseSpecificOrderRequired : Bool
    monotonicityRequiredForGenericComposition : Bool

canonicalEvidenceEnclosureBoundary : EvidenceEnclosureBoundary
canonicalEvidenceEnclosureBoundary =
  evidenceEnclosureBoundary true false false true true

record EvidenceEnclosureSourceReceipt : Set where
  constructor evidenceEnclosureSourceReceipt
  field
    sources : List Sources.ScholarlySource
    boundary : EvidenceEnclosureBoundary

canonicalEvidenceEnclosureSourceReceipt : EvidenceEnclosureSourceReceipt
canonicalEvidenceEnclosureSourceReceipt =
  evidenceEnclosureSourceReceipt
    (Sources.mooreKearfottCloudIntervalAnalysis ∷ [])
    canonicalEvidenceEnclosureBoundary
