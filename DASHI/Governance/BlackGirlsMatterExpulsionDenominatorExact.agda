module DASHI.Governance.BlackGirlsMatterExpulsionDenominatorExact where

-- SOURCE: Black Girls Matter (Crenshaw with Ocen and Nanda, 2015),
-- printed page 21, expulsion rates narrative and Figure 6.
-- In the two reported districts, no white girls were recorded as expelled;
-- the authors illustrate the ratio by COUNTERFACTUALLY assuming one.
-- The number 53:1 (NYC) or 10:1 (Boston) is thus not a directly observed
-- ratio with a positive white-girl count, nor a per-enrollee risk ratio.
-- This finite arithmetic/typed distinction is original to DASHI.
open import DASHI.Core.Prelude

data District : Set where
  newYorkCity boston : District

data DenominatorStatus : Set where
  actualZero hypotheticalOne : DenominatorStatus

whiteGirlExpulsionCount : District → DenominatorStatus → Nat
whiteGirlExpulsionCount newYorkCity actualZero = 0
whiteGirlExpulsionCount newYorkCity hypotheticalOne = 1
whiteGirlExpulsionCount boston actualZero = 0
whiteGirlExpulsionCount boston hypotheticalOne = 1

reportedBlackGirlExpulsions : District → Nat
reportedBlackGirlExpulsions newYorkCity = 53
reportedBlackGirlExpulsions boston = 10

newYorkWhiteGirlActualCountIsZero :
  whiteGirlExpulsionCount newYorkCity actualZero ≡ 0
newYorkWhiteGirlActualCountIsZero = refl

bostonWhiteGirlActualCountIsZero :
  whiteGirlExpulsionCount boston actualZero ≡ 0
bostonWhiteGirlActualCountIsZero = refl

newYorkAuthorsHypotheticalFiftyThreeToOne :
  reportedBlackGirlExpulsions newYorkCity ≡
    53 * whiteGirlExpulsionCount newYorkCity hypotheticalOne
newYorkAuthorsHypotheticalFiftyThreeToOne = refl

bostonAuthorsHypotheticalTenToOne :
  reportedBlackGirlExpulsions boston ≡
    10 * whiteGirlExpulsionCount boston hypotheticalOne
bostonAuthorsHypotheticalTenToOne = refl

data RatioEvidenceKind : Set where
  observedPositiveDenominator counterfactualOneDenominator : RatioEvidenceKind

reportedRatioEvidence : District → RatioEvidenceKind
reportedRatioEvidence _ = counterfactualOneDenominator

newYorkRatioIsHypotheticalNotObserved :
  reportedRatioEvidence newYorkCity ≡ observedPositiveDenominator → ⊥
newYorkRatioIsHypotheticalNotObserved ()

bostonRatioIsHypotheticalNotObserved :
  reportedRatioEvidence boston ≡ observedPositiveDenominator → ⊥
bostonRatioIsHypotheticalNotObserved ()

-- An actual *positive* comparison denominator is needed to produce
-- a conventional finite ratio from counts. It is not implied by adding
-- an illustrative pseudocount; no real-world denominator was observed.
record ObservedRatioAdmission (d : District) : Set where
  constructor observed-ratio-admission
  field
    actualWhiteExpulsions : Nat
    sourceCountMatched :
      actualWhiteExpulsions ≡ whiteGirlExpulsionCount d actualZero
    positiveDenominator : Nat
    denominatorPositive :
      actualWhiteExpulsions ≡ suc positiveDenominator

open ObservedRatioAdmission public

newYorkObservedExpulsionRatioBlocked :
  ObservedRatioAdmission newYorkCity → ⊥
newYorkObservedExpulsionRatioBlocked receipt
  with sourceCountMatched receipt
... | refl with denominatorPositive receipt
... | ()

bostonObservedExpulsionRatioBlocked :
  ObservedRatioAdmission boston → ⊥
bostonObservedExpulsionRatioBlocked receipt
  with sourceCountMatched receipt
... | refl with denominatorPositive receipt
... | ()

-- This does not say the disparity is unreal; it rules out the unsupported
-- precision of treating the illustrative pseudocount as an observed ratio.
