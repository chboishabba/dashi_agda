module DASHI.Foundations.SSPTritCarrier where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)
import DASHI.Algebra.Trit as Trit

------------------------------------------------------------------------
-- Canonical SSP trit carrier.
--
-- The carrier values are the typed trits -1, 0, +1.  The module keeps the
-- labels and polarity/neutral classifiers explicit so downstream odd-lane and
-- Base369 bridges can reuse the same surface without re-encoding the values.

data SSPTrit : Set where
  sspNegOne :
    SSPTrit

  sspZero :
    SSPTrit

  sspPosOne :
    SSPTrit

data SSPTritCarrierStatus : Set where
  canonicalSSPTritCarrierRecorded :
    SSPTritCarrierStatus

data SSPTritSemanticLabel : Set where
  minusOneLabel :
    SSPTritSemanticLabel

  zeroLabel :
    SSPTritSemanticLabel

  plusOneLabel :
    SSPTritSemanticLabel

canonicalSSPTritSemanticLabels :
  List SSPTritSemanticLabel
canonicalSSPTritSemanticLabels =
  minusOneLabel ∷ zeroLabel ∷ plusOneLabel ∷ []

sspTritSemanticLabelText :
  SSPTritSemanticLabel →
  String
sspTritSemanticLabelText minusOneLabel = "-1"
sspTritSemanticLabelText zeroLabel = "0"
sspTritSemanticLabelText plusOneLabel = "+1"

sspTritSemanticLabel :
  SSPTrit →
  SSPTritSemanticLabel
sspTritSemanticLabel sspNegOne = minusOneLabel
sspTritSemanticLabel sspZero = zeroLabel
sspTritSemanticLabel sspPosOne = plusOneLabel

sspTritLabelText :
  SSPTrit →
  String
sspTritLabelText t = sspTritSemanticLabelText (sspTritSemanticLabel t)

data SSPTritPolarity : Set where
  negativePolarity :
    SSPTritPolarity

  neutralPolarity :
    SSPTritPolarity

  positivePolarity :
    SSPTritPolarity

sspTritPolarity :
  SSPTrit →
  SSPTritPolarity
sspTritPolarity sspNegOne = negativePolarity
sspTritPolarity sspZero = neutralPolarity
sspTritPolarity sspPosOne = positivePolarity

data SSPTritNeutrality : Set where
  nonNeutralSSP :
    SSPTritNeutrality

  neutralSSP :
    SSPTritNeutrality

sspTritNeutrality :
  SSPTrit →
  SSPTritNeutrality
sspTritNeutrality sspNegOne = nonNeutralSSP
sspTritNeutrality sspZero = neutralSSP
sspTritNeutrality sspPosOne = nonNeutralSSP

sspTritIsNeutral :
  SSPTrit →
  Bool
sspTritIsNeutral sspNegOne = false
sspTritIsNeutral sspZero = true
sspTritIsNeutral sspPosOne = false

data SSPTritSemanticPiece : Set where
  carrierValuesAreMinusOneZeroPlusOne :
    SSPTritSemanticPiece

  semanticLabelsAreMinusOneZeroPlusOne :
    SSPTritSemanticPiece

  polarityClassificationIsExplicit :
    SSPTritSemanticPiece

  neutralityClassificationIsExplicit :
    SSPTritSemanticPiece

  oddLaneBridgeReady :
    SSPTritSemanticPiece

  base369BridgeReady :
    SSPTritSemanticPiece

  executableRoundtrips :
    SSPTritSemanticPiece

canonicalSSPTritSemanticPieces :
  List SSPTritSemanticPiece
canonicalSSPTritSemanticPieces =
  carrierValuesAreMinusOneZeroPlusOne
  ∷ semanticLabelsAreMinusOneZeroPlusOne
  ∷ polarityClassificationIsExplicit
  ∷ neutralityClassificationIsExplicit
  ∷ oddLaneBridgeReady
  ∷ base369BridgeReady
  ∷ executableRoundtrips
  ∷ []

data _≢_ {A : Set} (x y : A) : Set where
  impossible :
    (x ≡ y → ⊥) →
    x ≢ y

_≢_-elim :
  ∀ {A : Set} {x y : A} →
  x ≢ y →
  x ≡ y →
  ⊥
_≢_-elim (impossible notEq) eq = notEq eq

sspNegOne≢sspZero :
  sspNegOne ≢ sspZero
sspNegOne≢sspZero = impossible (λ ())

sspNegOne≢sspPosOne :
  sspNegOne ≢ sspPosOne
sspNegOne≢sspPosOne = impossible (λ ())

sspZero≢sspPosOne :
  sspZero ≢ sspPosOne
sspZero≢sspPosOne = impossible (λ ())

toTrit :
  SSPTrit →
  Trit.Trit
toTrit sspNegOne = Trit.neg
toTrit sspZero = Trit.zer
toTrit sspPosOne = Trit.pos

fromTrit :
  Trit.Trit →
  SSPTrit
fromTrit Trit.neg = sspNegOne
fromTrit Trit.zer = sspZero
fromTrit Trit.pos = sspPosOne

toTrit-fromTrit :
  ∀ t →
  toTrit (fromTrit t) ≡ t
toTrit-fromTrit Trit.neg = refl
toTrit-fromTrit Trit.zer = refl
toTrit-fromTrit Trit.pos = refl

fromTrit-toTrit :
  ∀ t →
  fromTrit (toTrit t) ≡ t
fromTrit-toTrit sspNegOne = refl
fromTrit-toTrit sspZero = refl
fromTrit-toTrit sspPosOne = refl

toTriTruth :
  SSPTrit →
  TriTruth
toTriTruth sspNegOne = tri-low
toTriTruth sspZero = tri-mid
toTriTruth sspPosOne = tri-high

fromTriTruth :
  TriTruth →
  SSPTrit
fromTriTruth tri-low = sspNegOne
fromTriTruth tri-mid = sspZero
fromTriTruth tri-high = sspPosOne

toTriTruth-fromTriTruth :
  ∀ t →
  toTriTruth (fromTriTruth t) ≡ t
toTriTruth-fromTriTruth tri-low = refl
toTriTruth-fromTriTruth tri-mid = refl
toTriTruth-fromTriTruth tri-high = refl

fromTriTruth-toTriTruth :
  ∀ t →
  fromTriTruth (toTriTruth t) ≡ t
fromTriTruth-toTriTruth sspNegOne = refl
fromTriTruth-toTriTruth sspZero = refl
fromTriTruth-toTriTruth sspPosOne = refl

carrierSummary :
  String
carrierSummary =
  "SSP trit carrier with typed values -1, 0, +1; polarity and neutrality are explicit; Trit and TriTruth bridges are total."

record SSPTritCarrierReceipt : Set₁ where
  constructor mkSSPTritCarrierReceipt
  field
    status :
      SSPTritCarrierStatus

    statusIsCanonical :
      status ≡ canonicalSSPTritCarrierRecorded

    carrier :
      Set

    negativeValue :
      carrier

    neutralValue :
      carrier

    positiveValue :
      carrier

    semanticLabels :
      List SSPTritSemanticLabel

    semanticLabelsAreCanonical :
      semanticLabels ≡ canonicalSSPTritSemanticLabels

    negativeLabel :
      SSPTritSemanticLabel

    negativeLabelIsCanonical :
      negativeLabel ≡ minusOneLabel

    neutralLabel :
      SSPTritSemanticLabel

    neutralLabelIsCanonical :
      neutralLabel ≡ zeroLabel

    positiveLabel :
      SSPTritSemanticLabel

    positiveLabelIsCanonical :
      positiveLabel ≡ plusOneLabel

    polarity :
      carrier →
      SSPTritPolarity

    polarityOfNegative :
      polarity negativeValue ≡ negativePolarity

    polarityOfNeutral :
      polarity neutralValue ≡ neutralPolarity

    polarityOfPositive :
      polarity positiveValue ≡ positivePolarity

    neutrality :
      carrier →
      SSPTritNeutrality

    neutralityOfNegative :
      neutrality negativeValue ≡ nonNeutralSSP

    neutralityOfNeutral :
      neutrality neutralValue ≡ neutralSSP

    neutralityOfPositive :
      neutrality positiveValue ≡ nonNeutralSSP

    isNeutral :
      carrier →
      Bool

    isNeutralOfNegative :
      isNeutral negativeValue ≡ false

    isNeutralOfNeutral :
      isNeutral neutralValue ≡ true

    isNeutralOfPositive :
      isNeutral positiveValue ≡ false

    toTritCarrier :
      carrier →
      Trit.Trit

    fromTritCarrier :
      Trit.Trit →
      carrier

    toTritFromTrit :
      ∀ t →
      toTritCarrier (fromTritCarrier t) ≡ t

    fromTritToTrit :
      ∀ t →
      fromTritCarrier (toTritCarrier t) ≡ t

    toTriTruthCarrier :
      carrier →
      TriTruth

    fromTriTruthCarrier :
      TriTruth →
      carrier

    toTriTruthFromTriTruth :
      ∀ t →
      toTriTruthCarrier (fromTriTruthCarrier t) ≡ t

    fromTriTruthToTriTruth :
      ∀ t →
      fromTriTruthCarrier (toTriTruthCarrier t) ≡ t

    semanticPieces :
      List SSPTritSemanticPiece

    semanticPiecesAreCanonical :
      semanticPieces ≡ canonicalSSPTritSemanticPieces

    summary :
      String

    summaryIsCanonical :
      summary ≡ carrierSummary

open SSPTritCarrierReceipt public

canonicalSSPTritCarrierReceipt :
  SSPTritCarrierReceipt
canonicalSSPTritCarrierReceipt =
  mkSSPTritCarrierReceipt
    canonicalSSPTritCarrierRecorded
    refl
    SSPTrit
    sspNegOne
    sspZero
    sspPosOne
    canonicalSSPTritSemanticLabels
    refl
    minusOneLabel
    refl
    zeroLabel
    refl
    plusOneLabel
    refl
    sspTritPolarity
    refl
    refl
    refl
    sspTritNeutrality
    refl
    refl
    refl
    sspTritIsNeutral
    refl
    refl
    refl
    toTrit
    fromTrit
    toTrit-fromTrit
    fromTrit-toTrit
    toTriTruth
    fromTriTruth
    toTriTruth-fromTriTruth
    fromTriTruth-toTriTruth
    canonicalSSPTritSemanticPieces
    refl
    carrierSummary
    refl

sspTritCarrierRecorded :
  SSPTritCarrierReceipt
sspTritCarrierRecorded =
  canonicalSSPTritCarrierReceipt

sspTritCarrierStatusRecorded :
  SSPTritCarrierStatus
sspTritCarrierStatusRecorded =
  canonicalSSPTritCarrierRecorded
