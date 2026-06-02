module DASHI.Physics.Closure.Gate3AtomSamplerPAWOTGQualityReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Gate3DigitExpansionPAWOTGPartialResultReceipt
  as Digit
import DASHI.Physics.Closure.Gate3PAWOTGUniformSeparationTargetReceipt
  as Target
import DASHI.Physics.Closure.MonsterMoonshineSSPQuotientControlReceipt
  as MonsterQuotient

------------------------------------------------------------------------
-- Gate 3 atom-sampler PAWOTG quality receipt.
--
-- The current finite-frame sampler is not a PAWOTG-quality sampler.  The
-- finite sweeps show max cross-term mu_N close to one, exploding frame ratios,
-- and negative Gershgorin lower bounds at every tested N.  The next sampler
-- target is quasi-uniform phase/twist placement with mu_N <= C/N, or at least
-- (N-1) mu_N < 1 for a Gershgorin-style lower frame bound.

data Gate3AtomSamplerPAWOTGQualityStatus : Set where
  gate3AtomSamplerQualityObstructionRecorded_noPromotion :
    Gate3AtomSamplerPAWOTGQualityStatus

data AtomSamplerObservation : Set where
  currentSamplerMuNearOne :
    AtomSamplerObservation

  gershgorinLowerBoundNegativeEverywhere :
    AtomSamplerObservation

  phaseCompleteHelpsAtSmallNOnly :
    AtomSamplerObservation

  bothToyDictionariesCollapseAtLargerN :
    AtomSamplerObservation

  maxFrameRatioLarge :
    AtomSamplerObservation

canonicalAtomSamplerObservations :
  List AtomSamplerObservation
canonicalAtomSamplerObservations =
  currentSamplerMuNearOne
  ∷ gershgorinLowerBoundNegativeEverywhere
  ∷ phaseCompleteHelpsAtSmallNOnly
  ∷ bothToyDictionariesCollapseAtLargerN
  ∷ maxFrameRatioLarge
  ∷ []

data AtomSamplerQualityTarget : Set where
  quasiUniformPhaseTwistPlacement :
    AtomSamplerQualityTarget

  muNBoundedByConstantOverN :
    AtomSamplerQualityTarget

  gershgorinProductBelowOne :
    AtomSamplerQualityTarget

  phaseAndTwistIncludedBeforeFrameClaim :
    AtomSamplerQualityTarget

  monsterMultiplicityQuotientedBeforeOverlapCount :
    AtomSamplerQualityTarget

canonicalAtomSamplerQualityTargets :
  List AtomSamplerQualityTarget
canonicalAtomSamplerQualityTargets =
  quasiUniformPhaseTwistPlacement
  ∷ muNBoundedByConstantOverN
  ∷ gershgorinProductBelowOne
  ∷ phaseAndTwistIncludedBeforeFrameClaim
  ∷ monsterMultiplicityQuotientedBeforeOverlapCount
  ∷ []

data Gate3SamplerPromotion : Set where

gate3SamplerPromotionImpossibleHere :
  Gate3SamplerPromotion →
  ⊥
gate3SamplerPromotionImpossibleHere ()

muMinHundredths :
  Nat
muMinHundredths =
  93

muMaxHundredths :
  Nat
muMaxHundredths =
  100

maxFrameRatioScientificMantissa :
  Nat
maxFrameRatioScientificMantissa =
  273

maxFrameRatioScientificExponent :
  Nat
maxFrameRatioScientificExponent =
  16

monsterSqrtLeakSigmaCritP3TenThousandths :
  Nat
monsterSqrtLeakSigmaCritP3TenThousandths =
  2960

monsterRawLeakSigmaCritP3TenThousandths :
  Nat
monsterRawLeakSigmaCritP3TenThousandths =
  2283

samplerObservationStatement :
  String
samplerObservationStatement =
  "Current Gate3 atom sampler clusters badly: mu_N is about 0.93 to 1.00, (N-1)mu_N is far above 1, Gershgorin lower bounds are negative, and A_N collapses numerically."

samplerTargetStatement :
  String
samplerTargetStatement =
  "Replace the sampler with PAWOTG-quality quasi-uniform phase/twist placement satisfying mu_N <= C/N, or at least (N-1)mu_N < 1 for finite-cutoff lower-bound tests."

monsterEntropyStatement :
  String
monsterEntropyStatement =
  "If Monster multiplicity leaks into Gate3 overlap entropy, the p=3 sigma threshold tightens from 0.5052 toward about 0.296 or 0.228; quotient control remains load-bearing."

promotionBoundary :
  String
promotionBoundary =
  "This receipt records the sampler-quality obstruction and target only.  It does not prove PAWOTG for the SSP sampler, inf_N A_N > 0, Gate 3 closure, or Clay."

record Gate3AtomSamplerPAWOTGQualityReceipt : Setω where
  field
    status :
      Gate3AtomSamplerPAWOTGQualityStatus

    statusIsCanonical :
      status ≡ gate3AtomSamplerQualityObstructionRecorded_noPromotion

    digitExpansionReceipt :
      Digit.Gate3DigitExpansionPAWOTGPartialResultReceipt

    digitExpansionPassesThreshold :
      Digit.phiDigitPassesPAWOTGThreshold digitExpansionReceipt ≡ true

    digitExpansionNoGate3Promotion :
      Digit.gate3Promoted digitExpansionReceipt ≡ false

    uniformSeparationTarget :
      Target.Gate3PAWOTGUniformSeparationTargetReceipt

    infANStillOpen :
      Target.infANPositiveProvedHere uniformSeparationTarget ≡ false

    targetNoGate3Promotion :
      Target.gate3Promoted uniformSeparationTarget ≡ false

    monsterQuotientReceipt :
      MonsterQuotient.MonsterMoonshineSSPQuotientControlReceipt

    monsterQuotientStillOpen :
      MonsterQuotient.quotientEntropyBoundProvedHere
        monsterQuotientReceipt
      ≡
      false

    observations :
      List AtomSamplerObservation

    observationsAreCanonical :
      observations ≡ canonicalAtomSamplerObservations

    targets :
      List AtomSamplerQualityTarget

    targetsAreCanonical :
      targets ≡ canonicalAtomSamplerQualityTargets

    muMin :
      Nat

    muMinIs093 :
      muMin ≡ muMinHundredths

    muMax :
      Nat

    muMaxIs100 :
      muMax ≡ muMaxHundredths

    maxFrameRatioMantissa :
      Nat

    maxFrameRatioMantissaIs273 :
      maxFrameRatioMantissa ≡ maxFrameRatioScientificMantissa

    maxFrameRatioExponent :
      Nat

    maxFrameRatioExponentIs16 :
      maxFrameRatioExponent ≡ maxFrameRatioScientificExponent

    monsterSqrtLeakSigmaCritP3 :
      Nat

    monsterSqrtLeakSigmaCritP3Is02960 :
      monsterSqrtLeakSigmaCritP3
      ≡
      monsterSqrtLeakSigmaCritP3TenThousandths

    monsterRawLeakSigmaCritP3 :
      Nat

    monsterRawLeakSigmaCritP3Is02283 :
      monsterRawLeakSigmaCritP3
      ≡
      monsterRawLeakSigmaCritP3TenThousandths

    currentSamplerSatisfiesPAWOTGQuality :
      Bool

    currentSamplerSatisfiesPAWOTGQualityIsFalse :
      currentSamplerSatisfiesPAWOTGQuality ≡ false

    replacementSamplerRequired :
      Bool

    replacementSamplerRequiredIsTrue :
      replacementSamplerRequired ≡ true

    uniformFrameLowerBoundProvedHere :
      Bool

    uniformFrameLowerBoundProvedHereIsFalse :
      uniformFrameLowerBoundProvedHere ≡ false

    gate3Promoted :
      Bool

    gate3PromotedIsFalse :
      gate3Promoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotions :
      List Gate3SamplerPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      Gate3SamplerPromotion →
      ⊥

    observationText :
      String

    observationTextIsCanonical :
      observationText ≡ samplerObservationStatement

    targetText :
      String

    targetTextIsCanonical :
      targetText ≡ samplerTargetStatement

    monsterEntropyText :
      String

    monsterEntropyTextIsCanonical :
      monsterEntropyText ≡ monsterEntropyStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ promotionBoundary

open Gate3AtomSamplerPAWOTGQualityReceipt public

canonicalGate3AtomSamplerPAWOTGQualityReceipt :
  Gate3AtomSamplerPAWOTGQualityReceipt
canonicalGate3AtomSamplerPAWOTGQualityReceipt =
  record
    { status =
        gate3AtomSamplerQualityObstructionRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; digitExpansionReceipt =
        Digit.canonicalGate3DigitExpansionPAWOTGPartialResultReceipt
    ; digitExpansionPassesThreshold =
        refl
    ; digitExpansionNoGate3Promotion =
        refl
    ; uniformSeparationTarget =
        Target.canonicalGate3PAWOTGUniformSeparationTargetReceipt
    ; infANStillOpen =
        refl
    ; targetNoGate3Promotion =
        refl
    ; monsterQuotientReceipt =
        MonsterQuotient.canonicalMonsterMoonshineSSPQuotientControlReceipt
    ; monsterQuotientStillOpen =
        refl
    ; observations =
        canonicalAtomSamplerObservations
    ; observationsAreCanonical =
        refl
    ; targets =
        canonicalAtomSamplerQualityTargets
    ; targetsAreCanonical =
        refl
    ; muMin =
        muMinHundredths
    ; muMinIs093 =
        refl
    ; muMax =
        muMaxHundredths
    ; muMaxIs100 =
        refl
    ; maxFrameRatioMantissa =
        maxFrameRatioScientificMantissa
    ; maxFrameRatioMantissaIs273 =
        refl
    ; maxFrameRatioExponent =
        maxFrameRatioScientificExponent
    ; maxFrameRatioExponentIs16 =
        refl
    ; monsterSqrtLeakSigmaCritP3 =
        monsterSqrtLeakSigmaCritP3TenThousandths
    ; monsterSqrtLeakSigmaCritP3Is02960 =
        refl
    ; monsterRawLeakSigmaCritP3 =
        monsterRawLeakSigmaCritP3TenThousandths
    ; monsterRawLeakSigmaCritP3Is02283 =
        refl
    ; currentSamplerSatisfiesPAWOTGQuality =
        false
    ; currentSamplerSatisfiesPAWOTGQualityIsFalse =
        refl
    ; replacementSamplerRequired =
        true
    ; replacementSamplerRequiredIsTrue =
        refl
    ; uniformFrameLowerBoundProvedHere =
        false
    ; uniformFrameLowerBoundProvedHereIsFalse =
        refl
    ; gate3Promoted =
        false
    ; gate3PromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        gate3SamplerPromotionImpossibleHere
    ; observationText =
        samplerObservationStatement
    ; observationTextIsCanonical =
        refl
    ; targetText =
        samplerTargetStatement
    ; targetTextIsCanonical =
        refl
    ; monsterEntropyText =
        monsterEntropyStatement
    ; monsterEntropyTextIsCanonical =
        refl
    ; boundary =
        promotionBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalGate3SamplerQualityFailsCurrentSampler :
  currentSamplerSatisfiesPAWOTGQuality
    canonicalGate3AtomSamplerPAWOTGQualityReceipt
  ≡
  false
canonicalGate3SamplerQualityFailsCurrentSampler =
  refl

canonicalGate3SamplerQualityNoPromotion :
  gate3Promoted canonicalGate3AtomSamplerPAWOTGQualityReceipt ≡ false
canonicalGate3SamplerQualityNoPromotion =
  refl
