module DASHI.Physics.Foundations.SheldrakeFieldLevinFilsingerConsolidationExact where

-- SOURCE / AUTHORITY:
-- Rupert Sheldrake, user-supplied Galton-board interview transcript (2026-11-21
-- conversation), explanation of fields, morphic resonance and cross-history
-- similarity. These are attributed hypotheses, NOT a field detection.
-- Michael Levin's pattern memory and Filsinger/Smith source claims remain
-- independently attributed in their original repository owners.
-- This module is a DASHI consolidation: it never grants a physical mechanism
-- merely because two typed mathematical carriers share a form.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.LevinBioelectricAgencyCore as Levin
import DASHI.Biology.Levin.FungalCollectiveIntelligenceCore as Fungal
import DASHI.Biology.Levin.TravelingFieldControl as Traveling
import DASHI.Physics.Foundations.SameObjectConservationLedgerExact as Ledger
import DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact as Retarded
import DASHI.Physics.Motors.SmithFilsingerSunEarthCoupledSourceExact as Source
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Upper
import DASHI.Physics.ExoticGravity.AntigravityClaimScopedExperimentalCutExact as Anti

------------------------------------------------------------------------
-- Reuse the ACTUAL master owners, not replacement field / memory objects.
-- The original records already enforce domain-specific limitations.
------------------------------------------------------------------------

record SourceNativePrimaryOwners : Set where
  field
    levin : Levin.LevinBioelectricAgencyCore
    levinIsNative : levin ≡ Levin.canonicalLevinBioelectricAgencyCore
    fungal : Fungal.FungalCollectiveIntelligenceCore
    fungalIsNative : fungal ≡ Fungal.canonicalFungalCollectiveIntelligenceCore
    travelingField : Traveling.FieldControlBoundary
    travelingFieldIsNative :
      travelingField ≡ Traveling.canonicalFieldControlBoundary
    energy : Ledger.EnergyLedger
    energyIsNative : energy ≡ Ledger.canonicalEnergyLedger
    antigravityCut : Anti.ClaimScopedCutBoundary
    antigravityCutIsNative :
      antigravityCut ≡ Anti.canonicalClaimScopedCutBoundary

canonicalPrimaryOwners : SourceNativePrimaryOwners
canonicalPrimaryOwners = record
  { levin = Levin.canonicalLevinBioelectricAgencyCore
  ; levinIsNative = refl
  ; fungal = Fungal.canonicalFungalCollectiveIntelligenceCore
  ; fungalIsNative = refl
  ; travelingField = Traveling.canonicalFieldControlBoundary
  ; travelingFieldIsNative = refl
  ; energy = Ledger.canonicalEnergyLedger
  ; energyIsNative = refl
  ; antigravityCut = Anti.canonicalClaimScopedCutBoundary
  ; antigravityCutIsNative = refl
  }

------------------------------------------------------------------------
-- Original Filsinger/source results are re-exported, with their actual
-- conditional premises. A zero-work output theorem is NOT field creation.
------------------------------------------------------------------------

retardedArrivalNotBeforeLaunch :
  (f : Retarded.RetardedFlight) →
  Upper._≤_ (Retarded.RetardedFlight.launch f)
             (Retarded.RetardedFlight.arrival f)
retardedArrivalNotBeforeLaunch = Retarded.arrivalNoEarlier

selectedBoundaryUsefulWorkCeiling :
  (b : Source.NonnegativeBoundaryWork) →
  Source._≤_ (Source.NonnegativeBoundaryWork.usefulLoad b)
    (Source.NonnegativeBoundaryWork.sunPhotons b +
      (Source.NonnegativeBoundaryWork.solarWind b +
        (Source.NonnegativeBoundaryWork.atmosphere b +
          (Source.NonnegativeBoundaryWork.pump b +
            Source.NonnegativeBoundaryWork.initialStorageRelease b))))
selectedBoundaryUsefulWorkCeiling = Source.loadWorkBound

zeroInputZeroStorageForbidsPositiveUsefulWork :
  (load loss : Nat) → zero ≡ load + loss → load ≡ zero
zeroInputZeroStorageForbidsPositiveUsefulWork = Source.sourceFreeLoadZero

------------------------------------------------------------------------
-- Exact four-path Galton-board observation quotient (synthetic only).
-- A local path reassignment can change the output histogram while the
-- normalized path count is unchanged. This is NOT a magnetic field solver,
-- magnet energy calculation, or evidence for a new nonlocal effect.
------------------------------------------------------------------------

data Bin : Set where left middle right : Bin

data TwoPegPath : Set where LL LR RL RR : TwoPegPath

unperturbed : TwoPegPath → Bin
unperturbed LL = left
unperturbed LR = middle
unperturbed RL = middle
unperturbed RR = right

illustrativeDeflection : TwoPegPath → Bin
illustrativeDeflection LL = middle
illustrativeDeflection LR = middle
illustrativeDeflection RL = middle
illustrativeDeflection RR = right

sameBin : Bin → Bin → Bool
sameBin left left = true
sameBin middle middle = true
sameBin right right = true
sameBin _ _ = false

indicator : Bool → Nat
indicator true = suc zero
indicator false = zero

countBin : (TwoPegPath → Bin) → Bin → Nat
countBin f b =
  indicator (sameBin (f LL) b) +
    (indicator (sameBin (f LR) b) +
      (indicator (sameBin (f RL) b) +
        indicator (sameBin (f RR) b)))

referenceCounts :
  countBin unperturbed left ≡ suc zero
referenceCounts = refl

referenceMiddleCounts :
  countBin unperturbed middle ≡ suc (suc zero)
referenceMiddleCounts = refl

referenceRightCounts :
  countBin unperturbed right ≡ suc zero
referenceRightCounts = refl

changedLeftCounts :
  countBin illustrativeDeflection left ≡ zero
changedLeftCounts = refl

changedMiddleCounts :
  countBin illustrativeDeflection middle ≡ suc (suc (suc zero))
changedMiddleCounts = refl

changedRightCounts :
  countBin illustrativeDeflection right ≡ suc zero
changedRightCounts = refl

------------------------------------------------------------------------
-- Different mechanism claims MUST remain different typed hypotheses.
------------------------------------------------------------------------

data ExplanationFamily : Set where
  measuredLocalElectromagnetism : ExplanationFamily
  localBioelectricPatternControl : ExplanationFamily
  apparatusSourceBackaction : ExplanationFamily
  claimScopedAntigravity : ExplanationFamily
  hypotheticalCrossPopulationResonance : ExplanationFamily

data Impossible : Set where

morphicIsNotDefinitionallyMagnetic :
  hypotheticalCrossPopulationResonance ≡ measuredLocalElectromagnetism → Impossible
morphicIsNotDefinitionallyMagnetic ()

morphicIsNotDefinitionallyLevinControl :
  hypotheticalCrossPopulationResonance ≡ localBioelectricPatternControl → Impossible
morphicIsNotDefinitionallyLevinControl ()

morphicIsNotDefinitionallyAntigravity :
  hypotheticalCrossPopulationResonance ≡ claimScopedAntigravity → Impossible
morphicIsNotDefinitionallyAntigravity ()

-- A candidate is a pair of distinguishable prediction functions with a
-- separate cross-population similarity-history input. Nothing here provides
-- a measurement, physical influence channel, signal or fitted coefficient.
record CrossPopulationRivalKernel
    (Population Time LocalHistory SimilarityHistory Outcome : Set) : Set where
  field
    ordinaryPrediction : Population → Time → LocalHistory → Outcome
    candidatePrediction :
      Population → Time → LocalHistory → SimilarityHistory → Outcome
    sourceIdentityReference : String
    hiddenLocalChannelAuditReference : String
    independentlyBlindedProtocolReference : String

-- No constructor of this type is supplied by the consolidation. Requiring
-- one in a future empirical consumer prevents promoting a synthetically
-- changed probability distribution to an observed nonlocal mechanism.
data EmpiricallyAdmittedMorphicMechanism : Set where

noAutomaticMorphicPromotion :
  EmpiricallyAdmittedMorphicMechanism → Impossible
noAutomaticMorphicPromotion ()
