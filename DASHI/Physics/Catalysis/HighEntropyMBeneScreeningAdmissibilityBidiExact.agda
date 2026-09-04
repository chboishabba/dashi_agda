module DASHI.Physics.Catalysis.HighEntropyMBeneScreeningAdmissibilityBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- HIGH-ENTROPY MBENE SCREENING AS PROOF-RELEVANT ADMISSIBILITY
--
-- The reported 56 -> 18 -> 3 funnel is represented as intersecting screening
-- obligations.  A candidate is not admitted merely because it scores well on
-- one downstream descriptor.
------------------------------------------------------------------------

record ScreeningPredicates (Candidate : Set) : Set₁ where
  field
    Relaxed : Candidate → Set
    FormationStable : Candidate → Set
    ActiveSiteIdentified : Candidate → Set
    CHEProfiled : Candidate → Set
    ScreeningReference : String

open ScreeningPredicates public

record ScreeningAdmissible
    {Candidate : Set}
    (screen : ScreeningPredicates Candidate)
    (candidate : Candidate) : Set where
  constructor screening-admissible
  field
    relaxed : Relaxed screen candidate
    formationStable : FormationStable screen candidate
    activeSiteIdentified : ActiveSiteIdentified screen candidate
    cheProfiled : CHEProfiled screen candidate

open ScreeningAdmissible public

admissibleImpliesRelaxed :
  ∀ {Candidate} {screen : ScreeningPredicates Candidate} {candidate} →
  ScreeningAdmissible screen candidate →
  Relaxed screen candidate
admissibleImpliesRelaxed = relaxed

admissibleImpliesFormationStable :
  ∀ {Candidate} {screen : ScreeningPredicates Candidate} {candidate} →
  ScreeningAdmissible screen candidate →
  FormationStable screen candidate
admissibleImpliesFormationStable = formationStable

admissibleImpliesActiveSiteIdentified :
  ∀ {Candidate} {screen : ScreeningPredicates Candidate} {candidate} →
  ScreeningAdmissible screen candidate →
  ActiveSiteIdentified screen candidate
admissibleImpliesActiveSiteIdentified = activeSiteIdentified

admissibleImpliesCHEProfiled :
  ∀ {Candidate} {screen : ScreeningPredicates Candidate} {candidate} →
  ScreeningAdmissible screen candidate →
  CHEProfiled screen candidate
admissibleImpliesCHEProfiled = cheProfiled

------------------------------------------------------------------------
-- Winner status is a downstream refinement, not a synonym for admissibility.
------------------------------------------------------------------------

record WinnerPredicate
    {Candidate : Set}
    (screen : ScreeningPredicates Candidate) : Set₁ where
  field
    Winner : Candidate → Set
    winnerRequiresAdmissibility :
      ∀ candidate → Winner candidate → ScreeningAdmissible screen candidate
    winnerReference : String

open WinnerPredicate public

record ScreeningFunnelBoundary : Set where
  constructor screening-funnel-boundary
  field
    oneGoodDescriptorImpliesScreeningAdmission : Bool
    oneGoodDescriptorImpliesScreeningAdmissionIsFalse :
      oneGoodDescriptorImpliesScreeningAdmission ≡ false

    screeningAdmissionEqualsWinnerStatus : Bool
    screeningAdmissionEqualsWinnerStatusIsFalse :
      screeningAdmissionEqualsWinnerStatus ≡ false

    winnerMustCarryUpstreamScreeningReceipts : Bool
    winnerMustCarryUpstreamScreeningReceiptsIsTrue :
      winnerMustCarryUpstreamScreeningReceipts ≡ true

canonicalScreeningFunnelBoundary : ScreeningFunnelBoundary
canonicalScreeningFunnelBoundary =
  screening-funnel-boundary false refl false refl true refl

------------------------------------------------------------------------
-- Source calibration only: counts and method stages reported by Bharadwaj H
-- and Ranganathan (npj Computational Materials, 2026).
------------------------------------------------------------------------

record ReportedFunnelReceipt : Set where
  constructor reported-funnel-receipt
  field
    initialQuinaryCount : String
    viableAfterScreeningCount : String
    highlightedWinnerCount : String
    dftRelaxationUsed : Bool
    dftRelaxationUsedIsTrue : dftRelaxationUsed ≡ true
    formationEnergyFilterUsed : Bool
    formationEnergyFilterUsedIsTrue : formationEnergyFilterUsed ≡ true
    pdosActiveSiteIdentificationUsed : Bool
    pdosActiveSiteIdentificationUsedIsTrue :
      pdosActiveSiteIdentificationUsed ≡ true
    cheProfilingUsed : Bool
    cheProfilingUsedIsTrue : cheProfilingUsed ≡ true

canonicalReportedFunnelReceipt : ReportedFunnelReceipt
canonicalReportedFunnelReceipt =
  reported-funnel-receipt
    "56" "18" "3"
    true refl true refl true refl true refl
