module DASHI.Physics.Foundations.CabarlahClaimStatusExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Evidence is kept separate from the content of a claim.  In particular, a
-- memorable or structurally useful interpretation is not definitionally equal
-- to a documented historical fact.

data EvidenceStatus : Set where
  documented : EvidenceStatus
  conventional : EvidenceStatus
  derived : EvidenceStatus
  contested : EvidenceStatus
  underdetermined : EvidenceStatus
  refuted : EvidenceStatus

data CabarlahClaim : Set where
  cabarlahConventionalEnglishSpelling : CabarlahClaim
  capbarlahHistoricalSpelling : CabarlahClaim
  exactIndigenousSourcePronunciation : CabarlahClaim
  cabarlahNearBrisbaneLatitude : CabarlahClaim
  officialFixedBrisbaneSurrenderLine : CabarlahClaim
  communistConcessionBoundaryAtCabarlah : CabarlahClaim
  postwarCabarlahSignalsIntelligence : CabarlahClaim
  pineGapProtestJoinedLandReturnAndPalestine : CabarlahClaim

claimStatus : CabarlahClaim → EvidenceStatus
claimStatus cabarlahConventionalEnglishSpelling = conventional
claimStatus capbarlahHistoricalSpelling = refuted
claimStatus exactIndigenousSourcePronunciation = underdetermined
claimStatus cabarlahNearBrisbaneLatitude = derived
claimStatus officialFixedBrisbaneSurrenderLine = contested
claimStatus communistConcessionBoundaryAtCabarlah = refuted
claimStatus postwarCabarlahSignalsIntelligence = documented
claimStatus pineGapProtestJoinedLandReturnAndPalestine = documented

capbarlahTypoIsNotHistoricalSpelling :
  claimStatus capbarlahHistoricalSpelling ≡ refuted
capbarlahTypoIsNotHistoricalSpelling = refl

communistBoundaryClaimIsRefuted :
  claimStatus communistConcessionBoundaryAtCabarlah ≡ refuted
communistBoundaryClaimIsRefuted = refl

exactSourcePronunciationRemainsUnderdetermined :
  claimStatus exactIndigenousSourcePronunciation ≡ underdetermined
exactSourcePronunciationRemainsUnderdetermined = refl

brisbaneLineOfficialityRemainsContested :
  claimStatus officialFixedBrisbaneSurrenderLine ≡ contested
brisbaneLineOfficialityRemainsContested = refl

postwarSignalsRoleIsDocumented :
  claimStatus postwarCabarlahSignalsIntelligence ≡ documented
postwarSignalsRoleIsDocumented = refl

documentedIsNotRefuted : documented ≡ refuted → ⊥
documentedIsNotRefuted ()

contestedIsNotDocumented : contested ≡ documented → ⊥
contestedIsNotDocumented ()

underdeterminedIsNotConventional : underdetermined ≡ conventional → ⊥
underdeterminedIsNotConventional ()

record ClaimStatusBoundary : Set where
  constructor claimStatusBoundary
  field
    typoPromotedToEtymology : Bool
    typoPromotedToEtymologyIsFalse : typoPromotedToEtymology ≡ false

    communistBoundaryPromotedToHistory : Bool
    communistBoundaryPromotedToHistoryIsFalse :
      communistBoundaryPromotedToHistory ≡ false

    conventionalSpellingRecoversUniqueSourceSound : Bool
    conventionalSpellingRecoversUniqueSourceSoundIsFalse :
      conventionalSpellingRecoversUniqueSourceSound ≡ false

    contestedBrisbaneLinePromotedToFixedOfficialLine : Bool
    contestedBrisbaneLinePromotedToFixedOfficialLineIsFalse :
      contestedBrisbaneLinePromotedToFixedOfficialLine ≡ false

open ClaimStatusBoundary public

canonicalClaimStatusBoundary : ClaimStatusBoundary
canonicalClaimStatusBoundary =
  claimStatusBoundary
    false refl
    false refl
    false refl
    false refl
