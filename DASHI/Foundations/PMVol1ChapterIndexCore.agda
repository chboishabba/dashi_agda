module DASHI.Foundations.PMVol1ChapterIndexCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PM Volume I chapter spine.
--
-- This is a deterministic comparison index.  Rows are candidate inventory
-- rows, not claims that PM propositions have been completed in Agda.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys =
  ys
(x ∷ xs) ++ ys =
  x ∷ (xs ++ ys)

data PMVol1PackageBand : Set where
  packageStar1To5 :
    PMVol1PackageBand

  packageStar6To14 :
    PMVol1PackageBand

  packageStar20To35 :
    PMVol1PackageBand

  packageStar36To43 :
    PMVol1PackageBand

  packageStar50To56 :
    PMVol1PackageBand

  packageStar60To67 :
    PMVol1PackageBand

  packageStar70To80 :
    PMVol1PackageBand

  packageStar90To97 :
    PMVol1PackageBand

  appendixPackage :
    PMVol1PackageBand

data PMVol1CoverageStatus : Set where
  checkedDashiSocket :
    PMVol1CoverageStatus

  candidateInventoryOnly :
    PMVol1CoverageStatus

  externalSubstrateOnly :
    PMVol1CoverageStatus

  pmPropositionCompletionMissing :
    PMVol1CoverageStatus

bandForPackageOrdinal : Nat → PMVol1PackageBand
bandForPackageOrdinal zero =
  packageStar1To5
bandForPackageOrdinal (suc zero) =
  packageStar1To5
bandForPackageOrdinal (suc (suc zero)) =
  packageStar1To5
bandForPackageOrdinal (suc (suc (suc zero))) =
  packageStar1To5
bandForPackageOrdinal (suc (suc (suc (suc zero)))) =
  packageStar1To5
bandForPackageOrdinal (suc (suc (suc (suc (suc zero))))) =
  packageStar6To14
bandForPackageOrdinal (suc (suc (suc (suc (suc (suc zero)))))) =
  packageStar6To14
bandForPackageOrdinal (suc (suc (suc (suc (suc (suc (suc zero))))))) =
  packageStar6To14
bandForPackageOrdinal (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) =
  packageStar6To14
bandForPackageOrdinal _ =
  candidateBand
  where
    candidateBand : PMVol1PackageBand
    candidateBand =
      packageStar20To35

coverageForBand : PMVol1PackageBand → PMVol1CoverageStatus
coverageForBand packageStar1To5 =
  checkedDashiSocket
coverageForBand packageStar6To14 =
  candidateInventoryOnly
coverageForBand packageStar20To35 =
  checkedDashiSocket
coverageForBand packageStar36To43 =
  checkedDashiSocket
coverageForBand packageStar50To56 =
  candidateInventoryOnly
coverageForBand packageStar60To67 =
  candidateInventoryOnly
coverageForBand packageStar70To80 =
  candidateInventoryOnly
coverageForBand packageStar90To97 =
  candidateInventoryOnly
coverageForBand appendixPackage =
  externalSubstrateOnly

record PMVol1ChapterRow : Set where
  constructor mkPMVol1ChapterRow
  field
    chapterOrdinal :
      Nat

    packageOrdinal :
      Nat

    chapterMark :
      String

    leanPackageId :
      String

    dashiSocket :
      String

    packageBand :
      PMVol1PackageBand

    coverageStatus :
      PMVol1CoverageStatus

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    propositionCompletionAuthority :
      Bool

    propositionCompletionAuthorityIsFalse :
      propositionCompletionAuthority ≡ false

numberedChapter : Nat → PMVol1ChapterRow
numberedChapter n =
  mkPMVol1ChapterRow
    n
    n
    "PM-Vol-I-numbered-star-chapter"
    "jmd-pm-vol1-numbered-package"
    "DASHI.Foundations.PMVol1ChapterIndexCore"
    (bandForPackageOrdinal n)
    (coverageForBand (bandForPackageOrdinal n))
    true
    refl
    false
    refl

appendixChapter : Nat → String → PMVol1ChapterRow
appendixChapter n leanId =
  mkPMVol1ChapterRow
    n
    n
    "PM-Vol-I-appendix"
    leanId
    "DASHI.Foundations.PMVol1ChapterIndexCore"
    appendixPackage
    externalSubstrateOnly
    true
    refl
    false
    refl

chaptersUpFrom : Nat → Nat → List PMVol1ChapterRow
chaptersUpFrom zero start =
  []
chaptersUpFrom (suc count) start =
  numberedChapter start ∷ chaptersUpFrom count (suc start)

canonicalNumberedPMVol1ChapterRows : List PMVol1ChapterRow
canonicalNumberedPMVol1ChapterRows =
  chaptersUpFrom 97 1

canonicalAppendixPMVol1ChapterRows : List PMVol1ChapterRow
canonicalAppendixPMVol1ChapterRows =
  appendixChapter 8 "jmd-pm-vol1-appendix-star8"
  ∷ appendixChapter 89 "jmd-pm-vol1-appendix-star89"
  ∷ appendixChapter 99 "jmd-pm-vol1-appendix-star99"
  ∷ []

canonicalPMVol1ChapterRows : List PMVol1ChapterRow
canonicalPMVol1ChapterRows =
  canonicalNumberedPMVol1ChapterRows ++ canonicalAppendixPMVol1ChapterRows

canonicalPMVol1ChapterRowCount : Nat
canonicalPMVol1ChapterRowCount =
  listCount canonicalPMVol1ChapterRows

canonicalPMVol1ChapterRowCountIs100 :
  canonicalPMVol1ChapterRowCount ≡ 100
canonicalPMVol1ChapterRowCountIs100 =
  refl

pmVol1ChapterRowsRemainCandidateOnly :
  PMVol1ChapterRow.candidateOnly (numberedChapter 1) ≡ true
pmVol1ChapterRowsRemainCandidateOnly =
  refl

pmVol1ChapterRowsDoNotCompletePropositions :
  PMVol1ChapterRow.propositionCompletionAuthority (numberedChapter 1) ≡ false
pmVol1ChapterRowsDoNotCompletePropositions =
  refl
