module DASHI.Physics.Foundations.CabarlahToponymTranscriptionExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- These are spelling-based hypotheses only.  They are not asserted to be
-- recovered Jarowair or Wakka lexical forms.

data SourceSoundCandidate : Set where
  kabalaCandidate : SourceSoundCandidate
  kabarlaCandidate : SourceSoundCandidate
  gabalaCandidate : SourceSoundCandidate
  gabarlaCandidate : SourceSoundCandidate

data ConventionalSpelling : Set where
  cabarlah : ConventionalSpelling

colonialRender : SourceSoundCandidate → ConventionalSpelling
colonialRender kabalaCandidate = cabarlah
colonialRender kabarlaCandidate = cabarlah
colonialRender gabalaCandidate = cabarlah
colonialRender gabarlaCandidate = cabarlah

allCandidates : List SourceSoundCandidate
allCandidates =
  kabalaCandidate
  ∷ kabarlaCandidate
  ∷ gabalaCandidate
  ∷ gabarlaCandidate
  ∷ []

candidateCount : List SourceSoundCandidate → Nat
candidateCount [] = 0
candidateCount (_ ∷ xs) = suc (candidateCount xs)

candidateCountIsFour : candidateCount allCandidates ≡ 4
candidateCountIsFour = refl

firstAndThirdRenderEqually :
  colonialRender kabalaCandidate ≡ colonialRender gabalaCandidate
firstAndThirdRenderEqually = refl

kabalaAndGabalaCandidatesDistinct :
  kabalaCandidate ≡ gabalaCandidate → ⊥
kabalaAndGabalaCandidatesDistinct ()

InjectiveColonialRender : Set
InjectiveColonialRender =
  (x y : SourceSoundCandidate) →
  colonialRender x ≡ colonialRender y →
  x ≡ y

colonialRenderIsNotInjective : ¬ InjectiveColonialRender
colonialRenderIsNotInjective injective =
  kabalaAndGabalaCandidatesDistinct
    (injective kabalaCandidate gabalaCandidate refl)

------------------------------------------------------------------------
-- Three levels prevent a conventional English name from being identified with
-- either Country itself or a uniquely recoverable spoken source form.

data PlaceRepresentation : Set where
  countryRelation : PlaceRepresentation
  unknownSpokenSource : PlaceRepresentation
  conventionalEnglishName : PlaceRepresentation
  militaryInstitutionalAddress : PlaceRepresentation

nextRepresentation : PlaceRepresentation → PlaceRepresentation
nextRepresentation countryRelation = unknownSpokenSource
nextRepresentation unknownSpokenSource = conventionalEnglishName
nextRepresentation conventionalEnglishName = militaryInstitutionalAddress
nextRepresentation militaryInstitutionalAddress = militaryInstitutionalAddress

countryToInstitutionalAddress :
  nextRepresentation
    (nextRepresentation
      (nextRepresentation countryRelation))
  ≡ militaryInstitutionalAddress
countryToInstitutionalAddress = refl

countryIsNotConventionalName :
  countryRelation ≡ conventionalEnglishName → ⊥
countryIsNotConventionalName ()

spokenSourceIsNotConventionalName :
  unknownSpokenSource ≡ conventionalEnglishName → ⊥
spokenSourceIsNotConventionalName ()

------------------------------------------------------------------------
-- The conventional spelling is legitimate as an English administrative form,
-- but it is not a lossless inverse for the source pronunciation.

record ToponymTranscriptionBoundary : Set where
  constructor toponymTranscriptionBoundary
  field
    conventionalSpelling : ConventionalSpelling

    exactSourceSoundRecovered : Bool
    exactSourceSoundRecoveredIsFalse : exactSourceSoundRecovered ≡ false

    candidateSetIsCertifiedWakkaLexicon : Bool
    candidateSetIsCertifiedWakkaLexiconIsFalse :
      candidateSetIsCertifiedWakkaLexicon ≡ false

    finalHIsCertifiedSourcePhoneme : Bool
    finalHIsCertifiedSourcePhonemeIsFalse :
      finalHIsCertifiedSourcePhoneme ≡ false

    singleRProvesTrill : Bool
    singleRProvesTrillIsFalse : singleRProvesTrill ≡ false

open ToponymTranscriptionBoundary public

canonicalToponymTranscriptionBoundary : ToponymTranscriptionBoundary
canonicalToponymTranscriptionBoundary =
  toponymTranscriptionBoundary
    cabarlah
    false refl
    false refl
    false refl
    false refl
