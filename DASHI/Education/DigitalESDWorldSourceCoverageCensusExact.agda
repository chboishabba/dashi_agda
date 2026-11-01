module DASHI.Education.DigitalESDWorldSourceCoverageCensusExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.EducationCorpusSourceRegistry as Alice
import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDEfSSourceCrossPollinationExact as EfS

-- Source identity census, NOT a completed full-text or empirical census.
-- Derive every row from canonical owner registries. There is no parallel
-- manually maintained list of titles, DOIs, or source URLs.
data SourcePopulation : Set where
  aliceCorpus : SourcePopulation
  independentEfSCandidate : SourcePopulation

data EvidenceCoverage : Set where
  reviewNotAsserted : EvidenceCoverage

record WorldSourceCoverageRow : Set where
  constructor world-source-coverage-row
  field
    sourceIdentity : String
    population : SourcePopulation
    reviewStatus : EvidenceCoverage
    claimEvidenceDebt : String

open WorldSourceCoverageRow public

map : {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

aliceRow : Alice.PaperReference → WorldSourceCoverageRow
aliceRow p = world-source-coverage-row
  (Alice.paperKey p)
  aliceCorpus
  reviewNotAsserted
  (Alice.paperSourceBoundary p)

efsRow : EfS.CrossPollinationCase → WorldSourceCoverageRow
efsRow c = world-source-coverage-row
  (Attr.canonicalURL (EfS.attributedSource c))
  independentEfSCandidate
  reviewNotAsserted
  (EfS.candidateEvidenceDebt c)

aliceCoverageRows : List WorldSourceCoverageRow
aliceCoverageRows = map aliceRow Alice.canonicalEducationCorpusPapers

efsCoverageRows : List WorldSourceCoverageRow
efsCoverageRows = map efsRow EfS.canonicalSourceCases

worldSourceCoverageRows : List WorldSourceCoverageRow
worldSourceCoverageRows = aliceCoverageRows ++ efsCoverageRows

-- These counts verify *registry coverage*, not review or source admission.
aliceRegistryCount : length aliceCoverageRows ≡ 9
aliceRegistryCount = refl

efsCandidateRegistryCount : length efsCoverageRows ≡ 16
efsCandidateRegistryCount = refl

combinedRegistryCount : length worldSourceCoverageRows ≡ 25
combinedRegistryCount = refl

-- No local constructor can promote this inventory into a source-audit
-- admission. Real admission stays in the canonical source-specific owner.
data RegistryRowImpliesReviewedEvidence : Set where

registryRowDoesNotProveReview :
  RegistryRowImpliesReviewedEvidence → {A : Set} → A
registryRowDoesNotProveReview () 
