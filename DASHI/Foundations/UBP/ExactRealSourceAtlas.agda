module DASHI.Foundations.UBP.ExactRealSourceAtlas where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

data DOIStatus : Set where
  doiRecorded : String → DOIStatus
  noDOIForRepository : DOIStatus

record ExactRealSource : Set where
  constructor exactRealSource
  field
    author : String
    title : String
    publication : String
    year : Nat
    doiStatus : DOIStatus
    canonicalURL : String
    formalRelationship : String

open ExactRealSource public

murrayBishopReals : ExactRealSource
murrayBishopReals =
  exactRealSource
    "Zachary Murray"
    "Constructive Analysis in the Agda Proof Assistant"
    "Master's thesis and arXiv:2205.08354"
    2022
    (doiRecorded "10.48550/arXiv.2205.08354")
    "https://arxiv.org/abs/2205.08354"
    "source for the Bishop-real implementation, regular-sequence arithmetic, ordering, Cauchy completeness and the existing vendor/bishop theorem lineage"

broughHoTTReals : ExactRealSource
broughHoTTReals =
  exactRealSource
    "Jackson Brough"
    "Formalizing the Real Numbers in Homotopy Type Theory with Cubical Agda"
    "arXiv:2604.24782"
    2026
    (doiRecorded "10.48550/arXiv.2604.24782")
    "https://arxiv.org/abs/2604.24782"
    "candidate prototype backend for higher-inductive-inductive HoTT reals in Cubical Agda; interoperability with non-cubical DASHI remains an explicit obligation"

csimmaBishopRepository : ExactRealSource
csimmaBishopRepository =
  exactRealSource
    "Viktor Csimma and contributors"
    "bishop: Constructive Analysis in Agda"
    "GitHub repository"
    2026
    noDOIForRepository
    "https://github.com/viktorcsimma/bishop"
    "pinned external implementation being migrated to Agda 2.9; suitability for heavily composed arithmetic remains a measured backend question"

exactRealSources : List ExactRealSource
exactRealSources =
  murrayBishopReals
  ∷ broughHoTTReals
  ∷ csimmaBishopRepository
  ∷ []

sourceCount : ∀ {A : Set} → List A → Nat
sourceCount [] = zero
sourceCount (_ ∷ xs) = suc (sourceCount xs)

exactRealSourceCountIsThree :
  sourceCount exactRealSources ≡ 3
exactRealSourceCountIsThree = refl

exactRealSourceAtlasReceipt : GenericReceipt.GenericReceipt
exactRealSourceAtlasReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "exact-real backend source atlas"
    "DASHI.Foundations.UBP.ExactRealSourceAtlas"
    "exactRealSources"
    "the Bishop-real thesis and implementation plus the 2026 Cubical HoTT-real prototype are attached with exact authors, titles, URLs and arXiv DOIs where applicable"
    "backend suitability, computational performance and interoperability are engineering and proof obligations; citations are not proof imports"
    "agda -i . DASHI/Foundations/UBP/ExactRealSourceAtlas.agda"

exactRealSourceAtlasReceiptNonPromoting :
  GenericReceipt.promotesClaim exactRealSourceAtlasReceipt ≡ false
exactRealSourceAtlasReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse exactRealSourceAtlasReceipt
