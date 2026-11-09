module DASHI.Governance.Crenshaw1989PassageWeldExact where

-- Source-anchored reading of Crenshaw (1989), not proof of judicial facts.
-- The PDF reproduced from a University of Chicago repository copy is at
-- https://ideas.wharton.upenn.edu/wp-content/uploads/2018/07/Crenshaw-1989.pdf
-- Page identifiers below refer to PRINTED journal pages, not PDF indices.
-- DASHI owns these finite indexing witnesses and their proofs, while
-- Crenshaw owns her textual scholarship and the courts own the opinions.
-- Source spans are visually checked, NOT crypto-hash authenticated.

open import DASHI.Core.Prelude

data CrenshawCase : Set where
  deGraffenreid moore payne jefferies : CrenshawCase

data SourceRole : Set where
  featuredDoctrinalExample citedContraryExample : SourceRole

crenshaw1989Role : CrenshawCase → SourceRole
crenshaw1989Role deGraffenreid = featuredDoctrinalExample
crenshaw1989Role moore = featuredDoctrinalExample
crenshaw1989Role payne = featuredDoctrinalExample
crenshaw1989Role jefferies = citedContraryExample

data PassageKind : Set where
  framedCaseAnalysis supportingFootnote : PassageKind

data PrintedPage : Set where
  p141 p143 p144 p145 p146 p147 p148 : PrintedPage

record LocatedCrenshawPassage : Set where
  constructor located
  field
    caseKey : CrenshawCase
    role : SourceRole
    page : PrintedPage
    kind : PassageKind
    topic : String

open LocatedCrenshawPassage public

deGraffenreidSelection : LocatedCrenshawPassage
deGraffenreidSelection =
  located deGraffenreid featuredDoctrinalExample p141 framedCaseAnalysis
    "Section I.A identifies three case studies; DeGraffenreid numbered 1"

mooreAnalysis : LocatedCrenshawPassage
mooreAnalysis =
  located moore featuredDoctrinalExample p143 framedCaseAnalysis
    "Moore numbered 2; class representation, proof pools"

payneAnalysis : LocatedCrenshawPassage
payneAnalysis =
  located payne featuredDoctrinalExample p147 framedCaseAnalysis
    "Payne numbered 3; class scope and remedial consequence"

jefferiesFootnote : LocatedCrenshawPassage
jefferiesFootnote =
  located jefferies citedContraryExample p143 supportingFootnote
    "Footnote 13: Jefferies cited as court recognizing Black women under Title VII"

-- Exact source-role indexing for the four selected cases.
jefferiesIsCitedByCrenshaw :
  crenshaw1989Role jefferies ≡ citedContraryExample
jefferiesIsCitedByCrenshaw = refl

jefferiesIsNotOneOfThreeFeaturedCases :
  crenshaw1989Role jefferies ≡ featuredDoctrinalExample → ⊥
jefferiesIsNotOneOfThreeFeaturedCases ()

threeOriginalCaseExamples :
  (crenshaw1989Role deGraffenreid ≡ featuredDoctrinalExample)
  × (crenshaw1989Role moore ≡ featuredDoctrinalExample)
  × (crenshaw1989Role payne ≡ featuredDoctrinalExample)
threeOriginalCaseExamples = refl , (refl , refl)

data AuthorshipLayer : Set where
  crenshawScholarship courtJudgment dashiFormalAdapter : AuthorshipLayer

caseAnalysisNotJudicialAuthorship :
  crenshawScholarship ≡ courtJudgment → ⊥
caseAnalysisNotJudicialAuthorship ()

formalAdapterNotCrenshawAuthorship :
  dashiFormalAdapter ≡ crenshawScholarship → ⊥
formalAdapterNotCrenshawAuthorship ()

-- A source citation alone must not be converted into a claim about
-- whether a participant experienced clinically or phenomenologically
-- significant fatigue or whether a court deliberately caused that effect.
data EmpiricalFatigueReceipt : Set where
data IntentionalExhaustionReceipt : Set where

sourceCitationAloneCannotProveFatigue :
  EmpiricalFatigueReceipt → ⊥
sourceCitationAloneCannotProveFatigue ()

sourceCitationAloneCannotProveIntent :
  IntentionalExhaustionReceipt → ⊥
sourceCitationAloneCannotProveIntent ()
