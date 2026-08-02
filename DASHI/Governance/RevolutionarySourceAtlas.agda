module DASHI.Governance.RevolutionarySourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Attributed source atlas for the revolutionary-practice adjunct.
--
-- The atlas records author, title, publication context and DOI state.  A
-- missing DOI means only that no DOI is recorded by this module; it is not a
-- global bibliographic non-existence theorem.  Source identity does not create
-- philosophical, cultural, historical, legal or political authority.
------------------------------------------------------------------------

record SourceReference : Set where
  constructor sourceReference
  field
    sourceAuthor : String
    sourceTitle : String
    publicationContext : String
    publicationYear : String
    doiValue : String
    doiRecordedByAtlas : Bool
    sourceCreatesInterpretiveAuthority : Bool
    sourceCreatesInterpretiveAuthorityIsFalse :
      sourceCreatesInterpretiveAuthority ≡ false

open SourceReference public

mkNoDOISource :
  String → String → String → String → SourceReference
mkNoDOISource author title context year =
  sourceReference
    author
    title
    context
    year
    "no DOI recorded by this atlas"
    false
    false
    refl

mkDOISource :
  String → String → String → String → String → SourceReference
mkDOISource author title context year doi =
  sourceReference
    author
    title
    context
    year
    doi
    true
    false
    refl

robinWallKimmererBraidingSweetgrass : SourceReference
robinWallKimmererBraidingSweetgrass =
  mkNoDOISource
    "Robin Wall Kimmerer"
    "Braiding Sweetgrass: Indigenous Wisdom, Scientific Knowledge and the Teachings of Plants"
    "book; Milkweed Editions"
    "2013"

andieNordgrenRelationshipAnarchy : SourceReference
andieNordgrenRelationshipAnarchy =
  mkNoDOISource
    "Andie Nordgren"
    "The Short Instructional Manifesto for Relationship Anarchy"
    "manifesto / relational-practice source"
    "2006; later English circulation"

peterKropotkinMutualAid : SourceReference
peterKropotkinMutualAid =
  mkNoDOISource
    "Peter Kropotkin"
    "Mutual Aid: A Factor of Evolution"
    "book"
    "1902"

frantzFanonWretchedEarth : SourceReference
frantzFanonWretchedEarth =
  mkNoDOISource
    "Frantz Fanon"
    "The Wretched of the Earth"
    "book"
    "1961"

judithButlerFramesOfWar : SourceReference
judithButlerFramesOfWar =
  mkNoDOISource
    "Judith Butler"
    "Frames of War: When Is Life Grievable?"
    "book"
    "2009"

dominickLaCapraWritingHistoryWritingTrauma : SourceReference
dominickLaCapraWritingHistoryWritingTrauma =
  mkNoDOISource
    "Dominick LaCapra"
    "Writing History, Writing Trauma"
    "book"
    "2001"

kimberleCrenshawMappingMargins : SourceReference
kimberleCrenshawMappingMargins =
  mkDOISource
    "Kimberle Williams Crenshaw"
    "Mapping the Margins: Intersectionality, Identity Politics, and Violence against Women of Color"
    "Stanford Law Review 43(6)"
    "1991"
    "10.2307/1229039"

nineElevenCommissionReport : SourceReference
nineElevenCommissionReport =
  mkNoDOISource
    "National Commission on Terrorist Attacks Upon the United States"
    "The 9/11 Commission Report"
    "official commission report"
    "2004"

edwardSaidQuestionOfPalestine : SourceReference
edwardSaidQuestionOfPalestine =
  mkNoDOISource
    "Edward W. Said"
    "The Question of Palestine"
    "book"
    "1979"

rashidKhalidiHundredYearsWar : SourceReference
rashidKhalidiHundredYearsWar =
  mkNoDOISource
    "Rashid Khalidi"
    "The Hundred Years' War on Palestine"
    "book"
    "2020"

ervandAbrahamianTheCoup : SourceReference
ervandAbrahamianTheCoup =
  mkNoDOISource
    "Ervand Abrahamian"
    "The Coup: 1953, the CIA, and the Roots of Modern U.S.-Iranian Relations"
    "book"
    "2013"

toddGitlinTheSixties : SourceReference
toddGitlinTheSixties =
  mkNoDOISource
    "Todd Gitlin"
    "The Sixties: Years of Hope, Days of Rage"
    "book / counterculture history"
    "1987"

canonicalRevolutionarySourceReferences : List SourceReference
canonicalRevolutionarySourceReferences =
  robinWallKimmererBraidingSweetgrass
  ∷ andieNordgrenRelationshipAnarchy
  ∷ peterKropotkinMutualAid
  ∷ frantzFanonWretchedEarth
  ∷ judithButlerFramesOfWar
  ∷ dominickLaCapraWritingHistoryWritingTrauma
  ∷ kimberleCrenshawMappingMargins
  ∷ nineElevenCommissionReport
  ∷ edwardSaidQuestionOfPalestine
  ∷ rashidKhalidiHundredYearsWar
  ∷ ervandAbrahamianTheCoup
  ∷ toddGitlinTheSixties
  ∷ []

record RevolutionarySourceAtlasBoundary : Set where
  constructor revolutionarySourceAtlasBoundary
  field
    sourceProvenanceRetained : Bool
    sourceProvenanceRetainedIsTrue : sourceProvenanceRetained ≡ true
    absentDOIClaimIsAtlasLocal : Bool
    absentDOIClaimIsAtlasLocalIsTrue : absentDOIClaimIsAtlasLocal ≡ true
    sourceAgreementClaimed : Bool
    sourceAgreementClaimedIsFalse : sourceAgreementClaimed ≡ false
    sourceEndorsementClaimed : Bool
    sourceEndorsementClaimedIsFalse : sourceEndorsementClaimed ≡ false
    philosophicalAuthorityPromoted : Bool
    philosophicalAuthorityPromotedIsFalse : philosophicalAuthorityPromoted ≡ false
    politicalAuthorityPromoted : Bool
    politicalAuthorityPromotedIsFalse : politicalAuthorityPromoted ≡ false

open RevolutionarySourceAtlasBoundary public

canonicalRevolutionarySourceAtlasBoundary :
  RevolutionarySourceAtlasBoundary
canonicalRevolutionarySourceAtlasBoundary =
  revolutionarySourceAtlasBoundary
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

canonicalRevolutionarySourceAtlasReceipt :
  GenericReceipt.GenericReceipt
canonicalRevolutionarySourceAtlasReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "attributed revolutionary philosophy source atlas"
    "DASHI.Governance.RevolutionarySourceAtlas"
    "canonicalRevolutionarySourceReferences"
    "records author/title/publication/DOI state for Sweetgrass, relationship anarchy, mutual aid, decolonial, trauma-memory, Palestine, Iran-US and counterculture reference lanes"
    "the atlas does not claim source agreement, endorsement, exhaustive bibliography, historical closure, legal authority or political authority"
    "agda -i . DASHI/Governance/RevolutionarySourceAtlas.agda"
