module DASHI.Governance.MontefioreRothschildAustralianGoldSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- CLAIM-LOCAL HISTORICAL SOURCE ATLAS
--
-- External sources retain authority for their historical/art-historical claims.
-- DASHI owns only the typed atlas, bounded-claim interface and promotion
-- firewalls below.
------------------------------------------------------------------------

data AuthorityClass : Set where
  governmentArchive : AuthorityClass
  nationalBiography : AuthorityClass
  institutionalArchive : AuthorityClass
  museumCatalogue : AuthorityClass
  congressionalInvestigation : AuthorityClass
  artworkAuthority : AuthorityClass

data Directness : Set where
  primaryRecord : Directness
  archivalInterpretation : Directness
  secondarySynthesis : Directness
  artworkRepresentation : Directness

data SourceRole : Set where
  familyBiography : SourceRole
  colonialFinanceHistory : SourceRole
  goldRushCorrespondenceHistory : SourceRole
  nuclearTestOfficialHistory : SourceRole
  narrativeArtworkCatalogue : SourceRole
  bankingInvestigation : SourceRole

data SourceIdentity : Set where
  npgMontefioreRothschildGoldRush : SourceIdentity
  adbPeopleAustraliaMontefiore : SourceIdentity
  rothschildArchiveAustralianGold : SourceIdentity
  naaMaralingaNuclearTests : SourceIdentity
  whitneyLombardiBCCI : SourceIdentity
  senateBCCIAffair : SourceIdentity

record SourceReceipt : Set where
  constructor source-receipt
  field
    identity : SourceIdentity
    role : SourceRole
    authority : AuthorityClass
    directness : Directness
    reference : String
    url : String
    interval : String
    boundedClaim : String
    claimTruthPaid : Bool
    transactionSettlementPaid : Bool
    wrongdoingPaid : Bool
open SourceReceipt public

npgReceipt : SourceReceipt
npgReceipt = source-receipt
  npgMontefioreRothschildGoldRush
  goldRushCorrespondenceHistory
  museumCatalogue
  archivalInterpretation
  "National Portrait Gallery of Australia, Angus Trumble, The Rothschilds, the Montefiores, and the Victorian Gold Rush (2017)"
  "https://www.portrait.gov.au/aboutface/2017/10/rothschilds-montefiores-gold-rush"
  "1851 and gold-rush correspondence context"
  "Documents surviving Montefiore correspondence with N. M. Rothschild & Sons and close involvement in the Victorian gold trade; museum interpretation is not itself a transaction ledger."
  true false false

adbReceipt : SourceReceipt
adbReceipt = source-receipt
  adbPeopleAustraliaMontefiore
  familyBiography
  nationalBiography
  secondarySynthesis
  "Australian Dictionary of Biography / People Australia, Jacob Barrow Montefiore and Joseph Barrow Montefiore"
  "https://peopleaustralia.anu.edu.au/biography/montefiore-joseph-barrow-2472"
  "nineteenth century"
  "Supports family relationships, colonial office, Bank of Australasia/mercantile roles and the wider Montefiore-Cohen-Rothschild kin/business context while requiring each business edge to be sourced separately."
  true false false

rothschildArchiveReceipt : SourceReceipt
rothschildArchiveReceipt = source-receipt
  rothschildArchiveAustralianGold
  goldRushCorrespondenceHistory
  institutionalArchive
  archivalInterpretation
  "The Rothschild Archive, Australian gold purchasing/shipping collection material"
  "https://www.rothschildarchive.org/collections/archivists_choice/january_2020_wooden_box_of_precious_metal_samples_c1860"
  "Victorian gold-rush era"
  "Supports that N. M. Rothschild & Sons used Australian agents and correspondence in purchasing/shipping Australian gold; exact account-book and consignment identifiers remain an acquisition frontier."
  true false false

maralingaReceipt : SourceReceipt
maralingaReceipt = source-receipt
  naaMaralingaNuclearTests
  nuclearTestOfficialHistory
  governmentArchive
  archivalInterpretation
  "National Archives of Australia, British nuclear tests at Maralinga"
  "https://www.naa.gov.au/explore-collection/first-australians/other-resources-about-first-australians/british-nuclear-tests-maralinga"
  "1950s-1960s and later Royal Commission"
  "Supports British nuclear testing with Australian-government agreement/support, Maralinga as a proving ground, Aboriginal Country and permission/exposure/removal consequences, while not establishing any later Pine Gap programme lineage."
  true false false

whitneyReceipt : SourceReceipt
whitneyReceipt = source-receipt
  whitneyLombardiBCCI
  narrativeArtworkCatalogue
  museumCatalogue
  artworkRepresentation
  "Whitney Museum of American Art, Mark Lombardi, BCCI-ICIC & FAB, 1972-91 (4th Version)"
  "https://whitney.org/collection/works/12916"
  "1972-1991 represented; artwork later"
  "Supports Lombardi's public-record-derived narrative-structure practice and the existence/content class of the artwork, not independent truth of each represented edge."
  true false false

senateReceipt : SourceReceipt
senateReceipt = source-receipt
  senateBCCIAffair
  bankingInvestigation
  congressionalInvestigation
  archivalInterpretation
  "U.S. Senate Foreign Relations Committee, Kerry/Brown, The BCCI Affair (1992)"
  "https://irp.fas.org/congress/1992_rpt/bcci/"
  "BCCI investigation period"
  "Supports congressional investigative findings concerning BCCI, ICIC, nominee arrangements and concealed First American control where expressly stated by the report."
  true false false

------------------------------------------------------------------------
-- Promotion ceilings.
------------------------------------------------------------------------

data SourcePresenceCreatesTruth : Set where
data ArtworkCreatesHistoricalReceipt : Set where
data ArchivalInterpretationCreatesPrimaryTransaction : Set where
data TransferStatementCreatesSettlement : Set where
data BiographyKinshipCreatesBusinessAgency : Set where

sourcePresenceDoesNotCreateTruth : SourcePresenceCreatesTruth → ⊥
sourcePresenceDoesNotCreateTruth ()

artworkDoesNotCreateHistoricalReceipt : ArtworkCreatesHistoricalReceipt → ⊥
artworkDoesNotCreateHistoricalReceipt ()

archivalInterpretationDoesNotCreatePrimaryTransaction : ArchivalInterpretationCreatesPrimaryTransaction → ⊥
archivalInterpretationDoesNotCreatePrimaryTransaction ()

transferStatementDoesNotCreateSettlement : TransferStatementCreatesSettlement → ⊥
transferStatementDoesNotCreateSettlement ()

biographyKinshipDoesNotCreateBusinessAgency : BiographyKinshipCreatesBusinessAgency → ⊥
biographyKinshipDoesNotCreateBusinessAgency ()

record SourceAtlasBoundary : Set where
  constructor source-atlas-boundary
  field
    sourcePresenceEqualsTruth : Bool
    artworkEqualsHistoricalReceipt : Bool
    archivalInterpretationEqualsPrimaryTransaction : Bool
    transferStatementEqualsSettlement : Bool
    biographyKinshipEqualsBusinessAgency : Bool
    claimLocalAuthorityRetained : Bool
open SourceAtlasBoundary public

canonicalSourceAtlasBoundary : SourceAtlasBoundary
canonicalSourceAtlasBoundary = source-atlas-boundary false false false false false true
