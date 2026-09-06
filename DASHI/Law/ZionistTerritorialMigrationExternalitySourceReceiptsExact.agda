module DASHI.Law.ZionistTerritorialMigrationExternalitySourceReceiptsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Historical territorial/migration projects and externality boundaries.
-- Proposed schemes, implemented settlements, migration, and colonial effects
-- are kept as different proposition types.
------------------------------------------------------------------------

data TerritorialSourceRole : Set where
  foundingText
  scholarlyHistory
  territorialistHistory
  archivalInstitution
  secondaryHistory
  dashiComparison : TerritorialSourceRole

data TerritorialProject : Set where
  palestineProject
  argentinaConsideration
  eastAfricaUgandaScheme
  mesopotamiaScheme
  angolaTerritorialistScheme
  cyrenaicaTerritorialistScheme
  hondurasTerritorialistScheme
  australiaTerritorialistConsideration
  otherTerritorialProposal : TerritorialProject

data TerritorialStatus : Set where
  considered
  formallyProposed
  commissionInvestigated
  attemptedSettlement
  implementedSettlement
  notImplemented
  statusUnresolved : TerritorialStatus

record TerritorialReceipt : Set where
  constructor territorialReceipt
  field
    project : TerritorialProject
    status : TerritorialStatus
    sourceRole : TerritorialSourceRole
    sourceReference : String
    boundedDescription : String

open TerritorialReceipt public

herzlArgentinaReceipt : TerritorialReceipt
herzlArgentinaReceipt = territorialReceipt
  argentinaConsideration considered foundingText
  "Theodor Herzl, Der Judenstaat / later historical discussion"
  "Herzl discussed Argentina alongside Palestine as a possible territorial solution; this is a consideration receipt, not evidence of implemented colonisation in Argentina by the Zionist Organization."

ugandaReceipt : TerritorialReceipt
ugandaReceipt = territorialReceipt
  eastAfricaUgandaScheme commissionInvestigated scholarlyHistory
  "British East Africa/Uganda proposal, Sixth Zionist Congress 1903; commission sent to inspect territory"
  "The Zionist Congress authorised investigation of a proposed autonomous Jewish settlement in British East Africa; the proposal was rejected and not implemented."

mesopotamiaReceipt : TerritorialReceipt
mesopotamiaReceipt = territorialReceipt
  mesopotamiaScheme notImplemented scholarlyHistory
  "Gur Alroey, Mesopotamia-'The Promised Land', Middle Eastern Studies 50(6), 2014, DOI 10.1080/00263206.2014.933418"
  "The Zionist Organization and later Jewish Territorial Organization considered settlement schemes in Mesopotamia; the plans did not reach practical implementation."

angolaReceipt : TerritorialReceipt
angolaReceipt = territorialReceipt
  angolaTerritorialistScheme notImplemented territorialistHistory
  "Gur Alroey, Angolan Zion, Journal of Modern Jewish Studies 14(2), 2015, DOI 10.1080/14725886.2015.1006009"
  "The Jewish Territorial Organization investigated an autonomous Jewish entity in Portuguese Angola; the plan failed. The JTO was a post-1905 secession from the Zionist movement and must not be silently equated with all Zionism."

multiTerritoryReceipt : TerritorialReceipt
multiTerritoryReceipt = territorialReceipt
  otherTerritorialProposal considered scholarlyHistory
  "Oxford Bibliographies, Jewish Territorialism; historical studies of the JTO"
  "Territorialists considered Mesopotamia, Cyrenaica, Angola, Honduras and other sites after leaving the Zionist movement. This is evidence of a broader territorial-colonisation repertoire, not evidence that each project was implemented."

------------------------------------------------------------------------
-- Externality fibre.
------------------------------------------------------------------------

data ExternalityCoordinate : Set where
  indigenousLandClaim
  demographicDisplacement
  imperialSponsor
  settlementInfrastructure
  migrationPressure
  sovereigntyConflict
  ecologicalMaterialChange
  localPoliticalResistance : ExternalityCoordinate

record TerritorialExternalityBoundary : Set where
  constructor territorialExternalityBoundary
  field
    proposalEqualsImplementation : Bool
    proposalEqualsImplementationIsFalse : proposalEqualsImplementation ≡ false
    migrationEqualsColonisation : Bool
    migrationEqualsColonisationIsFalse : migrationEqualsColonisation ≡ false
    territorialistSchemeEqualsAllZionism : Bool
    territorialistSchemeEqualsAllZionismIsFalse : territorialistSchemeEqualsAllZionism ≡ false
    oneHistoricalSchemeProvesGlobalBehaviouralTrait : Bool
    oneHistoricalSchemeProvesGlobalBehaviouralTraitIsFalse : oneHistoricalSchemeProvesGlobalBehaviouralTrait ≡ false

canonicalTerritorialExternalityBoundary : TerritorialExternalityBoundary
canonicalTerritorialExternalityBoundary =
  territorialExternalityBoundary false refl false refl false refl false refl

------------------------------------------------------------------------
-- BIDI claims.
------------------------------------------------------------------------

data TerritorialClaim : Set where
  zionistMovementConsideredMultipleTerritories
  territorialistMovementConsideredMultipleContinents
  schemeWasImplemented
  migrationProducedColonialExternality
  diasporaZionistsShareColonisingBehaviour : TerritorialClaim

data TerritorialProducer : Set where
  historicalProposalCorpusProducer
  territorialistCorpusProducer
  implementationReceiptProducer
  siteSpecificExternalityProducer
  populationBehaviourProducer : TerritorialProducer

reverseTerritorial : TerritorialClaim → TerritorialProducer
reverseTerritorial zionistMovementConsideredMultipleTerritories = historicalProposalCorpusProducer
reverseTerritorial territorialistMovementConsideredMultipleContinents = territorialistCorpusProducer
reverseTerritorial schemeWasImplemented = implementationReceiptProducer
reverseTerritorial migrationProducedColonialExternality = siteSpecificExternalityProducer
reverseTerritorial diasporaZionistsShareColonisingBehaviour = populationBehaviourProducer
