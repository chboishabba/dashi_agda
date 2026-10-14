module DASHI.Cognition.ApolloRowanDisclosureScopeReconciliation20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinMarcRowanApolloWorkSurface20261014Exact as Rowan

------------------------------------------------------------------------
-- APOLLO / ROWAN PUBLIC-DISCLOSURE SCOPE RECONCILIATION — 2026-10-14
--
-- Apollo's 18-Feb-2026 client letter is preserved literally as a first-party
-- corporate statement. Primary released records are compared by proposition,
-- not collapsed into an accusation that the statement is legally false.
------------------------------------------------------------------------

data DisclosureProposition : Set where
  noBusinessRelationship : DisclosureProposition
  noPersonalRelationship : DisclosureProposition
  selectInformationForBlackTaxWork : DisclosureProposition
  attemptedOtherFounderWorkDeclined : DisclosureProposition

record CorporateStatement : Set where
  constructor corporate-statement
  field
    date : String
    source : String
    proposition : DisclosureProposition
    textSummary : String
open CorporateStatement public

apolloNoBusiness : CorporateStatement
apolloNoBusiness = corporate-statement
  "2026-02-18" "Apollo letter to clients and partners"
  noBusinessRelationship
  "Apollo stated that Marc Rowan and Apollo personnel other than Leon Black had no business or personal relationship with Epstein."

apolloSelectInfo : CorporateStatement
apolloSelectInfo = corporate-statement
  "2026-02-18" "Apollo letter to clients and partners"
  selectInformationForBlackTaxWork
  "Apollo separately stated that in select instances Rowan and other employees provided information to Epstein in connection with Epstein's tax work for Black."

apolloDeclinedOtherWork : CorporateStatement
apolloDeclinedOtherWork = corporate-statement
  "2026-02-18" "Apollo letter to clients and partners"
  attemptedOtherFounderWorkDeclined
  "Apollo stated that Epstein sought work with Apollo co-founders other than Black but that this was declined at every turn."

record PrimaryScopeCoordinate : Set where
  constructor primary-scope-coordinate
  field
    label : String
    source : String
    directRowanEpsteinContact : Bool
    apolloRelatedSubject : Bool
    blackTaxMandateCompatible : Bool
    clearlyOutsideBlackTaxMandatePaid : Bool
    reading : String
open PrimaryScopeCoordinate public

traCoordinate : PrimaryScopeCoordinate
traCoordinate = primary-scope-coordinate
  "Apollo TRA calculation material forwarded to Epstein"
  "EFTA00645429 and related TRA thread"
  true true true false
  "Rowan forwarded Apollo's TRA valuation methodology and detailed calculation material to Epstein. The object is Apollo-related; current evidence does not independently exclude the possibility that it was supplied for Black/founder tax work."

founder8865Coordinate : PrimaryScopeCoordinate
founder8865Coordinate = primary-scope-coordinate
  "Historical 8865 founder-family-office project"
  "EFTA02450093 / EFTA00816834"
  true true true false
  "Wechsler explicitly included Epstein for substantive expertise on historical 8865 data involving founder family offices. This is substantive involvement but may still fall within Black/founder tax work."

rothschildInversionCoordinate : PrimaryScopeCoordinate
rothschildInversionCoordinate = primary-scope-coordinate
  "Rowan/Epstein Rothschild inversion discussion"
  "EFTA00833332"
  true true false false
  "Direct Rowan/Epstein correspondence discusses balance-sheet calculations and a potential Rothschild-enabled inversion structure. Whether this was wholly a Black tax project, an Apollo/founder project, or another workstream is not closed by the email alone."

liquidFundingRegulationCoordinate : PrimaryScopeCoordinate
liquidFundingRegulationCoordinate = primary-scope-coordinate
  "Rowan re-introduction after Liquid Funding"
  "EFTA02454291 / EFTA02361689"
  true false false true
  "Rowan re-introduced Sidley partner Perry Shwachman and Epstein under a prior Liquid Funding context; Shwachman then proposed discussing potential USVI insurance regulations. This work surface is not facially a Black personal tax-information exchange."

record DisclosureScopeBoundary : Set where
  constructor disclosure-scope-boundary
  field
    repeatedDirectContactPaid : Bool
    substantiveFinancialWorkSurfacePaid : Bool
    atLeastOneNonBlackTaxFacialSubjectPaid : Bool
    corporateRetainerPaid : Bool
    formalRowanClientRetainerPaid : Bool
    statementLegallyFalsePaid : Bool
    semanticTensionWorthAcquiring : Bool
open DisclosureScopeBoundary public

canonicalDisclosureScopeBoundary : DisclosureScopeBoundary
canonicalDisclosureScopeBoundary = disclosure-scope-boundary
  true true true false false false true

data PrimaryContactImpliesBusinessRelationshipAsLegalFact : Set where
data DisclosureTensionImpliesFraud : Set where
data InformationSharingImpliesRetainer : Set where

primaryContactDoesNotSetLegalLabel : PrimaryContactImpliesBusinessRelationshipAsLegalFact → ⊥
primaryContactDoesNotSetLegalLabel ()

disclosureTensionDoesNotCreateFraud : DisclosureTensionImpliesFraud → ⊥
disclosureTensionDoesNotCreateFraud ()

informationSharingDoesNotCreateRetainer : InformationSharingImpliesRetainer → ⊥
informationSharingDoesNotCreateRetainer ()

data DisclosureDebt : Set where
  apolloInternalScopeDefinition : DisclosureDebt
  rowanPurposeByThread : DisclosureDebt
  blackMandateBoundary : DisclosureDebt
  compensationAndBilling : DisclosureDebt
  boardDisclosureProcess : DisclosureDebt

record DisclosureAcquisition : Set where
  constructor disclosure-acquisition
  field
    debt : DisclosureDebt
    priority : Nat
    question : String
open DisclosureAcquisition public

canonicalDisclosureAcquisition : List DisclosureAcquisition
canonicalDisclosureAcquisition =
  disclosure-acquisition rowanPurposeByThread 100
    "Classify every Rowan/Epstein thread by actual work object and beneficiary: Black personal/family tax, founder tax, Apollo corporate, Athene/insurance, third-party introduction or unrelated business."
  ∷ disclosure-acquisition blackMandateBoundary 100
    "Acquire engagement scopes and billing/work records defining what Apollo means by Epstein's tax work for Black; do not infer scope from the label alone."
  ∷ disclosure-acquisition apolloInternalScopeDefinition 99
    "Acquire the analysis behind Apollo's 2026 use of 'business or personal relationship' and how direct meetings/work exchanges were classified for disclosure purposes."
  ∷ disclosure-acquisition compensationAndBilling 99
    "Test whether Rowan/Apollo-related work generated any distinct compensation or was bundled into Black's aggregate payments."
  ∷ disclosure-acquisition boardDisclosureProcess 98
    "Trace what primary records Apollo's board, conflicts committee and disclosure counsel reviewed when making the 2020-2026 public statements."
  ∷ []
