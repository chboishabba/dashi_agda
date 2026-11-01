module DASHI.Wikimedia.IbrahimCannabisTerpenePubChemCIDAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimCannabisTerpeneIdentityInteractionParetoExact as Parent

------------------------------------------------------------------------
-- PUBCHEM CID AUTHORITY LAYER
--
-- PubChem Compound is the registry source of record for PubChem CIDs in this
-- tranche. Wikidata is a secondary semantic/xlink coordinate and may repeat a
-- PubChem CID, but it does not become the primary CID authority merely by
-- carrying that external identifier.
------------------------------------------------------------------------

record CIDAuthorityReceipt : Set where
  constructor cid-authority-receipt
  field
    canonicalLabel : String
    pubChemCID : String
    pubChemCompoundLink : String
    molecularFormula : String
    wikidataQid : String
    wikidataRole : String
    cidAuthority : String
    cidPaidFromPubChemCompound : Bool
    wikidataIsPrimaryCIDAuthority : Bool
    occurrenceInCannabisPaid : Bool
    interactionMechanismPaid : Bool
open CIDAuthorityReceipt public

myrceneCID : CIDAuthorityReceipt
myrceneCID = cid-authority-receipt
  "myrcene / beta-myrcene"
  "31253"
  "https://pubchem.ncbi.nlm.nih.gov/compound/31253"
  "C10H16"
  "Q424577"
  "secondary semantic identity / cross-identifier coordinate"
  "PubChem Compound"
  true false false false

limoneneCID : CIDAuthorityReceipt
limoneneCID = cid-authority-receipt
  "(+/-)-limonene / dipentene"
  "22311"
  "https://pubchem.ncbi.nlm.nih.gov/compound/22311"
  "C10H16"
  "Q278809"
  "secondary semantic identity / racemic-group crosslink"
  "PubChem Compound"
  true false false false

alphaPineneCID : CIDAuthorityReceipt
alphaPineneCID = cid-authority-receipt
  "(+/-)-alpha-pinene"
  "6654"
  "https://pubchem.ncbi.nlm.nih.gov/compound/6654"
  "C10H16"
  "Q27104380"
  "secondary semantic identity / stereoisomer-group crosslink"
  "PubChem Compound"
  true false false false

betaPineneCID : CIDAuthorityReceipt
betaPineneCID = cid-authority-receipt
  "beta-pinene"
  "14896"
  "https://pubchem.ncbi.nlm.nih.gov/compound/14896"
  "C10H16"
  "Q300928"
  "secondary semantic identity / cross-identifier coordinate"
  "PubChem Compound"
  true false false false

linaloolCID : CIDAuthorityReceipt
linaloolCID = cid-authority-receipt
  "linalool"
  "6549"
  "https://pubchem.ncbi.nlm.nih.gov/compound/6549"
  "C10H18O"
  "Q410932"
  "secondary semantic identity / cross-identifier coordinate"
  "PubChem Compound"
  true false false false

betaCaryophylleneCID : CIDAuthorityReceipt
betaCaryophylleneCID = cid-authority-receipt
  "(-)-beta-caryophyllene / (-)-caryophyllene"
  "5281515"
  "https://pubchem.ncbi.nlm.nih.gov/compound/5281515"
  "C15H24"
  "Q421614"
  "secondary semantic identity / stereochemical crosslink"
  "PubChem Compound"
  true false false false

------------------------------------------------------------------------
-- Registry-source firewall.
------------------------------------------------------------------------

data WikidataCIDFieldCreatesPubChemAuthority : Set where
data PubChemCIDCreatesCannabisOccurrence : Set where
data PubChemCIDCreatesInteractionMechanism : Set where

data MatchingCIDCollapsesStereochemistry : Set where

wikidataCIDFieldDoesNotCreatePubChemAuthority :
  WikidataCIDFieldCreatesPubChemAuthority → ⊥
wikidataCIDFieldDoesNotCreatePubChemAuthority ()

pubChemCIDDoesNotCreateCannabisOccurrence :
  PubChemCIDCreatesCannabisOccurrence → ⊥
pubChemCIDDoesNotCreateCannabisOccurrence ()

pubChemCIDDoesNotCreateInteractionMechanism :
  PubChemCIDCreatesInteractionMechanism → ⊥
pubChemCIDDoesNotCreateInteractionMechanism ()

matchingCIDDoesNotCollapseStereochemistry :
  MatchingCIDCollapsesStereochemistry → ⊥
matchingCIDDoesNotCollapseStereochemistry ()

parentIdentityReference : String
parentIdentityReference =
  "Parent registry rows remain useful, but CID provenance is refined here: PubChem Compound owns CID payment; Wikidata carries QID/xlink corroboration."

record PubChemCIDAuthorityBoundary : Set where
  constructor pubchem-cid-authority-boundary
  field
    pubChemCompoundIsCIDAuthority : Bool
    wikidataIsSecondaryXlink : Bool
    molecularFormulaRetained : Bool
    stereochemistryScopeRetained : Bool
    cidCreatesOccurrence : Bool
    cidCreatesMechanism : Bool
open PubChemCIDAuthorityBoundary public

canonicalPubChemCIDAuthorityBoundary : PubChemCIDAuthorityBoundary
canonicalPubChemCIDAuthorityBoundary =
  pubchem-cid-authority-boundary true true true true false false
