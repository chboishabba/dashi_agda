module DASHI.Biology.BH4SpatialOriginalQDPRStoichiometryExact where

-- Original source / physical location weld for ONE genuine Rhea chemistry.
-- RHEA:32253: q-6,7-dihydrobiopterin + NADH + H+ -> BH4 + NAD+.
-- Reactome R-HSA-71130.5: QDPR homodimer, Homo sapiens, cytosol.
-- Source chemistry is original; numerical turnover/physiological transport
-- and endothelial identity are NOT obtained from this stoichiometry.
-- Attribution: Rhea, ChEBI, Reactome curators and original authors;
-- Kimberly Kitzerow owns her separately source-qualified proposed
-- pathway ordering, not the underlying QDPR reaction chemistry.

open import DASHI.Core.Prelude

import DASHI.Biology.BH4SystemStateExact as System
import DASHI.Biology.Molecular.BH4MolecularStoichiometryExact as Stoich
import DASHI.Biology.BH4SharedSourceTargetRedoxDynamicsExact as Redox
import DASHI.Biology.BH4SpatialConnectivityCirculationExact as Spatial

data SelectedPterin : Set where
  q67Dihydrobiopterin : SelectedPterin
  tetrahydrobiopterin : SelectedPterin
  genericUnresolvedBH2 : SelectedPterin

-- qDHB is a specific tautomer/isomer; a generic BH2 measurement must
-- not silently be promoted to this exact original Rhea reactant.
genericBH2IsNotExactQDHB :
  genericUnresolvedBH2 ≡ q67Dihydrobiopterin → ⊥
genericBH2IsNotExactQDHB ()

record QDPRCytosolicSourceReceipt : Set where
  constructor qdpr-cytosolic-source-receipt
  field
    reactionReference : String
    humanReactomeReference : String
    originalCompartment : System.Compartment
    originalCompartmentIsCytosol :
      originalCompartment ≡ System.cytosol
    qDHBReactant : SelectedPterin
    qDHBReactantIsSpecific :
      qDHBReactant ≡ q67Dihydrobiopterin
    bh4Product : SelectedPterin
    bh4ProductIsSpecific :
      bh4Product ≡ tetrahydrobiopterin
    originalCHNOPBalance :
      Stoich.qdprSubstrateInventory ≡ Stoich.qdprProductInventory
    originalChargeBalance :
      Stoich.qdprSubstrateCharge ≡ Stoich.qdprProductCharge
    originalReactionRateMeasured : Bool
    originalSameCellBH4BH2Measured : Bool
    originalMembraneTransferProven : Bool

open QDPRCytosolicSourceReceipt public

canonicalOriginalQDPRCytosolicSourceReceipt : QDPRCytosolicSourceReceipt
canonicalOriginalQDPRCytosolicSourceReceipt =
  qdpr-cytosolic-source-receipt
    "RHEA:32253; CHEBI:43120 + CHEBI:57945 + CHEBI:15378 -> CHEBI:59560 + CHEBI:57540"
    "R-HSA-71130.5; Homo sapiens; cytosolic QDPR dimer"
    System.cytosol refl
    q67Dihydrobiopterin refl
    tetrahydrobiopterin refl
    Stoich.qdprAtomsConserved
    Stoich.qdprChargeConserved
    false false false

theSelectedOriginalReactionIsAtomBalanced :
  originalCHNOPBalance canonicalOriginalQDPRCytosolicSourceReceipt
    ≡ Stoich.qdprAtomsConserved
theSelectedOriginalReactionIsAtomBalanced = refl

theSelectedOriginalReactionIsChargeBalanced :
  originalChargeBalance canonicalOriginalQDPRCytosolicSourceReceipt
    ≡ Stoich.qdprChargeConserved
theSelectedOriginalReactionIsChargeBalanced = refl

-- Explicit distinction from the simplified lumped BH4/BH2 event semantics.
-- These existing formal event carriers may not be identified without a
-- source-qualified physical refinement respecting qDHB/NADH/NAD+ identities.
selectedToyRedoxCarrier : Set
selectedToyRedoxCarrier = Redox.SharedSourceTargetRedox

sourceSelectedCirculationCarrier : Set₁
sourceSelectedCirculationCarrier = Spatial.ContextIndexedCirculation

originalKineticFluxPaidIsFalse :
  originalReactionRateMeasured canonicalOriginalQDPRCytosolicSourceReceipt
    ≡ false
originalKineticFluxPaidIsFalse = refl

originalMembraneTransferPaidIsFalse :
  originalMembraneTransferProven canonicalOriginalQDPRCytosolicSourceReceipt
    ≡ false
originalMembraneTransferPaidIsFalse = refl
