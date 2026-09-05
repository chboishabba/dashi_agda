module DASHI.Chemistry.AlliumMolecularIdentityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ALLIUM MOLECULAR IDENTITY / COMPOSITION
--
-- Identity anchors are database-level molecular descriptors, not biological
-- mechanism claims.
--
-- PubChem:
--   Alliin  CID 9576089: C6H11NO3S
--     canonical isomeric SMILES C=CC[S@](=O)C[C@@H](C(=O)O)N
--   Allicin CID 65036: C6H10OS2
--     SMILES C=CCSS(=O)CC=C
--     InChIKey JDLKFOPOAOFWQN-UHFFFAOYSA-N
--   (E)-Ajoene CID 5386591: C9H14OS3
--     SMILES C=CCSS/C=C/CS(=O)CC=C
--
-- The formula carrier is explicit so downstream stoichiometry need not infer
-- composition from compound names or prose labels.
------------------------------------------------------------------------

record ElementCount : Set where
  constructor elementCount
  field
    carbon hydrogen nitrogen oxygen sulfur : Nat

open ElementCount public

record MolecularIdentity : Set where
  constructor molecularIdentity
  field
    commonName : String
    pubChemCID : String
    formulaText : String
    composition : ElementCount
    smiles : String
    inchiKey : String
    identitySource : String

open MolecularIdentity public

alliinIdentity : MolecularIdentity
alliinIdentity = molecularIdentity
  "alliin"
  "PubChem CID 9576089"
  "C6H11NO3S"
  (elementCount 6 11 1 3 1)
  "C=CC[S@](=O)C[C@@H](C(=O)O)N"
  "XUHLIQGRKRUKPH-DYEAUMGKSA-N"
  "PubChem / ChEBI identity descriptors"

allicinIdentity : MolecularIdentity
allicinIdentity = molecularIdentity
  "allicin (diallyl thiosulfinate)"
  "PubChem CID 65036"
  "C6H10OS2"
  (elementCount 6 10 0 1 2)
  "C=CCSS(=O)CC=C"
  "JDLKFOPOAOFWQN-UHFFFAOYSA-N"
  "PubChem identity descriptors"

eAjoeneIdentity : MolecularIdentity
eAjoeneIdentity = molecularIdentity
  "(E)-ajoene"
  "PubChem CID 5386591"
  "C9H14OS3"
  (elementCount 9 14 0 1 3)
  "C=CCSS/C=C/CS(=O)CC=C"
  "IXELFRRANAOWSF-FNORWQNLSA-N"
  "PubChem / ChEBI identity descriptors"

------------------------------------------------------------------------
-- Definitionally checked formula coordinates.
------------------------------------------------------------------------

allicinCarbon : carbon (composition allicinIdentity) ≡ 6
allicinCarbon = refl

allicinHydrogen : hydrogen (composition allicinIdentity) ≡ 10
allicinHydrogen = refl

allicinOxygen : oxygen (composition allicinIdentity) ≡ 1
allicinOxygen = refl

allicinSulfur : sulfur (composition allicinIdentity) ≡ 2
allicinSulfur = refl

ajoeneSulfur : sulfur (composition eAjoeneIdentity) ≡ 3
ajoeneSulfur = refl

alliinNitrogen : nitrogen (composition alliinIdentity) ≡ 1
alliinNitrogen = refl

------------------------------------------------------------------------
-- Structural-family receipts. These identify chemically meaningful motifs but
-- do not assert a reaction merely from motif presence.
------------------------------------------------------------------------

data FunctionalMotif : Set where
  allyl
  sulfoxide
  thiosulfinate
  disulfide
  aminoAcid
  carboxyl
  : FunctionalMotif

record StructuralMotifReceipt : Set where
  constructor structuralMotifReceipt
  field
    molecule : MolecularIdentity
    motif : FunctionalMotif
    descriptorBasis : String
    sourceReference : String

allicinThiosulfinate : StructuralMotifReceipt
allicinThiosulfinate = structuralMotifReceipt
  allicinIdentity thiosulfinate
  "diallyl thiosulfinate; S-S(=O) motif represented in canonical SMILES"
  "PubChem CID 65036; Borlinghaus et al. 2014 PMID 25153873"

ajoeneSulfoxideDisulfide : StructuralMotifReceipt
ajoeneSulfoxideDisulfide = structuralMotifReceipt
  eAjoeneIdentity sulfoxide
  "ajoene contains sulfoxide and disulfide functionality"
  "PubChem CID 5386591"

record MolecularIdentityBoundary : Set where
  constructor molecularIdentityBoundary
  field
    sameFormulaImpliesSameMolecule : Bool
    sameFormulaImpliesSameMoleculeIsFalse : sameFormulaImpliesSameMolecule ≡ false

    sameMotifImpliesSameReactivity : Bool
    sameMotifImpliesSameReactivityIsFalse : sameMotifImpliesSameReactivity ≡ false

    smilesStringAloneProvesBiologicalMechanism : Bool
    smilesStringAloneProvesBiologicalMechanismIsFalse :
      smilesStringAloneProvesBiologicalMechanism ≡ false

canonicalMolecularIdentityBoundary : MolecularIdentityBoundary
canonicalMolecularIdentityBoundary = molecularIdentityBoundary
  false refl false refl false refl
