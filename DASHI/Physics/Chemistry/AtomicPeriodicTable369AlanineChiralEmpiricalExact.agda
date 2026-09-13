module DASHI.Physics.Chemistry.AtomicPeriodicTable369AlanineChiralEmpiricalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans)

------------------------------------------------------------------------
-- EMPIRICAL SAME-COARSE CHIRAL SEPARATING PAIR: D/L ALANINE
--
-- Source-facing identity:
--   L-alanine: PubChem 5950; ChEBI 16977; Wikidata Q218642.
--   D-alanine: PubChem 71080; ChEBI 15570; Wikidata Q27076975.
-- Both authoritative chemistry databases classify the pair as enantiomers and
-- give the same formula C3H7NO2.
--
-- Direct optical source:
--   Ishikawa, Terasawa, Tanaka, Asahi (2017),
--   "Accurate measurement of the optical activity of alanine crystals and the
--   determination of their absolute chirality",
--   Journal of Physics and Chemistry of Solids 104, 257-266,
--   DOI 10.1016/j.jpcs.2017.01.024.
--
-- That paper reports D-alanine crystal dextrorotatory and L-alanine crystal
-- laevorotatory, and reports that crystal and solution optical-activity signs
-- are opposite.  The formal fixture therefore pays a real separating pair and
-- also makes environment/phase part of the observation fibre.
------------------------------------------------------------------------

data AlanineEnantiomer : Set where
  lAlanine : AlanineEnantiomer
  dAlanine : AlanineEnantiomer

data AlanineFormula : Set where
  C3H7NO2 : AlanineFormula

data ChiralityLabel : Set where
  Sconfiguration : ChiralityLabel
  Rconfiguration : ChiralityLabel

data PhaseContext : Set where
  crystal : PhaseContext
  solution : PhaseContext

data OpticalRotationSign : Set where
  dextrorotatory : OpticalRotationSign
  laevorotatory : OpticalRotationSign

formula : AlanineEnantiomer → AlanineFormula
formula lAlanine = C3H7NO2
formula dAlanine = C3H7NO2

chirality : AlanineEnantiomer → ChiralityLabel
chirality lAlanine = Sconfiguration
chirality dAlanine = Rconfiguration

rotation : PhaseContext → AlanineEnantiomer → OpticalRotationSign
rotation crystal lAlanine = laevorotatory
rotation crystal dAlanine = dextrorotatory
rotation solution lAlanine = dextrorotatory
rotation solution dAlanine = laevorotatory

sameFormula : formula lAlanine ≡ formula dAlanine
sameFormula = refl

chiralitySeparates : chirality lAlanine ≡ chirality dAlanine → ⊥
chiralitySeparates ()

crystalRotationSeparates :
  rotation crystal lAlanine ≡ rotation crystal dAlanine → ⊥
crystalRotationSeparates ()

solutionRotationSeparates :
  rotation solution lAlanine ≡ rotation solution dAlanine → ⊥
solutionRotationSeparates ()

lAlaninePhaseSignChanges :
  rotation crystal lAlanine ≡ rotation solution lAlanine → ⊥
lAlaninePhaseSignChanges ()

dAlaninePhaseSignChanges :
  rotation crystal dAlanine ≡ rotation solution dAlanine → ⊥
dAlaninePhaseSignChanges ()

record FormulaOnlyOpticalFactor : Set where
  constructor formulaOnlyOpticalFactor
  field
    factor : AlanineFormula → OpticalRotationSign
    law : (x : AlanineEnantiomer) → rotation crystal x ≡ factor (formula x)

open FormulaOnlyOpticalFactor public

crystalOpticalRotationDoesNotFactorThroughFormula :
  FormulaOnlyOpticalFactor → ⊥
crystalOpticalRotationDoesNotFactorThroughFormula F =
  crystalRotationSeparates
    (trans
      (law F lAlanine)
      (sym (law F dAlanine)))

------------------------------------------------------------------------
-- Snowball attribution ledger.  Navigation identifiers do not import proof.
------------------------------------------------------------------------

record SourceCoordinate : Set where
  constructor sourceCoordinate
  field
    label : String
    doi : String
    qid : String
    pubchem : String
    chebi : String
    dewey : String
    oeis : String
    primaryStatus : String
    directLink : String
    sourceRole : String

lAlanineIdentitySource : SourceCoordinate
lAlanineIdentitySource =
  sourceCoordinate
    "L-alanine"
    "no same-object DOI required for database identity"
    "Q218642"
    "CID 5950"
    "CHEBI:16977"
    "exact item-level Dewey unresolved"
    "not a sequence object; no same-object OEIS coordinate located"
    "curated chemical-identity database object"
    "https://pubchem.ncbi.nlm.nih.gov/compound/5950"
    "identity/formula/configuration coordinate; ChEBI explicitly relates it as enantiomer of D-alanine"

dAlanineIdentitySource : SourceCoordinate
dAlanineIdentitySource =
  sourceCoordinate
    "D-alanine"
    "no same-object DOI required for database identity"
    "Q27076975"
    "CID 71080"
    "CHEBI:15570"
    "exact item-level Dewey unresolved"
    "not a sequence object; no same-object OEIS coordinate located"
    "curated chemical-identity database object"
    "https://pubchem.ncbi.nlm.nih.gov/compound/71080"
    "identity/formula/configuration coordinate; ChEBI explicitly relates it as enantiomer of L-alanine"

ishikawa2017OpticalSource : SourceCoordinate
ishikawa2017OpticalSource =
  sourceCoordinate
    "Ishikawa et al. 2017 alanine-crystal optical-activity measurement"
    "10.1016/j.jpcs.2017.01.024"
    "source-object QID unresolved"
    "not a PubChem identity object"
    "not a ChEBI identity object"
    "exact article-level Dewey unresolved"
    "not an integer-sequence object"
    "primary experimental research article"
    "https://doi.org/10.1016/j.jpcs.2017.01.024"
    "same-object D/L alanine crystal optical-rotation direction and crystal-versus-solution sign-context source"

iupacChiralityTerm : SourceCoordinate
iupacChiralityTerm =
  sourceCoordinate
    "IUPAC Gold Book chirality"
    "10.1351/goldbook.C01058"
    "terminology-item QID unresolved"
    "not a PubChem identity object"
    "not a ChEBI identity object"
    "exact term-level Dewey unresolved"
    "not an integer-sequence object"
    "authoritative terminology source"
    "https://goldbook.iupac.org/terms/view/C01058"
    "defines chirality as non-superposability with the mirror image; terminology only"

record AlanineChiralEmpiricalBoundary : Set where
  constructor alanineChiralEmpiricalBoundary
  field
    sameMolecularFormula : Bool
    sameMolecularFormulaIsTrue : sameMolecularFormula ≡ true

    enantiomerRelationPaid : Bool
    enantiomerRelationPaidIsTrue : enantiomerRelationPaid ≡ true

    crystalOpticalRotationSeparatesEnantiomers : Bool
    crystalOpticalRotationSeparatesEnantiomersIsTrue :
      crystalOpticalRotationSeparatesEnantiomers ≡ true

    opticalRotationSignIndependentOfEnvironment : Bool
    opticalRotationSignIndependentOfEnvironmentIsFalse :
      opticalRotationSignIndependentOfEnvironment ≡ false

    qidOrPubChemIdentityImportsOpticalTheorem : Bool
    qidOrPubChemIdentityImportsOpticalTheoremIsFalse :
      qidOrPubChemIdentityImportsOpticalTheorem ≡ false

    empiricalPairProvesUniversalChiralResponse : Bool
    empiricalPairProvesUniversalChiralResponseIsFalse :
      empiricalPairProvesUniversalChiralResponse ≡ false

canonicalAlanineChiralEmpiricalBoundary : AlanineChiralEmpiricalBoundary
canonicalAlanineChiralEmpiricalBoundary =
  alanineChiralEmpiricalBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
