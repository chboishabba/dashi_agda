module DASHI.Biology.Protein.AlliumThiolProteinInteractionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.AlliumMolecularIdentityExact as Identity
import DASHI.Chemistry.AlliumOrganosulfurMechanismExact as Mechanism

------------------------------------------------------------------------
-- PROTEIN-THIOL TARGET LAYER
--
-- Allicin is a reactive sulfur species and reacts with accessible low-molecular
-- weight thiols and accessible cysteine thiols in proteins. The literature
-- describes S-thioallylation / thiol-disulfide-exchange-like chemistry and
-- widespread proteomic targets. Accessibility and local chemical context are
-- therefore explicit rather than treating every cysteine as an equal target.
--
-- Source anchors:
--   Rabinkov et al. 1998 DOI 10.1016/S0304-4165(97)00104-9
--   Borlinghaus et al. 2014 PMID 25153873
--   Borlinghaus et al. 2021 PMID 33801955 / PMCID PMC8001868
------------------------------------------------------------------------

data ResidueKind : Set where
  cysteine otherResidue : ResidueKind

data ThiolState : Set where
  reducedThiol
  thiolateLike
  oxidized
  disulfideBound
  sThioallylated
  inaccessible
  : ThiolState

record ProteinSite : Set where
  constructor proteinSite
  field
    proteinReference : String
    residueReference : String
    residueKind : ResidueKind
    localEnvironmentReference : String
    startingThiolState : ThiolState

open ProteinSite public

record ProteinThiolReactionContext : Set where
  constructor proteinThiolReactionContext
  field
    pHReference : String
    redoxBufferReference : String
    solventAccessibilityReference : String
    localElectrostaticReference : String
    allicinExposureReference : String

open ProteinThiolReactionContext public

record SThioallylationReceipt : Set where
  constructor sThioallylationReceipt
  field
    reagent : Identity.MolecularIdentity
    site : ProteinSite
    context : ProteinThiolReactionContext
    productState : ThiolState
    reactionClass : String
    sourceReference : String
    scopeBoundary : String

open SThioallylationReceipt public

canonicalAllicinProteinThiolReceipt : SThioallylationReceipt
canonicalAllicinProteinThiolReceipt = sThioallylationReceipt
  Identity.allicinIdentity
  (proteinSite
    "generic protein target; identity must be supplied by experiment"
    "accessible cysteine thiol"
    cysteine
    "local pKa / solvent exposure / neighbouring residues remain target-specific"
    reducedThiol)
  (proteinThiolReactionContext
    "reaction rate is pH/context dependent"
    "GSH/bacillithiol/other low-molecular-weight thiols compete for reagent"
    "accessible thiol required"
    "target-specific"
    "allicin exposure")
  sThioallylated
  "nucleophilic thiol attack / S-thioallylation"
  "Rabinkov et al. 1998; Borlinghaus et al. 2021 PMID 33801955"
  "generic chemical target class; not a claim that every protein cysteine is modified"

------------------------------------------------------------------------
-- Causal propagation is typed by level. Chemical modification can change a
-- protein's function, but that bridge requires its own target-specific receipt.
------------------------------------------------------------------------

data ProteinFunctionalEffect : Set where
  noResolvedEffect
  reducedActivity
  increasedActivity
  alteredBinding
  alteredLocalization
  destabilized
  : ProteinFunctionalEffect

record ProteinFunctionModificationReceipt : Set where
  constructor proteinFunctionModificationReceipt
  field
    chemicalModification : SThioallylationReceipt
    functionalEffect : ProteinFunctionalEffect
    functionalAssayReference : String
    sourceReference : String
    targetSpecific : Bool

open ProteinFunctionModificationReceipt public

record ThiolProteinBoundary : Set where
  constructor thiolProteinBoundary
  field
    cysteinePresenceProvesModification : Bool
    cysteinePresenceProvesModificationIsFalse :
      cysteinePresenceProvesModification ≡ false

    chemicalModificationProvesFunctionalInhibition : Bool
    chemicalModificationProvesFunctionalInhibitionIsFalse :
      chemicalModificationProvesFunctionalInhibition ≡ false

    oneProteinTargetProvesUniqueCellularMechanism : Bool
    oneProteinTargetProvesUniqueCellularMechanismIsFalse :
      oneProteinTargetProvesUniqueCellularMechanism ≡ false

    proteomicTargetListIsExhaustive : Bool
    proteomicTargetListIsExhaustiveIsFalse :
      proteomicTargetListIsExhaustive ≡ false

canonicalThiolProteinBoundary : ThiolProteinBoundary
canonicalThiolProteinBoundary = thiolProteinBoundary
  false refl false refl false refl false refl

------------------------------------------------------------------------
-- Weld back to the existing organosulfur action vocabulary.
------------------------------------------------------------------------

record OrganosulfurProteinWeld : Set where
  constructor organosulfurProteinWeld
  field
    molecularAction : Mechanism.MolecularActionReceipt
    proteinReaction : SThioallylationReceipt
    sameCompoundReference : String
    relationMeaning : String

allicinProteinWeld : OrganosulfurProteinWeld
allicinProteinWeld = organosulfurProteinWeld
  Mechanism.allicinSThioallylationReceipt
  canonicalAllicinProteinThiolReceipt
  "both receipts refer to allicin"
  "mechanism-level S-thioallylation action refined into an explicit protein-site reaction context"
