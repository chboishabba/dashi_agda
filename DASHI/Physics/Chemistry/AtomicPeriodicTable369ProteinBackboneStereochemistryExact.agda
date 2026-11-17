module DASHI.Physics.Chemistry.AtomicPeriodicTable369ProteinBackboneStereochemistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl; sym; trans)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AlanineChiralEmpiricalExact as Alanine
import DASHI.Biology.Protein.ProteinConformationAttractor as Conformation
import DASHI.Biology.Protein.ProteinFunctionProjection as Function

------------------------------------------------------------------------
-- PROTEIN BACKBONE STEREOCHEMISTRY FIBRE
--
-- Cross-pollination target:
--
--   residue stereochemistry
--     -> peptide-backbone local geometry / torsion residual
--     -> conformational fibre
--     -> contextual function projection.
--
-- Primary sequence is therefore a coarse chart, not a definitionally complete
-- 3-D protein state.  The finite witness below pays only the nonfactorability
-- proof shape.  It does not claim that alpha/beta labels exhaust real protein
-- geometry or that a Ramachandran region determines a unique fold.
------------------------------------------------------------------------

data PrimarySequence : Set where
  samePrimarySequence : PrimarySequence

data BackboneRichState : Set where
  alphaLikeBackbone : BackboneRichState
  betaLikeBackbone : BackboneRichState

data BackboneTorsionResidual : Set where
  alphaLikeTorsion : BackboneTorsionResidual
  betaLikeTorsion : BackboneTorsionResidual

data BackboneConformationReadout : Set where
  alphaLikeConformation : BackboneConformationReadout
  betaLikeConformation : BackboneConformationReadout

primarySequence : BackboneRichState → PrimarySequence
primarySequence alphaLikeBackbone = samePrimarySequence
primarySequence betaLikeBackbone = samePrimarySequence

backboneResidual : BackboneRichState → BackboneTorsionResidual
backboneResidual alphaLikeBackbone = alphaLikeTorsion
backboneResidual betaLikeBackbone = betaLikeTorsion

conformationReadout : BackboneRichState → BackboneConformationReadout
conformationReadout alphaLikeBackbone = alphaLikeConformation
conformationReadout betaLikeBackbone = betaLikeConformation

sameSequencePair :
  primarySequence alphaLikeBackbone ≡ primarySequence betaLikeBackbone
sameSequencePair = refl

backboneResidualSeparates :
  backboneResidual alphaLikeBackbone ≡ backboneResidual betaLikeBackbone → ⊥
backboneResidualSeparates ()

conformationSeparates :
  conformationReadout alphaLikeBackbone
  ≡ conformationReadout betaLikeBackbone → ⊥
conformationSeparates ()

record FactorsThroughPrimarySequence : Set where
  constructor factorsThroughPrimarySequence
  field
    factor : PrimarySequence → BackboneConformationReadout
    law :
      (x : BackboneRichState) →
      conformationReadout x ≡ factor (primarySequence x)

open FactorsThroughPrimarySequence public

backboneConformationDoesNotFactorThroughPrimarySequence :
  FactorsThroughPrimarySequence → ⊥
backboneConformationDoesNotFactorThroughPrimarySequence F =
  conformationSeparates
    (trans
      (law F alphaLikeBackbone)
      (sym (law F betaLikeBackbone)))

------------------------------------------------------------------------
-- Existing downstream carriers reused rather than replaced.
------------------------------------------------------------------------

alanineStereochemistrySurface : Set
alanineStereochemistrySurface = Alanine.AlanineEnantiomer

proteinConformationSystemSurface : Set₁
proteinConformationSystemSurface = Conformation.ProteinConformationSystem

proteinMultipleAttractorSurface :
  Conformation.ProteinConformationSystem → Set₁
proteinMultipleAttractorSurface = Conformation.MultipleAttractorWitness

proteinFunctionSystemSurface : Set₁
proteinFunctionSystemSurface = Function.ProteinFunctionSystem

------------------------------------------------------------------------
-- Snowball attribution: DOI / QID / primary / Dewey / link / OEIS.
-- Unverified catalogue coordinates remain unresolved instead of being inferred.
------------------------------------------------------------------------

record BackboneSourceCoordinate : Set where
  constructor backboneSourceCoordinate
  field
    label : String
    doi : String
    qid : String
    dewey : String
    primaryStatus : String
    directLink : String
    oeis : String
    sourceRole : String

ramachandran1963 : BackboneSourceCoordinate
ramachandran1963 =
  backboneSourceCoordinate
    "Ramachandran, Ramakrishnan and Sasisekharan, Stereochemistry of polypeptide chain configurations"
    "10.1016/S0022-2836(63)80023-6"
    "source-article QID unresolved in inspected sources"
    "exact article-level Dewey unresolved"
    "primary research article"
    "https://doi.org/10.1016/S0022-2836(63)80023-6"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "primary stereochemical source for allowed peptide-backbone conformational regions; not a unique-fold theorem"

proteinDataBank1971 : BackboneSourceCoordinate
proteinDataBank1971 =
  backboneSourceCoordinate
    "Protein Data Bank archival route"
    "10.1038/newbio233223b0"
    "Q766195"
    "exact database-item Dewey unresolved"
    "primary archive announcement / structural-data infrastructure source"
    "https://doi.org/10.1038/newbio233223b0"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "acquisition route for experimentally deposited macromolecular 3-D structures; archive presence does not import a folding mechanism"

proteinStructureSemanticCoordinate : BackboneSourceCoordinate
proteinStructureSemanticCoordinate =
  backboneSourceCoordinate
    "protein structure semantic coordinate"
    "not a single publication DOI"
    "Q735188"
    "exact item-level Dewey unresolved"
    "catalogue / semantic-navigation object"
    "https://www.wikidata.org/wiki/Q735188"
    "not an integer-sequence object"
    "navigation coordinate only; primary structure Q899763, secondary structure Q904984, tertiary structure Q898483 remain distinct levels"

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record ProteinBackboneStereochemistryBoundary : Set where
  constructor proteinBackboneStereochemistryBoundary
  field
    alanineChiralDonorAvailable : Bool
    alanineChiralDonorAvailableIsTrue :
      alanineChiralDonorAvailable ≡ true

    samePrimarySequenceCanRetainDistinctBackboneResidual : Bool
    samePrimarySequenceCanRetainDistinctBackboneResidualIsTrue :
      samePrimarySequenceCanRetainDistinctBackboneResidual ≡ true

    backboneConformationFactorsThroughPrimarySequenceAlone : Bool
    backboneConformationFactorsThroughPrimarySequenceAloneIsFalse :
      backboneConformationFactorsThroughPrimarySequenceAlone ≡ false

    ramachandranBackboneConstraintSourcePaid : Bool
    ramachandranBackboneConstraintSourcePaidIsTrue :
      ramachandranBackboneConstraintSourcePaid ≡ true

    pdbArchiveRoutePaid : Bool
    pdbArchiveRoutePaidIsTrue : pdbArchiveRoutePaid ≡ true

    ramachandranAllowedRegionProvesUniqueFold : Bool
    ramachandranAllowedRegionProvesUniqueFoldIsFalse :
      ramachandranAllowedRegionProvesUniqueFold ≡ false

    backboneTorsionAloneDeterminesProteinFunction : Bool
    backboneTorsionAloneDeterminesProteinFunctionIsFalse :
      backboneTorsionAloneDeterminesProteinFunction ≡ false

    pdbEntryImportsFoldingMechanism : Bool
    pdbEntryImportsFoldingMechanismIsFalse :
      pdbEntryImportsFoldingMechanism ≡ false

canonicalProteinBackboneStereochemistryBoundary :
  ProteinBackboneStereochemistryBoundary
canonicalProteinBackboneStereochemistryBoundary =
  proteinBackboneStereochemistryBoundary
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
