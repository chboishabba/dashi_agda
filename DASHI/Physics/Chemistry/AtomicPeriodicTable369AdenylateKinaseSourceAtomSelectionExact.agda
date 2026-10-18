module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSourceAtomSelectionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAtomisticConfigurationExact as Config
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCollectiveVariableDefinitionAcquisitionExact as CV
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- SOURCE-OWNED ATOM / RESIDUE SELECTIONS FOR theta1, theta2, dLN
--
-- Li, Liu & Ji 2015 Figure 1 defines theta1/theta2 with explicit backbone
-- residue groups and defines dLN as the COM distance between the LID and NMP
-- domains.  This owner turns those strings into typed range/selection objects.
-- It deliberately does not invent a more specific dLN atom subset than the
-- Figure-1 caption supplies.
------------------------------------------------------------------------

articleDOI = Attr.articleDOI
articlePMID = Attr.articlePMID
articlePMCID = Attr.articlePMCID
articleQID = Attr.articleQID
adkQID = Attr.adkQID
adkUniProt = Attr.adkUniProt

sourceDeweyCoordinate : String
sourceDeweyCoordinate =
  "exact Li-Liu-Ji article/source-item Dewey coordinate unresolved; DOI/PMID/PMCID retained"

record ResidueSpan : Set where
  constructor residue-span
  field
    firstResidue : Nat
    lastResidue : Nat
open ResidueSpan public

data AtomSubsetKind : Set where
  backboneAtoms : AtomSubsetKind
  sourceDomainAtoms : AtomSubsetKind
  explicitlyNamedAtoms : AtomSubsetKind
  unresolvedAtomSubset : AtomSubsetKind

record AtomSelectionSpec : Set where
  constructor atom-selection-spec
  field
    label : String
    residueSpans : List ResidueSpan
    atomSubset : AtomSubsetKind
    chainScope : String
    sourceLocator : String
    sourceDefinition : CV.CollectiveVariableDefinition
    interpretation : String
    exactResidueSelectionPaid : Bool
    exactAtomSubsetPaid : Bool
open AtomSelectionSpec public

coreBackboneSelection : AtomSelectionSpec
coreBackboneSelection = atom-selection-spec
  "CORE backbone COM selection used in theta1/theta2"
  (residue-span 1 8 ∷ residue-span 79 85 ∷ residue-span 104 110 ∷ residue-span 190 198 ∷ [])
  backboneAtoms
  "same AdK chain as the evaluated configuration"
  "Li-Liu-Ji 2015 Figure 1 caption"
  CV.thetaOneDefinition
  "source-paid CORE backbone residue groups; theta2 reuses the identical CORE selection"
  true true

lidBackboneSelection : AtomSelectionSpec
lidBackboneSelection = atom-selection-spec
  "LID backbone COM selection used in theta1"
  (residue-span 123 155 ∷ [])
  backboneAtoms
  "same AdK chain as the evaluated configuration"
  "Li-Liu-Ji 2015 Figure 1 caption"
  CV.thetaOneDefinition
  "source-paid LID backbone residues 123--155"
  true true

hingeBackboneSelection : AtomSelectionSpec
hingeBackboneSelection = atom-selection-spec
  "hinge backbone COM selection used in theta1/theta2"
  (residue-span 161 165 ∷ [])
  backboneAtoms
  "same AdK chain as the evaluated configuration"
  "Li-Liu-Ji 2015 Figure 1 caption"
  CV.thetaOneDefinition
  "source-paid hinge backbone residues 161--165"
  true true

nmpBackboneSelection : AtomSelectionSpec
nmpBackboneSelection = atom-selection-spec
  "NMP backbone COM selection used in theta2"
  (residue-span 50 59 ∷ [])
  backboneAtoms
  "same AdK chain as the evaluated configuration"
  "Li-Liu-Ji 2015 Figure 1 caption"
  CV.thetaTwoDefinition
  "source-paid NMP backbone residues 50--59"
  true true

lidDomainSelection : AtomSelectionSpec
lidDomainSelection = atom-selection-spec
  "LID domain COM selection used in dLN"
  (residue-span 122 159 ∷ [])
  sourceDomainAtoms
  "same AdK chain as the evaluated configuration"
  "Li-Liu-Ji 2015 Figure 1 caption: LID domain residues 122--159; dLN is COM distance between LID and NMP domains"
  CV.dLnDefinition
  "domain residue extent is source-paid; the caption does not further resolve whether dLN COM uses every atom, backbone only, or another atom subset, so an evaluator must retain that residual explicitly"
  true false

nmpDomainSelection : AtomSelectionSpec
nmpDomainSelection = atom-selection-spec
  "NMP domain COM selection used in dLN"
  (residue-span 30 59 ∷ [])
  sourceDomainAtoms
  "same AdK chain as the evaluated configuration"
  "Li-Liu-Ji 2015 Figure 1 caption: NMP domain residues 30--59; dLN is COM distance between LID and NMP domains"
  CV.dLnDefinition
  "domain residue extent is source-paid; exact atom-subset semantics remain a same-object evaluator obligation"
  true false

------------------------------------------------------------------------
-- Typed three-CV selection bundle.
------------------------------------------------------------------------

record AdKThreeCVSelections : Set where
  constructor adk-three-cv-selections
  field
    thetaOneFirst : AtomSelectionSpec
    thetaOneVertex : AtomSelectionSpec
    thetaOneThird : AtomSelectionSpec
    thetaTwoFirst : AtomSelectionSpec
    thetaTwoVertex : AtomSelectionSpec
    thetaTwoThird : AtomSelectionSpec
    dLnFirst : AtomSelectionSpec
    dLnSecond : AtomSelectionSpec
    sourceIdentityReference : String
    deweyCoordinate : String
open AdKThreeCVSelections public

canonicalAdKThreeCVSelections : AdKThreeCVSelections
canonicalAdKThreeCVSelections = adk-three-cv-selections
  lidBackboneSelection
  hingeBackboneSelection
  coreBackboneSelection
  nmpBackboneSelection
  coreBackboneSelection
  hingeBackboneSelection
  lidDomainSelection
  nmpDomainSelection
  "Li-Liu-Ji 2015 DOI 10.1016/j.bpj.2015.06.059; PMID 26244746; PMCID PMC4572606"
  sourceDeweyCoordinate

------------------------------------------------------------------------
-- A resolver turns a typed source selection into actual atom indices for one
-- same-object topology.  The selection specification itself does not perform
-- topology lookup by magic.
------------------------------------------------------------------------

record ResolvedAtomSelection
  (configuration : Config.AtomisticConfiguration)
  (spec : AtomSelectionSpec) : Set where
  constructor resolved-atom-selection
  field
    selectedStableAtomIndices : List Nat
    sameObjectTopologyReceipt : String
    residueSelectionMatchesSpec : Set
    atomSubsetMatchesSpec : Set
    nonemptySelection : Set
open ResolvedAtomSelection public

record AdKSelectionResolver (configuration : Config.AtomisticConfiguration) : Set₁ where
  constructor adk-selection-resolver
  field
    resolve : (spec : AtomSelectionSpec) → ResolvedAtomSelection configuration spec
    resolverProvenance : String
    unresolvedDLnAtomSubsetExplicit : Bool
open AdKSelectionResolver public

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data SameResidueNumberAloneSelectsAtom : Set where
data SourceLabelCreatesSelectionTruth : Set where
data FigureCaptionResolvesUnstatedDLnAtomSubset : Set where
data SelectionSpecCreatesCoordinates : Set where

sameResidueNumberAloneDoesNotSelectAtom : SameResidueNumberAloneSelectsAtom → ⊥
sameResidueNumberAloneDoesNotSelectAtom ()

sourceLabelDoesNotCreateSelectionTruth : SourceLabelCreatesSelectionTruth → ⊥
sourceLabelDoesNotCreateSelectionTruth ()

figureCaptionDoesNotResolveUnstatedDLnSubset : FigureCaptionResolvesUnstatedDLnAtomSubset → ⊥
figureCaptionDoesNotResolveUnstatedDLnSubset ()

selectionSpecDoesNotCreateCoordinates : SelectionSpecCreatesCoordinates → ⊥
selectionSpecDoesNotCreateCoordinates ()

record AdKSourceAtomSelectionBoundary : Set where
  constructor adk-source-atom-selection-boundary
  field
    thetaOneSelectionsTyped : Bool
    thetaTwoSelectionsTyped : Bool
    dLnDomainSelectionsTyped : Bool
    figureOneSourceLocatorRetained : Bool
    articleIdentifiersRetained : Bool
    sourceDeweyExplicitlyUnresolved : Bool
    dLnDomainResidueExtentPaid : Bool
    dLnExactAtomSubsetPaidFromCaption : Bool
    sameResidueNumberAloneSelectsAtom : Bool
    sourceLabelCreatesSelectionTruth : Bool
    selectionSpecCreatesCoordinates : Bool
open AdKSourceAtomSelectionBoundary public

canonicalAdKSourceAtomSelectionBoundary : AdKSourceAtomSelectionBoundary
canonicalAdKSourceAtomSelectionBoundary =
  adk-source-atom-selection-boundary
    true true true true true true true false
    false false false
