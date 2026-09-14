module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseMixedStateReferenceSquareExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConformationalEmpiricalExact as EColi
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseNDimGeometricResidualExact as Geo

------------------------------------------------------------------------
-- ADENYLATE-KINASE MIXED-STATE REFERENCE SQUARE
--
-- Literature often displays four useful structural corners:
--
--   4AKE : fully open
--   1AKE : fully closed
--   2AK3 : LID-open / NMP-closed reference
--   1DVR : LID-closed / NMP-open reference
--
-- The high-alpha correction is carrier identity.  4AKE/1AKE are the E. coli
-- same-sequence pair already paid upstream; 2AK3 is bovine mitochondrial
-- adenylate kinase, and 1DVR is a yeast mutant.  Therefore the four-corner set
-- is a cross-homolog structural reference square, not a same-sequence 2x2
-- factorial experiment and not a proof that E. coli NMP/LID motions are
-- independent.
------------------------------------------------------------------------

data DomainGate : Set where
  domainOpen : DomainGate
  domainClosed : DomainGate

record DomainCorner : Set where
  constructor domain-corner
  field
    nmp : DomainGate
    lid : DomainGate
open DomainCorner public

fullyOpenCorner : DomainCorner
fullyOpenCorner = domain-corner domainOpen domainOpen

fullyClosedCorner : DomainCorner
fullyClosedCorner = domain-corner domainClosed domainClosed

lidOpenNmpClosedCorner : DomainCorner
lidOpenNmpClosedCorner = domain-corner domainClosed domainOpen

lidClosedNmpOpenCorner : DomainCorner
lidClosedNmpOpenCorner = domain-corner domainOpen domainClosed

------------------------------------------------------------------------
-- Explicit carrier provenance: corner coordinate != same-object identity.
------------------------------------------------------------------------

data CarrierKind : Set where
  eColiWildTypeCarrier : CarrierKind
  bovineMitochondrialCarrier : CarrierKind
  yeastMutantCarrier : CarrierKind

data StructuralReference : Set where
  ref4AKE : StructuralReference
  ref1AKE : StructuralReference
  ref2AK3 : StructuralReference
  ref1DVR : StructuralReference

corner : StructuralReference → DomainCorner
corner ref4AKE = fullyOpenCorner
corner ref1AKE = fullyClosedCorner
corner ref2AK3 = lidOpenNmpClosedCorner
corner ref1DVR = lidClosedNmpOpenCorner

carrier : StructuralReference → CarrierKind
carrier ref4AKE = eColiWildTypeCarrier
carrier ref1AKE = eColiWildTypeCarrier
carrier ref2AK3 = bovineMitochondrialCarrier
carrier ref1DVR = yeastMutantCarrier

eColiPairSharesCarrier : carrier ref4AKE ≡ carrier ref1AKE
eColiPairSharesCarrier = refl

mixedReferenceDoesNotShareEColiCarrier :
  carrier ref2AK3 ≡ carrier ref4AKE → ⊥
mixedReferenceDoesNotShareEColiCarrier ()

yeastReferenceDoesNotShareEColiCarrier :
  carrier ref1DVR ≡ carrier ref4AKE → ⊥
yeastReferenceDoesNotShareEColiCarrier ()

------------------------------------------------------------------------
-- Reuse the actual E. coli NDim endpoint residual owner.
------------------------------------------------------------------------

eColiEndpointResidualSurface : EColi.AdKResolvedState → Geo.AdKGeometricResidual
eColiEndpointResidualSurface = Geo.geometricResidual

------------------------------------------------------------------------
-- Snowball attribution: DOI / QID / PDB / primary / Dewey / link / OEIS.
------------------------------------------------------------------------

record MixedStateSourceCoordinate : Set where
  constructor mixed-state-source-coordinate
  field
    label : String
    doi : String
    pdb : String
    qid : String
    dewey : String
    directLink : String
    oeis : String
    primaryStatus : String
    sourceRole : String

pdb2AK3Source : MixedStateSourceCoordinate
pdb2AK3Source =
  mixed-state-source-coordinate
    "2AK3 bovine mitochondrial matrix adenylate kinase AMP complex"
    "PDB DOI 10.2210/pdb2AK3/pdb; primary article DOI 10.1016/0022-2836(91)90756-V"
    "2AK3"
    "exact PDB-object/article QID unresolved in inspected sources"
    "exact structure/article Dewey unresolved"
    "https://www.rcsb.org/structure/2AK3"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "primary X-ray structure / primary structural article"
    "cross-homolog LID-open / NMP-closed structural reference; not E. coli same-sequence evidence"

pdb1DVRSource : MixedStateSourceCoordinate
pdb1DVRSource =
  mixed-state-source-coordinate
    "1DVR yeast mutant adenylate kinase ATP-analogue complex"
    "PDB DOI 10.2210/pdb1DVR/pdb; primary article DOI 10.1006/jmbi.1996.0080"
    "1DVR"
    "exact PDB-object/article QID unresolved in inspected sources"
    "exact structure/article Dewey unresolved"
    "https://www.rcsb.org/structure/1DVR"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "primary X-ray structure / primary structural article"
    "cross-homolog LID-closed / NMP-open structural reference; primary paper discusses largely independent domain motions in that system"

frontiers2021FourStateMap : MixedStateSourceCoordinate
frontiers2021FourStateMap =
  mixed-state-source-coordinate
    "2021 AdK conformational-landscape four-crystal-state map"
    "10.3389/fmolb.2021.781635"
    "1AKE / 4AKE / 2AK3 / 1DVR"
    "source-article QID unresolved"
    "exact article-level Dewey unresolved"
    "https://doi.org/10.3389/fmolb.2021.781635"
    "not an integer-sequence object"
    "peer-reviewed computational/structural synthesis"
    "names fully closed, fully open, LID-open and NMP-open reference structures; does not make them one sequence carrier"

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record MixedStateReferenceBoundary : Set where
  constructor mixed-state-reference-boundary
  field
    fourStructuralCornersRepresented : Bool
    fourStructuralCornersRepresentedIsTrue : fourStructuralCornersRepresented ≡ true

    mixedCornersSourcePaid : Bool
    mixedCornersSourcePaidIsTrue : mixedCornersSourcePaid ≡ true

    allFourCornersShareSameProteinSequence : Bool
    allFourCornersShareSameProteinSequenceIsFalse :
      allFourCornersShareSameProteinSequence ≡ false

    crossHomologSquareProvesSameSequenceAxisIndependence : Bool
    crossHomologSquareProvesSameSequenceAxisIndependenceIsFalse :
      crossHomologSquareProvesSameSequenceAxisIndependence ≡ false

    referenceSquareUsefulForCoordinateHypothesis : Bool
    referenceSquareUsefulForCoordinateHypothesisIsTrue :
      referenceSquareUsefulForCoordinateHypothesis ≡ true

    mixedStatesCanGuideSameCarrierAcquisition : Bool
    mixedStatesCanGuideSameCarrierAcquisitionIsTrue :
      mixedStatesCanGuideSameCarrierAcquisition ≡ true

    referenceSquareProvesUniversalMechanism : Bool
    referenceSquareProvesUniversalMechanismIsFalse :
      referenceSquareProvesUniversalMechanism ≡ false

    pdbStateLabelEqualsDynamicsPath : Bool
    pdbStateLabelEqualsDynamicsPathIsFalse : pdbStateLabelEqualsDynamicsPath ≡ false

canonicalMixedStateReferenceBoundary : MixedStateReferenceBoundary
canonicalMixedStateReferenceBoundary =
  mixed-state-reference-boundary
    true refl
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
