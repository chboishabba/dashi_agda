module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePartialStateCoordinateAlignmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact as Graph

------------------------------------------------------------------------
-- PARTIAL ALIGNMENT OF NAMED LANDSCAPE STATES TO SOURCE-PAID COORDINATE REGIONS
--
-- Li, Liu & Ji 2015 (DOI 10.1016/j.bpj.2015.06.059) use theta1=LID--CORE
-- angle and theta2=NMP--CORE angle for the Figure-5 ligand-free free-energy
-- landscape.  The caption identifies alpha with the open crystal structure and
-- zeta with the closed crystal structure; beta/gamma/delta/epsilon are
-- semi-open--semi-closed intermediates; eta/lambda are nearer closed.
--
-- The study also defines dLN as a third collective variable, but the inspected
-- Figure-5 text does not pay a per-named-state dLN value.  This owner therefore
-- encodes only a partial three-CV alignment.  Endpoint two-angle points are
-- obtained by composing the source-paid alpha/open and zeta/closed identities
-- with the already-owned open/closed angle endpoints.  That composition is a
-- DASHI theorem, not a quotation or authorship transfer to the source.
------------------------------------------------------------------------

data FigureLandscapeStateLabel : Set where
  alphaFigure betaFigure gammaFigure deltaFigure epsilonFigure : FigureLandscapeStateLabel
  zetaFigure etaFigure lambdaFigure : FigureLandscapeStateLabel

data TwoAngleRegionClass : Set where
  openCrystalRegion : TwoAngleRegionClass
  closedCrystalRegion : TwoAngleRegionClass
  semiOpenSemiClosedRegion : TwoAngleRegionClass
  nearClosedRegion : TwoAngleRegionClass

data ExactTwoAnglePoint : Set where
  noExactTwoAnglePoint : ExactTwoAnglePoint
  exactTwoAnglePoint : Nat → Nat → ExactTwoAnglePoint

data DLnAlignmentStatus : Set where
  dLnUnresolvedForNamedState : DLnAlignmentStatus

record PartialThreeCvRegion : Set where
  constructor partial-three-cv-region
  field
    label : FigureLandscapeStateLabel
    twoAngleRegion : TwoAngleRegionClass
    exactTwoAnglePoint : ExactTwoAnglePoint
    dLnStatus : DLnAlignmentStatus
open PartialThreeCvRegion public

figureStateRegion : FigureLandscapeStateLabel → PartialThreeCvRegion
figureStateRegion alphaFigure =
  partial-three-cv-region
    alphaFigure
    openCrystalRegion
    (exactTwoAnglePoint
      (Graph.TwoAngleFreeEnergyReceipt.lidCoreOpenDegrees Graph.canonicalFreeEnergyReceipt)
      (Graph.TwoAngleFreeEnergyReceipt.nmpCoreOpenDegrees Graph.canonicalFreeEnergyReceipt))
    dLnUnresolvedForNamedState
figureStateRegion betaFigure =
  partial-three-cv-region betaFigure semiOpenSemiClosedRegion noExactTwoAnglePoint dLnUnresolvedForNamedState
figureStateRegion gammaFigure =
  partial-three-cv-region gammaFigure semiOpenSemiClosedRegion noExactTwoAnglePoint dLnUnresolvedForNamedState
figureStateRegion deltaFigure =
  partial-three-cv-region deltaFigure semiOpenSemiClosedRegion noExactTwoAnglePoint dLnUnresolvedForNamedState
figureStateRegion epsilonFigure =
  partial-three-cv-region epsilonFigure semiOpenSemiClosedRegion noExactTwoAnglePoint dLnUnresolvedForNamedState
figureStateRegion zetaFigure =
  partial-three-cv-region
    zetaFigure
    closedCrystalRegion
    (exactTwoAnglePoint
      (Graph.TwoAngleFreeEnergyReceipt.lidCoreClosedDegrees Graph.canonicalFreeEnergyReceipt)
      (Graph.TwoAngleFreeEnergyReceipt.nmpCoreClosedDegrees Graph.canonicalFreeEnergyReceipt))
    dLnUnresolvedForNamedState
figureStateRegion etaFigure =
  partial-three-cv-region etaFigure nearClosedRegion noExactTwoAnglePoint dLnUnresolvedForNamedState
figureStateRegion lambdaFigure =
  partial-three-cv-region lambdaFigure nearClosedRegion noExactTwoAnglePoint dLnUnresolvedForNamedState

------------------------------------------------------------------------
-- Partial bridge from equation-level graph states to Figure-5 state labels.
--
-- alpha/beta/gamma/delta/epsilon have direct same-label support.  The existing
-- graph deliberately stores xi as an equation-level target while the figure
-- caption uses zeta for the closed crystal state.  We therefore do not create
-- xi -> zeta by fiat.
------------------------------------------------------------------------

data GraphStateAlignedToFigureLabel :
  Graph.AdKLandscapeState → FigureLandscapeStateLabel → Set where
  alphaAligned : GraphStateAlignedToFigureLabel Graph.alpha alphaFigure
  betaAligned : GraphStateAlignedToFigureLabel Graph.beta betaFigure
  gammaAligned : GraphStateAlignedToFigureLabel Graph.gamma gammaFigure
  deltaAligned : GraphStateAlignedToFigureLabel Graph.delta deltaFigure
  epsilonAligned : GraphStateAlignedToFigureLabel Graph.epsilon epsilonFigure

xiHasNoPaidFigureAlignment :
  (Σ FigureLandscapeStateLabel
    (λ label → GraphStateAlignedToFigureLabel Graph.xiEquationTarget label)) → ⊥
xiHasNoPaidFigureAlignment (label , ())

alignedGraphRegion :
  ∀ {state label} →
  GraphStateAlignedToFigureLabel state label →
  PartialThreeCvRegion
alignedGraphRegion {label = alphaFigure} alphaAligned = figureStateRegion alphaFigure
alignedGraphRegion {label = betaFigure} betaAligned = figureStateRegion betaFigure
alignedGraphRegion {label = gammaFigure} gammaAligned = figureStateRegion gammaFigure
alignedGraphRegion {label = deltaFigure} deltaAligned = figureStateRegion deltaFigure
alignedGraphRegion {label = epsilonFigure} epsilonAligned = figureStateRegion epsilonFigure

------------------------------------------------------------------------
-- Concrete endpoint deductions.  These are compositions of two separately
-- source-paid facts: named-state crystal identity and open/closed angle values.
------------------------------------------------------------------------

alphaComposedEndpoint :
  ExactTwoAnglePoint
alphaComposedEndpoint = exactTwoAnglePoint 95 61

zetaComposedEndpoint :
  ExactTwoAnglePoint
zetaComposedEndpoint = exactTwoAnglePoint 68 28

alphaEndpointAgreement :
  exactTwoAnglePoint (Graph.TwoAngleFreeEnergyReceipt.lidCoreOpenDegrees Graph.canonicalFreeEnergyReceipt)
                     (Graph.TwoAngleFreeEnergyReceipt.nmpCoreOpenDegrees Graph.canonicalFreeEnergyReceipt)
  ≡ alphaComposedEndpoint
alphaEndpointAgreement = refl

zetaEndpointAgreement :
  exactTwoAnglePoint (Graph.TwoAngleFreeEnergyReceipt.lidCoreClosedDegrees Graph.canonicalFreeEnergyReceipt)
                     (Graph.TwoAngleFreeEnergyReceipt.nmpCoreClosedDegrees Graph.canonicalFreeEnergyReceipt)
  ≡ zetaComposedEndpoint
zetaEndpointAgreement = refl

------------------------------------------------------------------------
-- Attribution/snowball coordinate.
------------------------------------------------------------------------

record PartialAlignmentSourceCoordinate : Set where
  constructor partial-alignment-source-coordinate
  field
    label : String
    doi : String
    pmid : String
    pmcid : String
    qid : String
    pdb : String
    uniprot : String
    dewey : String
    directLink : String
    oeis : String
    sourceRole : String
    dashiRole : String

liLiuJi2015PartialAlignmentSource : PartialAlignmentSourceCoordinate
liLiuJi2015PartialAlignmentSource =
  partial-alignment-source-coordinate
    "Li, Liu and Ji 2015 named-state / two-angle landscape alignment"
    "10.1016/j.bpj.2015.06.059"
    "26244746"
    "PMC4572606"
    "source-article QID unresolved in inspected sources; adenylate kinase Q356240"
    "alpha=open 4AKE structural endpoint; zeta=closed 1AKE structural endpoint"
    "P69441"
    "exact article-level Dewey unresolved"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC4572606/"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "pays Figure-5 named-state classes on the theta1/theta2 landscape and the alpha/open, zeta/closed crystal identities; dLN is defined in the study but no per-named-state dLN assignment is paid by the inspected caption"
    "DASHI composes named endpoint identity with separately owned open/closed angle coordinates and retains partiality where the source is silent"

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKPartialStateCoordinateAlignmentBoundary : Set where
  constructor adk-partial-state-coordinate-alignment-boundary
  field
    alphaOpenEndpointComposed : Bool
    zetaClosedEndpointComposed : Bool
    intermediateLabelsRetainQualitativeRegion : Bool
    nearClosedLabelsRetainQualitativeRegion : Bool
    xiToFigureLabelAlignmentPaid : Bool
    namedStateDLnAssignmentsPaid : Bool
    partialAlignmentEqualsTotalThreeCvLookup : Bool
    graphStateSilentlyEqualsFigureState : Bool
    qualitativeRegionEqualsExactNumericPoint : Bool
    sourceOwnsDashiCompositionTheorem : Bool
    citationCreatesProofAuthority : Bool

canonicalAdKPartialStateCoordinateAlignmentBoundary :
  AdKPartialStateCoordinateAlignmentBoundary
canonicalAdKPartialStateCoordinateAlignmentBoundary =
  adk-partial-state-coordinate-alignment-boundary
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    false
