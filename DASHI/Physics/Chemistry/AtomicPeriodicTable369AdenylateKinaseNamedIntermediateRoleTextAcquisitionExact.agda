module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseNamedIntermediateRoleTextAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- NAMED INTERMEDIATE ROLE TEXT ACQUISITION
--
-- Machine-readable Li-Liu-Ji prose pays more than the coarse Figure-5 caption:
--   * gamma and delta are examples where LID is closed/contacting NMP while
--     NMP is open and semi-open, respectively;
--   * alpha/beta are used as the open-state side in the discussion of the
--     Henzler-Wildman FRET population;
--   * the alternative route alpha -> beta -> epsilon -> zeta is explicitly
--     described as NMP closing first and LID closing afterward.
--
-- These are qualitative state/route roles.  They do not pay exact theta1,
-- theta2 or dLN coordinates for beta/gamma/delta/epsilon, and they do not turn
-- source prose into a state-identity quotient.  DOI/PMID/PMCID/QID/UniProt are
-- retained only through the existing attribution envelope.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Attr.liLiuJiSource

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

articleDOI = Attr.articleDOI
articlePMID = Attr.articlePMID
articlePMCID = Attr.articlePMCID
articleQID = Attr.articleQID
adkQID = Attr.adkQID
adkUniProt = Attr.adkUniProt

data NamedIntermediateState : Set where
  alpha beta gamma delta epsilon zeta : NamedIntermediateState

data LidRole : Set where
  lidOpenLike lidClosedContactingNmp lidRoleNotFurtherResolved : LidRole

data NmpRole : Set where
  nmpOpen nmpSemiOpen nmpClosesBeforeLid nmpRoleNotFurtherResolved : NmpRole

data PopulationSide : Set where
  openLikeSide closedLikeSide populationSideNotAssigned : PopulationSide

record NamedStateRoleObservation : Set where
  constructor named-state-role-observation
  field
    state : NamedIntermediateState
    lidRole : LidRole
    nmpRole : NmpRole
    populationSide : PopulationSide
    sourceLocator : String
    sourceReading : String
    exactThetaOnePaid : Bool
    exactThetaTwoPaid : Bool
    exactDLnPaid : Bool
open NamedStateRoleObservation public

alphaRole : NamedStateRoleObservation
alphaRole = named-state-role-observation
  alpha lidOpenLike nmpOpen openLikeSide
  "Li-Liu-Ji 2015 ligand-free/FRET discussion and Figure-5 route context"
  "alpha is on the open-state side; no new alpha numeric coordinate is acquired here"
  false false false

betaRole : NamedStateRoleObservation
betaRole = named-state-role-observation
  beta lidRoleNotFurtherResolved nmpRoleNotFurtherResolved openLikeSide
  "Li-Liu-Ji 2015 FRET discussion: open state corresponding to alpha or beta"
  "beta is retained as an open-like population-role label only; exact beta geometry remains unpaid"
  false false false

gammaRole : NamedStateRoleObservation
gammaRole = named-state-role-observation
  gamma lidClosedContactingNmp nmpOpen closedLikeSide
  "Li-Liu-Ji 2015 ligand-free transition prose: gamma/delta configurations correspond to NMP open/semi-open after LID contact, respectively"
  "gamma: LID closed/contacting NMP while NMP remains open; qualitative role only"
  false false false

deltaRole : NamedStateRoleObservation
deltaRole = named-state-role-observation
  delta lidClosedContactingNmp nmpSemiOpen closedLikeSide
  "Li-Liu-Ji 2015 ligand-free transition prose: gamma/delta configurations correspond to NMP open/semi-open after LID contact, respectively"
  "delta: LID closed/contacting NMP while NMP is semi-open; qualitative role only"
  false false false

epsilonRole : NamedStateRoleObservation
epsilonRole = named-state-role-observation
  epsilon lidRoleNotFurtherResolved nmpClosesBeforeLid populationSideNotAssigned
  "Li-Liu-Ji 2015 alternative ligand-free route alpha->beta->epsilon->zeta"
  "epsilon is on the source-described NMP-first alternative route; exact epsilon geometry remains unpaid"
  false false false

zetaRole : NamedStateRoleObservation
zetaRole = named-state-role-observation
  zeta lidClosedContactingNmp nmpRoleNotFurtherResolved closedLikeSide
  "Li-Liu-Ji 2015 Figure-5 caption/prose closed terminal role"
  "zeta is the Figure-level closed-state role; equation-xi identity remains a separate role bridge"
  false false false

namedRoleObservations : List NamedStateRoleObservation
namedRoleObservations = alphaRole ∷ betaRole ∷ gammaRole ∷ deltaRole ∷ epsilonRole ∷ zetaRole ∷ []

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data QualitativeRoleCreatesExactCoordinate : Set where
data RoleDescriptionCreatesStateIdentity : Set where
data PopulationSideCreatesExactPopulationFraction : Set where
data CitationCreatesScientificAuthority : Set where

data AlternativeRouteRoleCreatesRateConstant : Set where

qualitativeRoleDoesNotCreateExactCoordinate : QualitativeRoleCreatesExactCoordinate → ⊥
qualitativeRoleDoesNotCreateExactCoordinate ()

roleDescriptionDoesNotCreateStateIdentity : RoleDescriptionCreatesStateIdentity → ⊥
roleDescriptionDoesNotCreateStateIdentity ()

populationSideDoesNotCreateFraction : PopulationSideCreatesExactPopulationFraction → ⊥
populationSideDoesNotCreateFraction ()

citationDoesNotCreateScientificAuthority : CitationCreatesScientificAuthority → ⊥
citationDoesNotCreateScientificAuthority ()

alternativeRouteRoleDoesNotCreateRate : AlternativeRouteRoleCreatesRateConstant → ⊥
alternativeRouteRoleDoesNotCreateRate ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record NamedIntermediateRoleTextAcquisitionBoundary : Set where
  constructor named-intermediate-role-text-acquisition-boundary
  field
    gammaNmpOpenRolePaid : Bool
    deltaNmpSemiOpenRolePaid : Bool
    gammaDeltaLidContactRolePaid : Bool
    betaOpenLikePopulationRolePaid : Bool
    epsilonNmpFirstAlternativeRolePaid : Bool
    namedIntermediateExactAnglesPaid : Bool
    namedIntermediateExactDLnPaid : Bool
    exactPopulationFractionsPaid : Bool
    routeRoleCreatesRateConstant : Bool
    roleDescriptionCreatesStateIdentity : Bool
    citationCreatesScientificAuthority : Bool
    doiPmidPmcidRetained : Bool
    articleQidMayRemainUnresolved : Bool
open NamedIntermediateRoleTextAcquisitionBoundary public

canonicalNamedIntermediateRoleTextAcquisitionBoundary :
  NamedIntermediateRoleTextAcquisitionBoundary
canonicalNamedIntermediateRoleTextAcquisitionBoundary =
  named-intermediate-role-text-acquisition-boundary
    true true true true true
    false false false false false false
    true true
