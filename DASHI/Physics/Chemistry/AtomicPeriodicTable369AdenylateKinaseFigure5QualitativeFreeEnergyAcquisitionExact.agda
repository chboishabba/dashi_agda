module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFigure5QualitativeFreeEnergyAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr

------------------------------------------------------------------------
-- FIGURE-5 MACHINE-READABLE QUALITATIVE FREE-ENERGY ACQUISITION
--
-- Li, Liu & Ji 2015 pay several free-energy relations in article text/caption
-- without requiring visual transcription of the tiny labels in Figure 5c:
--
--   * gamma is the minimum-free-energy reference state for the apo Figure-5
--     landscape;
--   * alpha -> beta -> gamma follows an energy valley and alpha, beta, gamma
--     are described as nearly at the same free-energy level;
--   * the red route is the most favorable path, while dashed black routes are
--     possible alternatives.
--
-- This owner retains those source-paid *qualitative* relations only.  It does
-- not infer per-state Delta-G numerals, pairwise equality, error bars, or edge
-- rates.  The source article owns the reported AdK observations; DASHI owns the
-- typed acquisition boundary and promotion firewalls below.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Attr.liLiuJiSource

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

data ApoFigure5State : Set where
  alpha beta gamma delta epsilon zeta eta lambda : ApoFigure5State

data QualitativeEnergyRelation : Set where
  minimumReference : QualitativeEnergyRelation
  nearlySameLevel : QualitativeEnergyRelation
  favorableRoute : QualitativeEnergyRelation
  possibleAlternativeRoute : QualitativeEnergyRelation

record Figure5QualitativePayment : Set where
  constructor figure5-qualitative-payment
  field
    relation : QualitativeEnergyRelation
    states : String
    sourceLocator : String
    interpretation : String
    numericDeltaGPaid : Bool
open Figure5QualitativePayment public

gammaReferencePayment : Figure5QualitativePayment
gammaReferencePayment = figure5-qualitative-payment
  minimumReference
  "gamma"
  "Li-Liu-Ji 2015 Figure 5 caption: state with the minimum free energy was set as the reference state, gamma"
  "gamma is the source-defined zero/reference state for the apo Figure-5 relative free-energy landscape; this is not an absolute thermodynamic zero"
  false

alphaBetaGammaPlateauPayment : Figure5QualitativePayment
alphaBetaGammaPlateauPayment = figure5-qualitative-payment
  nearlySameLevel
  "alpha, beta, gamma"
  "Li-Liu-Ji 2015 apo metadynamics prose immediately after Figure 5: alpha-beta-gamma fall in an energy valley and are nearly at the same free-energy level"
  "source-paid qualitative near-level relation only; it does not assert exact equality or supply alpha/beta/gamma numerical Delta-G differences"
  false

mostFavorableRoutePayment : Figure5QualitativePayment
mostFavorableRoutePayment = figure5-qualitative-payment
  favorableRoute
  "Figure-5 red route"
  "Li-Liu-Ji 2015 Figure 5 caption: red line indicates the most favorable path"
  "source role is a reported most-favorable route on the computed apo free-energy landscape, not an experimentally measured kinetic pathway"
  false

alternativeRoutesPayment : Figure5QualitativePayment
alternativeRoutesPayment = figure5-qualitative-payment
  possibleAlternativeRoute
  "Figure-5 dashed black routes"
  "Li-Liu-Ji 2015 Figure 5 caption: dashed black lines are possible alternative pathways"
  "source-paid alternative-route role; no exact route probability or per-edge rate is created"
  false

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data NearlySameMeansEqualFreeEnergy : Set where
data QualitativeRelationCreatesNumericCalibration : Set where
data FavorableRouteCreatesExperimentalKinetics : Set where
data GammaReferenceCreatesAbsoluteThermodynamicZero : Set where
data DOIorQIDCreatesEnergyRelation : Set where

nearlySameDoesNotMeanExactEquality : NearlySameMeansEqualFreeEnergy → ⊥
nearlySameDoesNotMeanExactEquality ()

qualitativeRelationDoesNotCreateNumericCalibration :
  QualitativeRelationCreatesNumericCalibration → ⊥
qualitativeRelationDoesNotCreateNumericCalibration ()

favorableRouteDoesNotCreateExperimentalKinetics :
  FavorableRouteCreatesExperimentalKinetics → ⊥
favorableRouteDoesNotCreateExperimentalKinetics ()

gammaReferenceDoesNotCreateAbsoluteZero :
  GammaReferenceCreatesAbsoluteThermodynamicZero → ⊥
gammaReferenceDoesNotCreateAbsoluteZero ()

identityMetadataDoesNotCreateEnergyRelation : DOIorQIDCreatesEnergyRelation → ⊥
identityMetadataDoesNotCreateEnergyRelation ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record Figure5QualitativeFreeEnergyBoundary : Set where
  constructor figure5-qualitative-free-energy-boundary
  field
    gammaReferenceStatePaid : Bool
    alphaBetaGammaNearlySameFreeEnergyPaid : Bool
    mostFavorableRouteRolePaid : Bool
    alternativeRouteRolePaid : Bool
    exactAlphaBetaGammaFreeEnergyDifferencesPaid : Bool
    nearlySameMeansExactEquality : Bool
    qualitativeRelationCreatesNumericCalibration : Bool
    favorableRouteCreatesExperimentalKinetics : Bool
    gammaReferenceCreatesAbsoluteThermodynamicZero : Bool
    DOIorQIDCreatesEnergyRelation : Bool
    attributionEnvelopeReused : Bool
    nextResidual : String
open Figure5QualitativeFreeEnergyBoundary public

canonicalFigure5QualitativeFreeEnergyBoundary : Figure5QualitativeFreeEnergyBoundary
canonicalFigure5QualitativeFreeEnergyBoundary = figure5-qualitative-free-energy-boundary
  true true true true
  false false false false false false true
  "retain gamma as the relative-energy reference and alpha/beta/gamma as a source-paid qualitative near-level energy valley. Do not upgrade missing Figure-5 per-state Delta-G numerals or Kramers arrow labels without an exact same-object locator-specific numeric receipt."
