module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFreeEnergyTextAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseMetadynamicsUncertaintyExact as Uncertainty

------------------------------------------------------------------------
-- TEXT-LEVEL FREE-ENERGY ACQUISITION
--
-- This owner records only free-energy relations stated in machine-readable
-- article text.  It does not transcribe the small Figure-5/6 per-state labels.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source = Attr.liLiuJiSource

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

articleDOI : Identity.ExternalIdentityDemand
articleDOI = Attr.articleDOI
articlePMID : Identity.ExternalIdentityDemand
articlePMID = Attr.articlePMID
articlePMCID : Identity.ExternalIdentityDemand
articlePMCID = Attr.articlePMCID
articleQID : Identity.ExternalIdentityDemand
articleQID = Attr.articleQID
adkQID : Identity.ExternalIdentityDemand
adkQID = Attr.adkQID

record ApproxDeltaG : Set where
  constructor approx-delta-g
  field
    tenthsKcalMol : Nat
    approximate : Bool
    context : String
    sourceLocator : String
    referenceReading : String
open ApproxDeltaG public

ligandBoundOpenClosedDeltaG : ApproxDeltaG
ligandBoundOpenClosedDeltaG = approx-delta-g
  80 true
  "ligand-bound AdK; alpha_L open to zeta_L closed"
  "Li-Liu-Ji 2015, Metadynamics of the ligand-bound AdK"
  "source reports Delta G_O->C approximately 8.0 kcal/mol (13.5 kBT)"

record KTRange : Set where
  constructor kt-range
  field
    lowerKT : Nat
    upperKT : Nat
    context : String
    sourceLocator : String
    reading : String
open KTRange public

ligandFreeOpenClosedRange : KTRange
ligandFreeOpenClosedRange = kt-range
  1 2
  "ligand-free AdK open<->closed free-energy difference"
  "Li-Liu-Ji 2015 discussion following Figs. 5/6"
  "source describes the free-energy difference as only a few kcal/mol, in the range 1-2 kBT"

record LigandFreeQualitativeFreeEnergyOrdering : Set where
  constructor ligand-free-qualitative-free-energy-ordering
  field
    gammaIsReferenceMinimum : Bool
    alphaBetaGammaNearlySame : Bool
    relationReading : String
    sourceLocator : String
open LigandFreeQualitativeFreeEnergyOrdering public

ligandFreeQualitativeOrdering : LigandFreeQualitativeFreeEnergyOrdering
ligandFreeQualitativeOrdering = ligand-free-qualitative-free-energy-ordering
  true true
  "gamma is the declared reference minimum; article prose states alpha, beta and gamma fall in the energy valley and are nearly at the same free-energy level"
  "Figure 5 caption + ligand-free metadynamics prose"

record LigandBoundQualitativeFreeEnergyOrdering : Set where
  constructor ligand-bound-qualitative-free-energy-ordering
  field
    deltaLLowerThanZetaL : Bool
    closedFavouredOverall : Bool
    relationReading : String
    sourceLocator : String
open LigandBoundQualitativeFreeEnergyOrdering public

ligandBoundQualitativeOrdering : LigandBoundQualitativeFreeEnergyOrdering
ligandBoundQualitativeOrdering = ligand-bound-qualitative-free-energy-ordering
  true true
  "article text states delta_L is a bit lower in free energy than zeta_L while the ligand-bound landscape overall shifts toward closed conformations"
  "Metadynamics of the ligand-bound AdK"

freeEnergyUncertainty = Uncertainty.metadynamicsFreeEnergyUncertainty

------------------------------------------------------------------------
-- WrongType / precision firewalls.
------------------------------------------------------------------------

data NearlySameCreatesEqualNumerics : Set where
data QualitativeOrderingCreatesMissingFigureLabels : Set where
data ApproxEightBecomesExactPhysicalConstant : Set where
data OneToTwoKTBecomesExactKcalValue : Set where
data QidCreatesFreeEnergyPayment : Set where

nearlySameDoesNotCreateEqualNumerics : NearlySameCreatesEqualNumerics → ⊥
nearlySameDoesNotCreateEqualNumerics ()

qualitativeOrderingDoesNotCreateFigureLabels : QualitativeOrderingCreatesMissingFigureLabels → ⊥
qualitativeOrderingDoesNotCreateFigureLabels ()

approxEightDoesNotBecomeExactPhysicalConstant : ApproxEightBecomesExactPhysicalConstant → ⊥
approxEightDoesNotBecomeExactPhysicalConstant ()

ktRangeDoesNotBecomeExactKcalValue : OneToTwoKTBecomesExactKcalValue → ⊥
ktRangeDoesNotBecomeExactKcalValue ()

qidDoesNotPayFreeEnergy : QidCreatesFreeEnergyPayment → ⊥
qidDoesNotPayFreeEnergy ()

record AdKFreeEnergyTextAcquisitionBoundary : Set where
  constructor adk-free-energy-text-acquisition-boundary
  field
    gammaReferenceMinimumPaid : Bool
    alphaBetaGammaNearSameLevelPaid : Bool
    ligandBoundDeltaLLowerThanZetaLPaid : Bool
    ligandBoundOpenClosedApproxEightKcalMolPaid : Bool
    ligandFreeOpenClosedOneToTwoKTPaid : Bool
    metadynamicsUncertaintyRetained : Bool
    perStateFigureFiveNumericLabelsPaid : Bool
    perEdgeKramersNumericsPaid : Bool
    qualitativeNearSamePromotedToEquality : Bool
    articleQidCreatesNumericAuthority : Bool
open AdKFreeEnergyTextAcquisitionBoundary public

canonicalAdKFreeEnergyTextAcquisitionBoundary : AdKFreeEnergyTextAcquisitionBoundary
canonicalAdKFreeEnergyTextAcquisitionBoundary = adk-free-energy-text-acquisition-boundary
  true true true true true true
  false false false false
