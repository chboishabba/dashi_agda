module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseBarrierRegimeTextAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCalibrationAttributionEnvelopeExact as Attr
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseFreeEnergyTextAcquisitionExact as FreeEnergy

------------------------------------------------------------------------
-- CONTEXT-INDEXED BARRIER-REGIME TEXT ACQUISITION
--
-- Li, Liu & Ji 2015 state in machine-readable article text that ligand-free AdK
-- has no significant free-energy barrier separating open and closed states and
-- instead has multiple intermediate states, whereas ligand-bound AdK favours
-- the closed conformation and has a large free-energy barrier to opening.
--
-- This owner records those qualitative barrier-regime roles only.  It does not
-- manufacture a numerical barrier height, transition-state energy, experimental
-- activation rate, or universal mechanism.  The source owns the AdK-specific
-- statements; DASHI owns this typed acquisition boundary and its firewalls.
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
adkUniProt : Identity.ExternalIdentityDemand
adkUniProt = Attr.adkUniProt

data LigandContext : Set where
  ligandFree : LigandContext
  ligandBound : LigandContext

data BarrierRegime : Set where
  noSignificantOpenClosedBarrier : BarrierRegime
  largeOpeningBarrier : BarrierRegime

data LandscapeRole : Set where
  multipleIntermediateStates : LandscapeRole
  closedEnergeticallyFavoured : LandscapeRole

record BarrierRegimePayment : Set where
  constructor barrier-regime-payment
  field
    context : LigandContext
    regime : BarrierRegime
    sourceLocator : String
    interpretation : String
    numericBarrierHeightPaid : Bool
open BarrierRegimePayment public

apoBarrierPayment : BarrierRegimePayment
apoBarrierPayment = barrier-regime-payment
  ligandFree
  noSignificantOpenClosedBarrier
  "Li-Liu-Ji 2015 abstract: ligand-free AdK has no significant energy barrier separating open and closed states"
  "source-paid qualitative apo barrier regime; not a zero barrier and not a numerical activation-energy measurement"
  false

boundBarrierPayment : BarrierRegimePayment
boundBarrierPayment = barrier-regime-payment
  ligandBound
  largeOpeningBarrier
  "Li-Liu-Ji 2015 abstract: ligand-bound AdK closed conformation is energetically most favored with a large energy barrier to open it up"
  "source-paid qualitative ligand-bound opening-barrier regime; no numerical barrier height is inferred"
  false

record LandscapeRolePayment : Set where
  constructor landscape-role-payment
  field
    context : LigandContext
    role : LandscapeRole
    sourceLocator : String
    interpretation : String
open LandscapeRolePayment public

apoIntermediatePayment : LandscapeRolePayment
apoIntermediatePayment = landscape-role-payment
  ligandFree
  multipleIntermediateStates
  "Li-Liu-Ji 2015 abstract: multiple intermediate conformational states facilitate rapid transitions in ligand-free AdK"
  "source-paid existence/role of multiple apo intermediates; not a complete state census or per-state kinetic table"

boundClosedFavouredPayment : LandscapeRolePayment
boundClosedFavouredPayment = landscape-role-payment
  ligandBound
  closedEnergeticallyFavoured
  "Li-Liu-Ji 2015 abstract and ligand-bound metadynamics discussion"
  "source-paid ligand-bound energetic preference for closed conformations; distinct from an experimental equilibrium constant"

-- Reuse the separately paid text-level free-energy coordinates rather than
-- turning the qualitative barrier statements into numerical values.
ligandFreeOpenClosedRange = FreeEnergy.ligandFreeOpenClosedRange
ligandBoundOpenClosedDeltaG = FreeEnergy.ligandBoundOpenClosedDeltaG

------------------------------------------------------------------------
-- WrongType / promotion firewalls.
------------------------------------------------------------------------

data NoSignificantBarrierMeansZeroBarrier : Set where
data LargeBarrierCreatesNumericBarrierHeight : Set where
data BarrierRegimeIsExperimentalKinetics : Set where
data IntermediateStatesCreateCompleteMechanism : Set where
data ClosedFavouredCreatesExperimentalPopulation : Set where
data IdentityMetadataCreatesBarrierPayment : Set where

noSignificantDoesNotMeanZero : NoSignificantBarrierMeansZeroBarrier → ⊥
noSignificantDoesNotMeanZero ()

largeBarrierDoesNotCreateNumericHeight : LargeBarrierCreatesNumericBarrierHeight → ⊥
largeBarrierDoesNotCreateNumericHeight ()

barrierRegimeDoesNotBecomeExperimentalKinetics : BarrierRegimeIsExperimentalKinetics → ⊥
barrierRegimeDoesNotBecomeExperimentalKinetics ()

intermediatesDoNotCreateCompleteMechanism : IntermediateStatesCreateCompleteMechanism → ⊥
intermediatesDoNotCreateCompleteMechanism ()

closedFavouredDoesNotCreateExperimentalPopulation : ClosedFavouredCreatesExperimentalPopulation → ⊥
closedFavouredDoesNotCreateExperimentalPopulation ()

identityDoesNotCreateBarrierPayment : IdentityMetadataCreatesBarrierPayment → ⊥
identityDoesNotCreateBarrierPayment ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record AdKBarrierRegimeTextAcquisitionBoundary : Set where
  constructor adk-barrier-regime-text-acquisition-boundary
  field
    apoNoSignificantOpenClosedBarrierPaid : Bool
    apoMultipleIntermediateStatesPaid : Bool
    boundClosedEnergeticallyFavouredPaid : Bool
    boundLargeOpeningBarrierPaid : Bool
    numericBarrierHeightPaid : Bool
    noSignificantBarrierMeansZero : Bool
    barrierRegimeEqualsExperimentalKinetics : Bool
    multipleIntermediatesCreateCompleteMechanism : Bool
    closedFavouredCreatesExperimentalPopulation : Bool
    identityMetadataCreatesBarrierPayment : Bool
    attributionEnvelopeReused : Bool
    nextResidual : String
open AdKBarrierRegimeTextAcquisitionBoundary public

canonicalBarrierRegimeTextAcquisitionBoundary : AdKBarrierRegimeTextAcquisitionBoundary
canonicalBarrierRegimeTextAcquisitionBoundary = adk-barrier-regime-text-acquisition-boundary
  true true true true
  false false false false false false true
  "retain apo and ligand-bound barrier regimes as source-paid qualitative context coordinates. Numerical barrier heights require their own exact source locator; do not derive them from the 1-2 kBT apo state difference, the ~8.0 kcal/mol bound open-to-closed difference, or Kramers edge rates."
