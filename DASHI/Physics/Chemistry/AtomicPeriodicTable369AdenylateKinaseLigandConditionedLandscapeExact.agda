module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseLigandConditionedLandscapeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseWeightedNDimStateGraphExact as Weighted
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseCouplingResidualExact as Coupling

------------------------------------------------------------------------
-- LIGAND-CONDITIONED ADENYLATE-KINASE NDIM LANDSCAPE
--
-- Li, Liu & Ji 2015 use the same LID--CORE and NMP--CORE collective-variable
-- axes for ligand-free and ligand-bound AdK, but report materially different
-- free-energy landscapes.  For the bound system the closed state is favoured,
-- the open->closed free-energy difference is about 8.0 kcal/mol, and the region
-- corresponding to NMP-closing first (LID still open, NMP closed) is strongly
-- unfavourable.  Therefore the graph/weight object is indexed by environment;
-- the ligand-free ~5.7:1 path-flux receipt is not silently transferred.
------------------------------------------------------------------------

data AdKLandscapeContext : Set where
  ligandFree : AdKLandscapeContext
  ligandBoundATPAMP : AdKLandscapeContext

record LigandBoundLandscapeReceipt : Set where
  constructor ligand-bound-landscape-receipt
  field
    context : AdKLandscapeContext
    boundOpenToClosedDeltaGTenthsKcal : Nat
    boundClosedStateFavoured : Bool
    nmpFirstRegionStronglyUnfavourable : Bool
    lidCoreAxisRetained : Bool
    nmpCoreAxisRetained : Bool
    sourceSummary : String
open LigandBoundLandscapeReceipt public

canonicalLigandBoundLandscape : LigandBoundLandscapeReceipt
canonicalLigandBoundLandscape =
  ligand-bound-landscape-receipt
    ligandBoundATPAMP
    80
    true
    true
    true
    true
    "Li-Liu-Ji 2015: ligand-bound open->closed delta G approx 8.0 kcal/mol; NMP-first/LID-open region strongly unfavourable"

------------------------------------------------------------------------
-- Existing ligand-free graph/coupling donors remain context-specific.
------------------------------------------------------------------------

ligandFreeWeightedGraphDonor : Weighted.AdKWeightedGraphBoundary
ligandFreeWeightedGraphDonor = Weighted.canonicalAdKWeightedGraphBoundary

ligandFreeCouplingDonor : Coupling.AdKCouplingBoundary
ligandFreeCouplingDonor = Coupling.canonicalAdKCouplingBoundary

------------------------------------------------------------------------
-- Snowball attribution.
------------------------------------------------------------------------

record LigandConditionedSourceCoordinate : Set where
  constructor ligand-conditioned-source-coordinate
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

liLiuJi2015LigandConditionedLandscape : LigandConditionedSourceCoordinate
liLiuJi2015LigandConditionedLandscape =
  ligand-conditioned-source-coordinate
    "Li, Liu and Ji 2015 ligand-conditioned AdK free-energy landscapes"
    "10.1016/j.bpj.2015.06.059"
    "26244746"
    "PMC4572606"
    "source-article QID unresolved in inspected sources; adenylate kinase Q356240"
    "4AKE open and 1AKE closed reference endpoints"
    "P69441"
    "exact article-level Dewey unresolved"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC4572606/"
    "not an integer-sequence object; no same-object OEIS coordinate"
    "pays same-CV ligand-free/bound comparison, approx 8.0 kcal/mol bound open-to-closed delta G, bound closed-state preference, and strongly unfavourable NMP-first region"

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record AdKLigandConditionedBoundary : Set where
  constructor adk-ligand-conditioned-boundary
  field
    sameGeometricAxesRetainedAcrossContexts : Bool
    sameGeometricAxesRetainedAcrossContextsIsTrue :
      sameGeometricAxesRetainedAcrossContexts ≡ true

    ligandChangesFreeEnergyLandscape : Bool
    ligandChangesFreeEnergyLandscapeIsTrue :
      ligandChangesFreeEnergyLandscape ≡ true

    boundClosedStateEnergeticallyFavoured : Bool
    boundClosedStateEnergeticallyFavouredIsTrue :
      boundClosedStateEnergeticallyFavoured ≡ true

    boundOpenToClosedDeltaGSourcePaid : Bool
    boundOpenToClosedDeltaGSourcePaidIsTrue :
      boundOpenToClosedDeltaGSourcePaid ≡ true

    boundNmpFirstRegionStronglyUnfavourable : Bool
    boundNmpFirstRegionStronglyUnfavourableIsTrue :
      boundNmpFirstRegionStronglyUnfavourable ≡ true

    freePathFluxRatioTransfersToBoundContext : Bool
    freePathFluxRatioTransfersToBoundContextIsFalse :
      freePathFluxRatioTransfersToBoundContext ≡ false

    deltaGDeterminesFullKinetics : Bool
    deltaGDeterminesFullKineticsIsFalse : deltaGDeterminesFullKinetics ≡ false

    sameAxesImplySameLandscape : Bool
    sameAxesImplySameLandscapeIsFalse : sameAxesImplySameLandscape ≡ false

    computationalLandscapeEqualsExperimentalPopulation : Bool
    computationalLandscapeEqualsExperimentalPopulationIsFalse :
      computationalLandscapeEqualsExperimentalPopulation ≡ false

    ligandConditionCreatesUniversalMechanism : Bool
    ligandConditionCreatesUniversalMechanismIsFalse :
      ligandConditionCreatesUniversalMechanism ≡ false

canonicalAdKLigandConditionedBoundary : AdKLigandConditionedBoundary
canonicalAdKLigandConditionedBoundary =
  adk-ligand-conditioned-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
