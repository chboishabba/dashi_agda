module DASHI.Wikimedia.IbrahimOracleCrossDomainFibreCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimFirstLinkHistoricalDiscriminatorParetoExact as Ibrahim
import DASHI.Wikimedia.IbrahimSnowballEcologyEcosystemBiogeochemistryLESExact as LES
import DASHI.Chemistry.SaltPetroleumIndustrialChemistryNetworkExact as Petrochem
import DASHI.Planning.ChemicalManufacturingInventoryLogisticsCrossPollinationExact as Logistics
import DASHI.Papers.NavierStokes.TheoremInterface as NS
import DASHI.Papers.YangMills.TheoremInterface as YM
import DASHI.Music.MusicalSymmetryDynamicsCore as Music
import DASHI.Governance.PhenomenonEvidenceFibreOverTimeExact as Temporal

------------------------------------------------------------------------
-- IBRAHIM ORACLE -> EXISTING DASHI DOMAIN FIBRES
--
-- The four paper-owned historical first-link examples are used as traversal
-- seeds only.  They do not acquire new scientific authority by being routed
-- into LES, petrochemistry/logistics, NS/YM, or music.  Cross-pollination is a
-- typed relation between already-owned formulation fibres.
--
-- Historical edge identity, current QID/DDC identity, domain formulation,
-- empirical mechanism and theorem status remain separate coordinates.
------------------------------------------------------------------------

data OracleSeed : Set where
  bananaFruitSeed
  trainRailSeed
  physicsNaturalScienceSeed
  bobDylanSongSeed : OracleSeed

data DomainFibre : Set where
  lesPlantOutputFibre
  petrochemicalLogisticsFibre
  navierStokesPhysicsFibre
  yangMillsPhysicsFibre
  musicObjectFibre
  musicSymmetryDynamicsFibre
  physicsMusicSharedStructureFibre : DomainFibre

record CrossPollinationReceipt : Set where
  constructor cross-pollination-receipt
  field
    seed : OracleSeed
    ibrahimEdge : String
    childQid : String
    parentQid : String
    childDewey : String
    parentDewey : String
    source : String
    sourceLink : String
    targetFibre : DomainFibre
    existingOwner : String
    admittedReading : String
    survivingResidual : String
    sourceBoundaryRetained : Bool
    sameObjectRequiredForEmpiricalPromotion : Bool
    historicalEdgeCreatesDomainMechanism : Bool
    crossPollinationCreatesTheorem : Bool
open CrossPollinationReceipt public

------------------------------------------------------------------------
-- Banana -> fruit -> LES.
--
-- Fruit is used as a plant-output consumer coordinate: reproductive/harvest
-- output can consume plant carbon allocation, water state and nutrient state.
-- This does not identify a particular fruit crop, site, cultivar, treatment,
-- yield response, or LES mechanism.
------------------------------------------------------------------------

bananaFruitLES : CrossPollinationReceipt
bananaFruitLES = cross-pollination-receipt
  bananaFruitSeed
  "Banana -> fruit"
  "Q503"
  "Q1364"
  "unresolved"
  "unresolved"
  "Ibrahim, Danforth, Dodds 2017, Connecting every bit of knowledge: The structure of Wikipedia's First Link Network, DOI 10.1016/j.jocs.2016.12.001"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  lesPlantOutputFibre
  "DASHI.Wikimedia.IbrahimSnowballEcologyEcosystemBiogeochemistryLESExact; DASHI.Environment.SoilPlantAtmosphereContinuumExact"
  "fruit is admitted only as a possible plant-output consumer downstream of explicit plant carbon allocation, hydraulic/water and biogeochemical state fibres"
  "bind a concrete fruit/crop observation to exact site, time, plant state, carbon allocation, water balance, nutrient state and measured output before any causal or yield claim"
  true true false false

------------------------------------------------------------------------
-- Train -> rail transport -> petrochemistry/logistics.
--
-- Rail is a transport/network carrier.  The petrochemical lane already keeps
-- feedstock identity, transformation, inventory and logistics distinct.  Rail
-- can therefore carry feedstocks/products as a logistics edge without becoming
-- a chemistry mechanism or implying that every rail movement is petrochemical.
------------------------------------------------------------------------

trainRailPetrochemicalLogistics : CrossPollinationReceipt
trainRailPetrochemicalLogistics = cross-pollination-receipt
  trainRailSeed
  "Train -> rail transport"
  "Q870"
  "Q3565868"
  "unresolved"
  "unresolved"
  "Ibrahim, Danforth, Dodds 2017, Connecting every bit of knowledge: The structure of Wikipedia's First Link Network, DOI 10.1016/j.jocs.2016.12.001"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  petrochemicalLogisticsFibre
  "DASHI.Chemistry.SaltPetroleumIndustrialChemistryNetworkExact; DASHI.Planning.ChemicalManufacturingInventoryLogisticsCrossPollinationExact"
  "rail transport is admitted as one possible capacity/congestion/inventory movement carrier for identified petroleum/petrochemical feedstocks or products"
  "same-object shipment identity, material identity, origin/destination, quantity, time, capacity and custody remain required for any concrete petrochemical logistics claim"
  true true false false

------------------------------------------------------------------------
-- Physics -> natural science -> NS/YM.
--
-- The Ibrahim edge is navigation evidence.  The mathematical content remains
-- owned by the canonical NS/YM theorem interfaces and their promotion
-- boundaries.
------------------------------------------------------------------------

physicsToNS : CrossPollinationReceipt
physicsToNS = cross-pollination-receipt
  physicsNaturalScienceSeed
  "Physics -> natural science"
  "Q413"
  "Q7991"
  "530"
  "500"
  "Ibrahim, Danforth, Dodds 2017, Connecting every bit of knowledge: The structure of Wikipedia's First Link Network, DOI 10.1016/j.jocs.2016.12.001"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  navierStokesPhysicsFibre
  "DASHI.Papers.NavierStokes.TheoremInterface"
  "the physics navigation seed is routed to the existing Navier-Stokes formulation/theorem fibre; no first-link fact participates in the PDE proof"
  "retain the live NS proof frontier and its own analytical/physical receipts; Ibrahim contributes discoverability only"
  true true false false

physicsToYM : CrossPollinationReceipt
physicsToYM = cross-pollination-receipt
  physicsNaturalScienceSeed
  "Physics -> natural science"
  "Q413"
  "Q7991"
  "530"
  "500"
  "Ibrahim, Danforth, Dodds 2017, Connecting every bit of knowledge: The structure of Wikipedia's First Link Network, DOI 10.1016/j.jocs.2016.12.001"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  yangMillsPhysicsFibre
  "DASHI.Papers.YangMills.TheoremInterface"
  "the physics navigation seed is routed to the existing Yang-Mills formulation/theorem fibre; QID/DDC/first-link coordinates carry no mass-gap or continuum authority"
  "retain the live YM continuum/clustering/spectrum frontier and its own theorem receipts"
  true true false false

------------------------------------------------------------------------
-- Bob Dylan -> Blowin' in the Wind -> music.
--
-- The paper-owned edge gives a historical song-object navigation witness.  It
-- does not establish any symmetry, attractor, cognition, authorship or musical
-- analysis result.  Those require their own source/object receipts.
------------------------------------------------------------------------

bobDylanSongMusic : CrossPollinationReceipt
bobDylanSongMusic = cross-pollination-receipt
  bobDylanSongSeed
  "Bob Dylan -> Blowin' in the Wind"
  "Q392"
  "Q640529"
  "unresolved"
  "unresolved"
  "Ibrahim, Danforth, Dodds 2017, Connecting every bit of knowledge: The structure of Wikipedia's First Link Network, DOI 10.1016/j.jocs.2016.12.001"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  musicObjectFibre
  "DASHI.Music.Everything; DASHI.Music.MusicalSymmetryDynamicsCore"
  "the song is admitted as a concrete music-object coordinate that may later receive separately sourced structural observations"
  "no claim about melody, harmony, symmetry, lyrical structure, cognition or attractor dynamics is paid until the exact musical representation and source are supplied"
  true true false false

------------------------------------------------------------------------
-- Physics <-> music: structural cross-pollination only.
--
-- Shared mathematical language can include state, transformation, symmetry,
-- defect/energy-like functions, dynamics, fixed points and basins.  The music
-- owner deliberately leaves its Energy carrier/order domain supplied, so no
-- physical energy semantics are imported automatically.
------------------------------------------------------------------------

physicsMusicStructure : CrossPollinationReceipt
physicsMusicStructure = cross-pollination-receipt
  physicsNaturalScienceSeed
  "Physics -> natural science; cross-pollinated with repo-native music dynamics"
  "Q413"
  "Q7991"
  "530"
  "500"
  "Ibrahim paper DOI 10.1016/j.jocs.2016.12.001 plus repo-native DASHI.Music.MusicalSymmetryDynamicsCore"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  physicsMusicSharedStructureFibre
  "DASHI.Music.MusicalSymmetryDynamicsCore; DASHI.Papers.NavierStokes.TheoremInterface; DASHI.Papers.YangMills.TheoremInterface"
  "reuse only abstract structure: states, symmetries/transformations, domain-supplied defect or energy functionals, dynamics and fixed/basin structure"
  "a concrete bridge must specify the representation and prove which equations/invariants transport; similarity of vocabulary is not a physical or musical theorem"
  true true false false

------------------------------------------------------------------------
-- Native fibres over time.
--
-- Cross-pollination observations are time-indexed and history-preserving.  A
-- later source can refine or reopen a bridge without rewriting the historical
-- Ibrahim edge or earlier DASHI state.
------------------------------------------------------------------------

data CrossTime : Set where
  ibrahim2014Snapshot
  paper2017Publication
  dashiCurrent : CrossTime

data CrossInterpretation : Set where
  navigationOnly
  structuralBridgeCandidate
  empiricallyPaidBridge : CrossInterpretation

data CrossSummary : Set where
  crossDomainBridgeOpen : CrossSummary

CrossCompatible : CrossTime → CrossInterpretation → Set
CrossCompatible ibrahim2014Snapshot navigationOnly = ⊤
CrossCompatible ibrahim2014Snapshot structuralBridgeCandidate = ⊥
CrossCompatible ibrahim2014Snapshot empiricallyPaidBridge = ⊥
CrossCompatible paper2017Publication navigationOnly = ⊤
CrossCompatible paper2017Publication structuralBridgeCandidate = ⊥
CrossCompatible paper2017Publication empiricallyPaidBridge = ⊥
CrossCompatible dashiCurrent navigationOnly = ⊤
CrossCompatible dashiCurrent structuralBridgeCandidate = ⊤
CrossCompatible dashiCurrent empiricallyPaidBridge = ⊥

crossTemporalSystem : Temporal.TemporalEvidenceSystem
crossTemporalSystem = record
  { Time = CrossTime
  ; Interpretation = CrossInterpretation
  ; Compatible = CrossCompatible
  ; Summary = CrossSummary
  ; summarize = λ _ → crossDomainBridgeOpen
  ; timeReference = λ
      { ibrahim2014Snapshot → "Ibrahim Wikipedia source snapshot: month/day identity still under producer archaeology"
      ; paper2017Publication → "Ibrahim et al. Journal of Computational Science publication, DOI 10.1016/j.jocs.2016.12.001"
      ; dashiCurrent → "DASHI cross-domain formulation state on agent/dewey-qid-firstlink-coverage-priorart"
      }
  }

currentStructuralBridgeLive : Temporal.EvidenceFibre crossTemporalSystem dashiCurrent
currentStructuralBridgeLive = Temporal.liveInterpretationAt structuralBridgeCandidate tt

historicalNavigationLive : Temporal.EvidenceFibre crossTemporalSystem ibrahim2014Snapshot
historicalNavigationLive = Temporal.liveInterpretationAt navigationOnly tt

------------------------------------------------------------------------
-- Cross-domain no-promotion firewalls.
------------------------------------------------------------------------

data FruitCreatesLESMechanism : Set where
data RailCreatesPetrochemicalIdentity : Set where
data PhysicsFirstLinkCreatesNSProof : Set where
data PhysicsFirstLinkCreatesYMProof : Set where
data SongIdentityCreatesMusicTheory : Set where
data SharedEnergyWordCreatesPhysicalEquivalence : Set where
data CrossPollinationErasesTemporalSourcePath : Set where

fruitDoesNotCreateLESMechanism : FruitCreatesLESMechanism → ⊥
fruitDoesNotCreateLESMechanism ()

railDoesNotCreatePetrochemicalIdentity : RailCreatesPetrochemicalIdentity → ⊥
railDoesNotCreatePetrochemicalIdentity ()

physicsFirstLinkDoesNotCreateNSProof : PhysicsFirstLinkCreatesNSProof → ⊥
physicsFirstLinkDoesNotCreateNSProof ()

physicsFirstLinkDoesNotCreateYMProof : PhysicsFirstLinkCreatesYMProof → ⊥
physicsFirstLinkDoesNotCreateYMProof ()

songIdentityDoesNotCreateMusicTheory : SongIdentityCreatesMusicTheory → ⊥
songIdentityDoesNotCreateMusicTheory ()

sharedEnergyWordDoesNotCreatePhysicalEquivalence : SharedEnergyWordCreatesPhysicalEquivalence → ⊥
sharedEnergyWordDoesNotCreatePhysicalEquivalence ()

crossPollinationRetainsTemporalSourcePath : CrossPollinationErasesTemporalSourcePath → ⊥
crossPollinationRetainsTemporalSourcePath ()

record IbrahimOracleCrossDomainBoundary : Set where
  constructor ibrahim-oracle-cross-domain-boundary
  field
    ibrahimPrimaryDOIRetained : Bool
    qidCoordinatesRetained : Bool
    inspectedDeweyCoordinatesRetained : Bool
    unresolvedDeweyStaysUnresolved : Bool
    existingDomainOwnersReused : Bool
    fibresRemainTimeIndexed : Bool
    sourcePathRetained : Bool
    crossPollinationCreatesEmpiricalPayment : Bool
    crossPollinationCreatesProof : Bool
open IbrahimOracleCrossDomainBoundary public

canonicalIbrahimOracleCrossDomainBoundary : IbrahimOracleCrossDomainBoundary
canonicalIbrahimOracleCrossDomainBoundary =
  ibrahim-oracle-cross-domain-boundary
    true true true true true true true false false

lesBoundary : LES.EcologyLESSnowballBoundary
lesBoundary = LES.canonicalEcologyLESSnowballBoundary

musicCoreReference : String
musicCoreReference = "DASHI.Music.MusicalSymmetryDynamicsCore owns abstract symmetry/defect-energy/repair/attractor structure; it does not identify physical energy with musical defect energy"

nsReference : String
nsReference = "DASHI.Papers.NavierStokes.TheoremInterface remains the canonical NS theorem surface"

yangMillsReference : String
yangMillsReference = "DASHI.Papers.YangMills.TheoremInterface remains the canonical YM theorem surface"

petrochemReference : String
petrochemReference = "DASHI.Chemistry.SaltPetroleumIndustrialChemistryNetworkExact plus ChemicalManufacturingInventoryLogisticsCrossPollinationExact own the chemistry/logistics seam"
