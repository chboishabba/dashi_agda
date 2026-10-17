module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoPublishedMaterialProducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PUBLISHED MATERIAL PRODUCER
--
-- Structure authority:
--   Mandujano et al., Phys. Rev. B 110, 144420 (2024),
--   DOI 10.1103/PhysRevB.110.144420.
--   P63/mmc #194, a = 6.8828(1) A, c = 12.4535(3) A; Table-II refined
--   Co/Ta/Se Wyckoff coordinates are materialised in
--   data/co_tase2/published_material_dft_recipe_2026.json.
--
-- ARPES/DFT authority:
--   Sprague et al., Nature Communications (2026),
--   DOI 10.1038/s41467-026-76784-x.
--   Public Methods specify VASP, plane-wave pseudopotential GGA/PBE,
--   600 eV cutoff, a=b=6.88 A, c=12.47 A, 9x9x4 k mesh, internal relaxation
--   to <0.001 eV/A and self-consistency 1e-9 eV.
--
-- Source-reported agreement with the observed bands is retained as a SOURCE
-- statement.  It is not promoted to a repository reproduction or an explicit
-- material Hamiltonian.  Public material inspected for this tranche does not
-- provide a repository-native Wannier Hamiltonian/hopping table or enough
-- implementation identity to bitwise reproduce the source calculation.
------------------------------------------------------------------------

record CrystalStructureProducer : Set where
  constructor crystal-structure-producer
  field
    sourceDOI : String
    nuclearSpaceGroupNumber : Nat
    latticeConstantsMaterialised : Bool
    cobaltWyckoffMaterialised : Bool
    tantalumWyckoffMaterialised : Bool
    seleniumWyckoffMaterialised : Bool
    siteOccupanciesMaterialised : Bool
    fullPublishedRefinedBasisMaterialised : Bool

open CrystalStructureProducer public

publishedCrystalStructure : CrystalStructureProducer
publishedCrystalStructure = crystal-structure-producer
  "10.1103/PhysRevB.110.144420"
  194
  true true true true true true

record PublishedDFTProducer : Set where
  constructor published-dft-producer
  field
    sourceDOI : String
    codeIdentityPublished : Bool
    planeWavePseudopotentialMethodPublished : Bool
    pbeGGAPublished : Bool
    cutoff600eVPublished : Bool
    fixedLatticePublished : Bool
    kMesh9x9x4Published : Bool
    relaxationTolerancePublished : Bool
    scfTolerancePublished : Bool
    sourceReportsBandAgreement : Bool
    exactPseudopotentialArtifactsAvailable : Bool
    exactSourceInputDeckAvailable : Bool
    sourceWavefunctionsAvailable : Bool
    explicitWannierConstructionAvailable : Bool
    explicitTightBindingMatrixAvailable : Bool
    repositoryDFTReproductionExecuted : Bool

open PublishedDFTProducer public

publishedSpragueDFT : PublishedDFTProducer
publishedSpragueDFT = published-dft-producer
  "10.1038/s41467-026-76784-x"
  true true true true true true true true true
  false false false false false false

record MaterialHamiltonianProducerStatus : Set where
  constructor material-hamiltonian-producer-status
  field
    literalCrystalBasisPaid : Bool
    publishedAbInitioProtocolPaid : Bool
    sourceReportedBandAgreementPaid : Bool
    exactAbInitioArtifactPaid : Bool
    fullOrbitalHamiltonianPaid : Bool
    explicitSOCHamiltonianPaid : Bool
    WannierSameObjectPaid : Bool
    quantitativeARPESSameObjectPaid : Bool

canonicalMaterialHamiltonianProducerStatus : MaterialHamiltonianProducerStatus
canonicalMaterialHamiltonianProducerStatus =
  material-hamiltonian-producer-status
    true true true
    false false false false false

record MaterialProducerPromotionBoundary : Set where
  constructor material-producer-promotion-boundary
  field
    publishedRecipeImpliesReproducedCalculation : Bool
    sourceAgreementImpliesRepositoryHamiltonian : Bool
    refinedCrystalBasisDeterminesHoppings : Bool
    symmetryDeterminesMaterialParameters : Bool
    explicitElectronicArtifactStillRequired : Bool

canonicalMaterialProducerPromotionBoundary : MaterialProducerPromotionBoundary
canonicalMaterialProducerPromotionBoundary =
  material-producer-promotion-boundary false false false false true
