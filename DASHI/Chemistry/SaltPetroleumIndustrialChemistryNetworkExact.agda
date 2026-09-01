module DASHI.Chemistry.SaltPetroleumIndustrialChemistryNetworkExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Chemistry.ChlorAlkaliSaltIndustryExact as ChlorAlkali
import DASHI.Chemistry.RefineryFeedstockSaltConstraintBidiExact as Refinery
import DASHI.Geology.SaltGeochemistryExact as Salt

------------------------------------------------------------------------
-- SALT + PETROLEUM INDUSTRIAL CHEMISTRY NETWORK
--
-- The common structure is a transformation network, not one generic
-- "cracking" reaction.  Chlor-alkali electrolysis, hydrocarbon cracking,
-- chlorination, polymerisation, neutralisation and hydrogenation remain
-- distinct process kinds even when their material streams meet downstream.
--
-- Source anchors / bounded empirical roles:
-- * Chemistry Australia: salt/brine -> chlorine/caustic/hydrogen and the
--   chlorine + ethylene -> VCM/PVC industrial connection.
-- * ECVM / European PVC value-chain material: PVC combines chlorine derived
--   from salt with ethylene from hydrocarbon or other carbon feedstocks.
-- * Linde/BASF petrochemical process descriptions: steam crackers produce
--   ethylene, propylene, butadiene and aromatics as downstream building blocks.
-- * US EPA petroleum-refining material: caustic solutions are used to
--   neutralise/extract acidic refinery species and cracking products.
--
-- These sources motivate application sockets; plant-specific kinetics, yields,
-- product slates, pharmaceutical syntheses and causal market effects still need
-- independent application receipts.
------------------------------------------------------------------------

data IndustrialProcessKind : Set where
  chlorAlkaliElectrolysis
  steamCracking
  catalyticCracking
  chlorination
  dehydrochlorination
  polymerisation
  hydrogenation
  oxidation
  neutralisationExtraction
  separationPurification
  formulationFinishing
  : IndustrialProcessKind

data MaterialFamily : Set where
  geologicalSalt
  purifiedBrine
  chlorine
  causticSoda
  hydrogen
  hydrocarbonFeed
  ethylene
  propylene
  aromatics
  ethyleneDichloride
  vinylChlorideMonomer
  pvcResin
  hydrochloricAcid
  refineryTreatedStream
  pharmaceuticalIntermediate
  formulatedMedicine
  : MaterialFamily

------------------------------------------------------------------------
-- Important process non-collapse.
------------------------------------------------------------------------

saltPrimaryTransformation : IndustrialProcessKind
saltPrimaryTransformation = chlorAlkaliElectrolysis

petrochemicalPrimaryTransformation : IndustrialProcessKind
petrochemicalPrimaryTransformation = steamCracking

electrolysisIsNotSteamCracking :
  saltPrimaryTransformation ≡ petrochemicalPrimaryTransformation → ⊥
electrolysisIsNotSteamCracking ()

------------------------------------------------------------------------
-- Material lineage graph.
------------------------------------------------------------------------

record IndustrialTransformationEdge : Set where
  constructor industrial-transformation-edge
  field
    process : IndustrialProcessKind
    inputA : MaterialFamily
    inputB : MaterialFamily
    output : MaterialFamily
    stoichiometryOrMaterialBalanceReference : String
    operatingEnvelopeReference : String
    separationPurificationReference : String
    safetyReference : String
    validationReference : String

open IndustrialTransformationEdge public

saltToChlorine : IndustrialTransformationEdge
saltToChlorine =
  industrial-transformation-edge
    chlorAlkaliElectrolysis geologicalSalt purifiedBrine chlorine
    "2 NaCl + 2 H2O -> Cl2 + H2 + 2 NaOH overall bookkeeping; detailed half reactions owned elsewhere"
    "chlor-alkali cell envelope supplied by plant receipt"
    "brine purification and product separation required"
    "chlorine/caustic/hydrogen plant safety receipt required"
    "consume canonical ChlorAlkaliProductionReceipt"

hydrocarbonToEthylene : IndustrialTransformationEdge
hydrocarbonToEthylene =
  industrial-transformation-edge
    steamCracking hydrocarbonFeed hydrocarbonFeed ethylene
    "cracker material balance and product slate supplied by application"
    "feed-specific steam-cracking envelope supplied by application"
    "cracked-gas separation train required"
    "petrochemical furnace/separation safety receipt required"
    "plant-specific cracker validation required"

chlorineEthyleneToEDC : IndustrialTransformationEdge
chlorineEthyleneToEDC =
  industrial-transformation-edge
    chlorination chlorine ethylene ethyleneDichloride
    "chlorine + ethylene material balance supplied by EDC/VCM process receipt"
    "EDC reaction envelope supplied by application"
    "EDC purification supplied by application"
    "chlorinated-organic process safety receipt required"
    "EDC/VCM plant validation required"

edcToVCM : IndustrialTransformationEdge
edcToVCM =
  industrial-transformation-edge
    dehydrochlorination ethyleneDichloride ethyleneDichloride vinylChlorideMonomer
    "EDC -> VCM + HCl process balance supplied by application"
    "VCM process envelope supplied by application"
    "VCM/HCl separation supplied by application"
    "VCM process safety receipt required"
    "VCM plant validation required"

vcmToPVC : IndustrialTransformationEdge
vcmToPVC =
  industrial-transformation-edge
    polymerisation vinylChlorideMonomer vinylChlorideMonomer pvcResin
    "VCM polymerisation material balance supplied by application"
    "polymerisation recipe/envelope supplied by application"
    "residual monomer and resin finishing supplied by application"
    "polymerisation safety/specification receipt required"
    "PVC grade validation required"

causticToRefineryTreatment : IndustrialTransformationEdge
causticToRefineryTreatment =
  industrial-transformation-edge
    neutralisationExtraction causticSoda hydrocarbonFeed refineryTreatedStream
    "caustic neutralisation/extraction load supplied by refinery application"
    "refinery treating envelope supplied by application"
    "spent-caustic separation/treatment supplied by application"
    "spent-caustic and sour-service safety receipt required"
    "refinery treating validation required"

hydrogenToRefineryTreatment : IndustrialTransformationEdge
hydrogenToRefineryTreatment =
  industrial-transformation-edge
    hydrogenation hydrogen hydrocarbonFeed refineryTreatedStream
    "hydrogen consumption/material balance supplied by hydrotreating application"
    "pressure/catalyst/feed envelope supplied by application"
    "gas/liquid separation and recycle supplied by application"
    "high-pressure hydrogen service safety receipt required"
    "hydrotreating validation required"

------------------------------------------------------------------------
-- PVC is the canonical literal join between salt-derived chlorine and a
-- carbon-derived ethylene stream.  Neither side alone recovers the product.
------------------------------------------------------------------------

data PVCFeedAvailability : Set where
  chlorineOnly ethyleneOnly bothFeedsAvailable : PVCFeedAvailability

data PVCProductionReady : PVCFeedAvailability → Set where
  pvcReady : PVCProductionReady bothFeedsAvailable

chlorineAloneDoesNotClosePVC : PVCProductionReady chlorineOnly → ⊥
chlorineAloneDoesNotClosePVC ()

ethyleneAloneDoesNotClosePVC : PVCProductionReady ethyleneOnly → ⊥
ethyleneAloneDoesNotClosePVC ()

------------------------------------------------------------------------
-- Pharmaceutical chemistry is represented as a downstream family, not as the
-- false claim that every medicine contains chlorine or petroleum.  Chlorine,
-- caustic, hydrogen and petrochemical intermediates may participate at some
-- manufacturing stage; each concrete synthesis still needs a product-specific
-- route receipt.
------------------------------------------------------------------------

data PharmaceuticalRouteAuthority : Set where
  productSpecificSynthesisReceipt : PharmaceuticalRouteAuthority

data GenericChlorineUseAutomaticallyProvesMedicineComposition : Set where

genericChlorineUseDoesNotProveMedicineComposition :
  GenericChlorineUseAutomaticallyProvesMedicineComposition → ⊥
genericChlorineUseDoesNotProveMedicineComposition ()

record DownstreamManufacturingReceipt : Set where
  constructor downstream-manufacturing-receipt
  field
    productFamily : MaterialFamily
    upstreamSaltDerivedInputReference : String
    upstreamPetroleumDerivedInputReference : String
    reactionRouteReference : String
    purificationSpecificationReference : String
    inventoryLotTraceabilityReference : String
    regulationQualityReference : String
    wasteByproductReference : String
    empiricalValidationReference : String

------------------------------------------------------------------------
-- Existing-owner welds.
------------------------------------------------------------------------

saltBoundary : Salt.SaltGeochemistryBoundary
saltBoundary = Salt.canonicalSaltGeochemistryBoundary

chlorAlkaliBoundary : ChlorAlkali.ChlorAlkaliBoundary
chlorAlkaliBoundary = ChlorAlkali.canonicalChlorAlkaliBoundary

refineryBoundary : Refinery.RefineryFeedstockSaltBoundary
refineryBoundary = Refinery.canonicalRefineryFeedstockSaltBoundary

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record SaltPetroleumIndustrialChemistryBoundary : Set where
  constructor salt-petroleum-industrial-chemistry-boundary
  field
    chlorAlkaliElectrolysisEqualsHydrocarbonCracking : Bool
    chlorAlkaliElectrolysisEqualsHydrocarbonCrackingIsFalse :
      chlorAlkaliElectrolysisEqualsHydrocarbonCracking ≡ false
    saltAloneDeterminesPVCProduction : Bool
    saltAloneDeterminesPVCProductionIsFalse : saltAloneDeterminesPVCProduction ≡ false
    petroleumAloneDeterminesPVCProduction : Bool
    petroleumAloneDeterminesPVCProductionIsFalse : petroleumAloneDeterminesPVCProduction ≡ false
    chlorineUseAtSomeManufacturingStageMeansFinalProductContainsChlorine : Bool
    chlorineUseAtSomeManufacturingStageMeansFinalProductContainsChlorineIsFalse :
      chlorineUseAtSomeManufacturingStageMeansFinalProductContainsChlorine ≡ false
    causticAvailabilityDeterminesRefineryThroughput : Bool
    causticAvailabilityDeterminesRefineryThroughputIsFalse :
      causticAvailabilityDeterminesRefineryThroughput ≡ false
    sameNominalEndProductRecoversUniqueUpstreamMaterialHistory : Bool
    sameNominalEndProductRecoversUniqueUpstreamMaterialHistoryIsFalse :
      sameNominalEndProductRecoversUniqueUpstreamMaterialHistory ≡ false
    integratedManufactureNeedsChemistryLogisticsAndQualityReceipts : Bool
    integratedManufactureNeedsChemistryLogisticsAndQualityReceiptsIsTrue :
      integratedManufactureNeedsChemistryLogisticsAndQualityReceipts ≡ true

canonicalSaltPetroleumIndustrialChemistryBoundary :
  SaltPetroleumIndustrialChemistryBoundary
canonicalSaltPetroleumIndustrialChemistryBoundary =
  salt-petroleum-industrial-chemistry-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
