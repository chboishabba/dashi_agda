module DASHI.Cognition.SpringfieldLayeredValueCaptureParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.BlackRockMirvacSpringfieldCapitalOverlapExact as Capital
import DASHI.Law.SensibLawSpringfieldGasLobbyingOwnershipSnowballExact as GasLobby
import DASHI.Law.SensibLawAzureSpringfieldInducedGasDemandExact as GasDemand
import DASHI.Law.SensibLawWoogarooSwanbankDataCentreDevelopmentPressureExact as DataCentre

------------------------------------------------------------------------
-- GREATER SPRINGFIELD LAYERED VALUE-CAPTURE PARETO
--
-- The city is not treated as a single-owner object. Distinct layers include:
-- master-developer land/masterplan uplift; parcel/precinct development margin;
-- retail/commercial rent; energy-network/embedded-network revenue; listed
-- equity exposure; public rates/tax and infrastructure/service obligations;
-- and ecological/social burdens. Ownership at one layer does not imply control
-- of another.
------------------------------------------------------------------------

data ValueLayer : Set where
  masterDeveloperLandUplift : ValueLayer
  parcelDevelopmentMargin : ValueLayer
  retailCommercialRent : ValueLayer
  residentialSaleOrRent : ValueLayer
  energyConnectionAndThroughput : ValueLayer
  embeddedNetworkRevenue : ValueLayer
  listedEquityReturn : ValueLayer
  ratesAndTax : ValueLayer
  publicInfrastructureObligation : ValueLayer
  ecologicalExternality : ValueLayer
  optionValueFromFutureExpansion : ValueLayer

record LayerReceipt : Set where
  constructor layer-receipt
  field
    label : String
    actor : String
    source : String
    boundedFinding : String
    layer : ValueLayer
    paid : Bool
open LayerReceipt public

springfieldMasterDeveloper : LayerReceipt
springfieldMasterDeveloper = layer-receipt
  "Springfield City Group master-developer layer"
  "Springfield City Group / Maha Sinnathamby and Bob Sharpless"
  "Springfield City Group public history; 2026 City West transaction reporting"
  "Springfield City Group is the master developer of Greater Springfield and sold the 12.7 ha City West town-centre site in 2026 after long-term stewardship. This pays the master-developer/land-allocation layer, not ownership of every downstream parcel or operating asset."
  masterDeveloperLandUplift true

mirvacOrionLayer : LayerReceipt
mirvacOrionLayer = layer-receipt
  "Mirvac Orion Springfield Central"
  "Mirvac"
  "Mirvac FY26 property portfolio / Orion asset page"
  "Mirvac owns Orion Springfield Central 100%, developed the centre and records adjoining land for future expansion. Orion therefore pays a retail-rent plus future-expansion-option layer within Springfield, not master control of Greater Springfield."
  retailCommercialRent true

blackRockMirvacLayer : LayerReceipt
blackRockMirvacLayer = layer-receipt
  "BlackRock listed-equity exposure to Mirvac"
  "BlackRock Group"
  "Mirvac 2026 substantial-holder disclosure summary"
  "BlackRock is a substantial Mirvac securityholder at about 7.70%. This pays portfolio/equity exposure to Mirvac's asset base, including Orion indirectly, but not operational control over Mirvac, Orion or Springfield City Group."
  listedEquityReturn true

mathiesonGordonCityWestLayer : LayerReceipt
mathiesonGordonCityWestLayer = layer-receipt
  "Mathieson/Gordon City West acquisition"
  "Bruce Mathieson family / Gordon Corp"
  "2026 Springfield Central City West transaction reporting"
  "Gordon Corp and the Mathieson family acquired a 12.7 ha town-centre site from Springfield City Group for AUD 50 million for mixed retail, commercial, entertainment, leisure and residential development. This pays a downstream parcel-development/value-capture layer."
  parcelDevelopmentMargin true

mathiesonHospitalityRetailAdjacency : LayerReceipt
mathiesonHospitalityRetailAdjacency = layer-receipt
  "Mathieson hospitality/retail capital adjacency"
  "Bruce Mathieson Group"
  "Endeavour Group demerger/annual-report material"
  "Bruce Mathieson Group historically held a substantial Endeavour Group interest following the ALH/Woolworths restructuring. This identifies a large hospitality/retail capital base adjacent to the Springfield City West acquisition; it does not prove that Endeavour or ALH is a party to the Springfield project."
  listedEquityReturn true

springfieldGasLayer : LayerReceipt
springfieldGasLayer = layer-receipt
  "Springfield gas/electric infrastructure alliance"
  "Springfield Land Corporation / Energex"
  "Existing SpringfieldGasLobbyingOwnershipSnowball source atlas"
  "A contemporaneous source locates an Energex-Springfield alliance to develop gas and electricity networks, including an 8,000-gas-connection target. The original agreement and exact current gas-asset lineage remain open."
  energyConnectionAndThroughput true

orionEmbeddedNetworkLayer : LayerReceipt
orionEmbeddedNetworkLayer = layer-receipt
  "Orion embedded electricity network"
  "Mirvac Real Estate / registered network entities"
  "AER Orion Springfield Central embedded-network exemption; BlackRockMirvacSpringfield owner"
  "The Orion precinct has a separately identifiable embedded electricity-network coordinate, distinct from the wider historical Springfield gas-network lineage."
  embeddedNetworkRevenue true

------------------------------------------------------------------------
-- Benefit / burden / control / voice / exit decomposition.
------------------------------------------------------------------------

record IncidenceCoordinate : Set where
  constructor incidence-coordinate
  field
    actor : String
    directGain : String
    controlCoordinate : String
    burdenCoordinate : String
    voiceCoordinate : String
    exitCoordinate : String
open IncidenceCoordinate public

masterDeveloperIncidence : IncidenceCoordinate
masterDeveloperIncidence = incidence-coordinate
  "Springfield City Group"
  "Land-sale proceeds, residual land uplift, masterplan option value and downstream development participation where separately contracted."
  "Masterplan/land-allocation influence subject to planning law, approvals and municipal/state powers."
  "Carries development, infrastructure and market risk on retained interests; ecological/public burdens may fall elsewhere."
  "High private development voice plus formal planning engagement; not equivalent to sovereign/local-government authority."
  "Can sell/partner parcels subject to contracts, planning and market conditions."

mirvacIncidence : IncidenceCoordinate
mirvacIncidence = incidence-coordinate
  "Mirvac"
  "Retail/commercial rents, asset appreciation and future-expansion option value from Orion and adjoining holdings."
  "Operational control of Orion asset; not control of Springfield City Group or Greater Springfield as a whole."
  "Carries Orion operating/capital risk while broader infrastructure/ecological burdens are distributed across public/private actors."
  "Large institutional/property-owner voice through ownership and planning processes."
  "Can refinance, redevelop or transact assets subject to law/market constraints."

blackRockIncidence : IncidenceCoordinate
blackRockIncidence = incidence-coordinate
  "BlackRock-managed capital"
  "Portfolio return from Mirvac securities proportional to holdings and fund mandates."
  "Voting/equity influence at Mirvac level; no paid same-object operational control of Orion or Springfield."
  "Investment risk is borne by underlying funds/clients according to mandate; local ecological/service burdens are not thereby internalised."
  "Shareholder voice through governance rights; not local planning sovereignty."
  "Can trade/rebalance subject to mandate, liquidity and disclosure rules."

mathiesonGordonIncidence : IncidenceCoordinate
mathiesonGordonIncidence = incidence-coordinate
  "Gordon Corp / Mathieson family partnership"
  "Future development margin, rents/sales and option value from City West precinct development."
  "Control over acquired parcel/project subject to approvals and contracts; not master control of Greater Springfield."
  "Carries project/development risk; infrastructure and ecological burdens may be shared or externalised depending on approvals/agreements."
  "Strong project-level commercial voice."
  "Can phase, partner, sell or refinance interests subject to contracts and approvals."

------------------------------------------------------------------------
-- Non-collapse boundaries.
------------------------------------------------------------------------

data BlackRockStakeImpliesSpringfieldControl : Set where
data MirvacOrionImpliesCityOwnership : Set where
data MathiesonParcelImpliesCityControl : Set where
data GasAllianceImpliesCurrentGasAssetOwnership : Set where
data ValueCaptureImpliesWrongdoing : Set where

blackRockStakeDoesNotCreateSpringfieldControl : BlackRockStakeImpliesSpringfieldControl → ⊥
blackRockStakeDoesNotCreateSpringfieldControl ()

mirvacOrionDoesNotCreateCityOwnership : MirvacOrionImpliesCityOwnership → ⊥
mirvacOrionDoesNotCreateCityOwnership ()

mathiesonParcelDoesNotCreateCityControl : MathiesonParcelImpliesCityControl → ⊥
mathiesonParcelDoesNotCreateCityControl ()

gasAllianceDoesNotCreateCurrentAssetOwnership : GasAllianceImpliesCurrentGasAssetOwnership → ⊥
gasAllianceDoesNotCreateCurrentAssetOwnership ()

valueCaptureDoesNotCreateWrongdoing : ValueCaptureImpliesWrongdoing → ⊥
valueCaptureDoesNotCreateWrongdoing ()

------------------------------------------------------------------------
-- Pareto acquisition order.
------------------------------------------------------------------------

data SpringfieldDebt : Set where
  cityWestOwnershipVehicleAndCapitalStack : SpringfieldDebt
  masterDeveloperResidualOwnershipMap : SpringfieldDebt
  mirvacSpringfieldTransactionHistory : SpringfieldDebt
  blackRockMirvacVotingAndFundExposure : SpringfieldDebt
  springfieldGasAgreementAndAssetChain : SpringfieldDebt
  santoroLobbyingSubjectMatter : SpringfieldDebt
  localInfrastructureSubsidyAndRatesIncidence : SpringfieldDebt
  ecologicalBurdenByParcel : SpringfieldDebt

record SpringfieldAcquisition : Set where
  constructor springfield-acquisition
  field
    debt : SpringfieldDebt
    priority : Nat
    sameObjectRequired : Bool
    question : String
open SpringfieldAcquisition public

canonicalSpringfieldAcquisition : List SpringfieldAcquisition
canonicalSpringfieldAcquisition =
  springfield-acquisition cityWestOwnershipVehicleAndCapitalStack 100 true
    "Resolve the exact Gordon/Mathieson acquisition vehicle, equity/debt split, lenders, guarantees, JV rights, future leases and counterparties for the AUD 50m City West site."
  ∷ springfield-acquisition springfieldGasAgreementAndAssetChain 100 true
    "Acquire the original Energex-Springfield gas/electric alliance instrument and trace the exact Springfield gas assets through later Allgas/AGIG/Stonepeak ownership."
  ∷ springfield-acquisition santoroLobbyingSubjectMatter 99 true
    "Resolve the subject matter, asks, documents and downstream decisions attached to Springfield/Santoro ministerial lobbying contacts."
  ∷ springfield-acquisition mirvacSpringfieldTransactionHistory 98 true
    "Trace Mirvac's original Orion acquisition/development agreements, adjoining-land purchases, Springfield City Group counterparties and any joint-development/revenue-sharing arrangements."
  ∷ springfield-acquisition masterDeveloperResidualOwnershipMap 98 true
    "Map Springfield City Group retained parcels, sold parcels, options, JVs and continuing revenue rights across the masterplanned city."
  ∷ springfield-acquisition blackRockMirvacVotingAndFundExposure 97 true
    "Resolve which BlackRock funds/entities hold Mirvac securities, voting arrangements and whether exposure is passive/index, active or mandate-specific; do not equate substantial holding with operational control."
  ∷ springfield-acquisition localInfrastructureSubsidyAndRatesIncidence 96 true
    "Quantify public infrastructure contributions, developer charges, rates/tax and service obligations by layer to identify public/private incidence."
  ∷ springfield-acquisition ecologicalBurdenByParcel 95 true
    "Join parcel-level value capture to habitat clearing, offset, heat, water, traffic and cumulative ecological burdens rather than assigning impacts to the city as a monolith."
  ∷ []
