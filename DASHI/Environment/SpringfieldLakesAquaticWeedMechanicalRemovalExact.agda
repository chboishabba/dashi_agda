module DASHI.Environment.SpringfieldLakesAquaticWeedMechanicalRemovalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- SPRINGFIELD LAKES OPERATIONAL ANALOGUE
--
-- Primary institutional source: Ipswich City Council, published 19 June 2025.
-- The reported target is SALVINIA, not water hyacinth.  This owner therefore
-- indexes the record only as a local operational analogue for mechanical
-- aquatic-weed removal, access constraints, biomass export and equipment choice.
-- It is not evidence that the same machinery has controlled water hyacinth at
-- Springfield Lakes and it does not transfer efficacy across weed species.
------------------------------------------------------------------------

ipswichSpiderSource : Attr.AttributedSource
ipswichSpiderSource = Attr.mkNoDOISource
  "Ipswich City Council"
  "Strides made in salvinia weed management across Springfield Lakes waterways"
  "Ipswich City Council news release"
  "2025"
  "https://www.ipswich.qld.gov.au/News-Articles-Folder/2025/Strides-made-in-salvinia-weed-management-across-Springfield-Lakes-waterways"
  Attr.governmentSource
  "local Springfield Lakes operational record for salvinia removal using a spider excavator and aquatic weed harvester; supports access/equipment/biomass-removal context only, not water-hyacinth efficacy"
  Attr.publicAttribution

ipswichSpiderSnowballReceipt : Snowball.SourceRoleSnowballReceipt ipswichSpiderSource
ipswichSpiderSnowballReceipt = Snowball.canonicalSourceRoleSnowballReceipt ipswichSpiderSource

------------------------------------------------------------------------
-- Source-bound operational coordinates.
------------------------------------------------------------------------

data WeedIdentity : Set where
  salvinia : WeedIdentity
  waterHyacinth : WeedIdentity

data EquipmentKind : Set where
  spiderExcavator : EquipmentKind
  aquaticWeedHarvester : EquipmentKind

data SiteKind : Set where
  viewpointDrivePond : SiteKind
  vistulaCircuitPond : SiteKind

data AccessConstraint : Set where
  steepHardAccess shallowDenseMat : AccessConstraint

data SourceOutcome : Set where
  someSuccessWorksContinuing eightyTonnesRemoved : SourceOutcome

record SpringfieldMechanicalRemovalReceipt : Set where
  constructor springfieldMechanicalRemovalReceipt
  field
    targetWeed : WeedIdentity
    site : SiteKind
    equipment : EquipmentKind
    accessConstraint : AccessConstraint
    reportedOutcome : SourceOutcome
    sourceReference : String
    biomassExportOperationallyRelevant : Bool

open SpringfieldMechanicalRemovalReceipt public

viewpointSpiderReceipt : SpringfieldMechanicalRemovalReceipt
viewpointSpiderReceipt = springfieldMechanicalRemovalReceipt
  salvinia
  viewpointDrivePond
  spiderExcavator
  steepHardAccess
  someSuccessWorksContinuing
  "Ipswich City Council, 19 June 2025: council-first spider excavator trial at 9000 Viewpoint Drive, Springfield Lakes"
  true

vistulaHarvesterReceipt : SpringfieldMechanicalRemovalReceipt
vistulaHarvesterReceipt = springfieldMechanicalRemovalReceipt
  salvinia
  vistulaCircuitPond
  aquaticWeedHarvester
  shallowDenseMat
  eightyTonnesRemoved
  "Ipswich City Council, 19 June 2025: aquatic weed harvester at pond near 31 Vistula Circuit Reserve; reported 80 tonnes salvinia removed from that pond"
  true

------------------------------------------------------------------------
-- Species-transfer and outcome boundaries.
------------------------------------------------------------------------

record SpringfieldMechanicalRemovalBoundary : Set where
  constructor springfieldMechanicalRemovalBoundary
  field
    sourceTargetIsSalvinia : Bool
    sourceTargetIsSalviniaIsTrue : sourceTargetIsSalvinia ≡ true

    sourceProvesSpringfieldWaterHyacinthRemoval : Bool
    sourceProvesSpringfieldWaterHyacinthRemovalIsFalse :
      sourceProvesSpringfieldWaterHyacinthRemoval ≡ false

    salviniaEquipmentSuccessTransfersToWaterHyacinth : Bool
    salviniaEquipmentSuccessTransfersToWaterHyacinthIsFalse :
      salviniaEquipmentSuccessTransfersToWaterHyacinth ≡ false

    mechanicalRemovalCanInstantiateBiomassExportPath : Bool
    mechanicalRemovalCanInstantiateBiomassExportPathIsTrue :
      mechanicalRemovalCanInstantiateBiomassExportPath ≡ true

    equipmentChoiceDependsOnAccessGeometry : Bool
    equipmentChoiceDependsOnAccessGeometryIsTrue :
      equipmentChoiceDependsOnAccessGeometry ≡ true

    removalMassAloneProvesNetEcosystemBenefit : Bool
    removalMassAloneProvesNetEcosystemBenefitIsFalse :
      removalMassAloneProvesNetEcosystemBenefit ≡ false

canonicalSpringfieldMechanicalRemovalBoundary : SpringfieldMechanicalRemovalBoundary
canonicalSpringfieldMechanicalRemovalBoundary = springfieldMechanicalRemovalBoundary
  true refl
  false refl
  false refl
  true refl
  true refl
  false refl

operationalReading : String
operationalReading =
  "Springfield Lakes supplies a local, source-paid example that mechanical weed removal has equipment/access geometry: spider excavator for a steep hard-to-access pond and aquatic weed harvester for a dense surface mat.  Because the reported weed is salvinia, this is an operational analogue for the biocontrol biomass-fate experiment, not water-hyacinth efficacy evidence."

------------------------------------------------------------------------
-- Repository easter egg only.
--
-- This is intentionally outside every empirical/proof receipt above.  The
-- address is source-paid; the joke is Johl/DASHI commentary and carries no
-- evidentiary, ecological, metrological, or deployment meaning.
------------------------------------------------------------------------

over9000ViewpointSpiderJoke : String
over9000ViewpointSpiderJoke =
  "You can view the spider at 9000 Viewpoint Drive: the spider is OVER 9000. WHAT? 9000? That's impossible!"

record SpiderJokeAttributionBoundary : Set where
  constructor spiderJokeAttributionBoundary
  field
    jokeIsSourceClaim : Bool
    jokeIsSourceClaimIsFalse : jokeIsSourceClaim ≡ false
    jokeCreatesScientificEvidence : Bool
    jokeCreatesScientificEvidenceIsFalse : jokeCreatesScientificEvidence ≡ false
    addressRemainsSourceBound : Bool
    addressRemainsSourceBoundIsTrue : addressRemainsSourceBound ≡ true

canonicalSpiderJokeAttributionBoundary : SpiderJokeAttributionBoundary
canonicalSpiderJokeAttributionBoundary =
  spiderJokeAttributionBoundary false refl false refl true refl
