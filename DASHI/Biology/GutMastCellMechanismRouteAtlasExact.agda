module DASHI.Biology.GutMastCellMechanismRouteAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.QuailEggHistamineGutSnowballExact as Gut
import DASHI.Biology.QuailEggGutTransferRound2Exact as Transfer

------------------------------------------------------------------------
-- Distinct mast-cell / histamine mechanism routes.
-- A shared word such as "mast cell" does not make receptor, trigger,
-- compartment, intervention direction, or endpoint interchangeable.
------------------------------------------------------------------------

data RouteInput : Set where
  quailAlbumenExposure : RouteInput
  microbialHistamine : RouteInput
  fecalLPS : RouteInput
  releasedHistamine : RouteInput

data RouteTarget : Set where
  par2MAPKNFkBCellSignalling : RouteTarget
  histamineH4Receptor : RouteTarget
  mastCellTLR4 : RouteTarget
  histamineH1TRPV1SensoryAxis : RouteTarget

data RouteEndpoint : Set where
  degranulationMediatorRelease : RouteEndpoint
  visceralHypersensitivityAndMastCellAccumulation : RouteEndpoint
  colonicBarrierDysfunction : RouteEndpoint
  visceralSensoryNeuronSensitization : RouteEndpoint

data RouteDirection : Set where
  suppressiveInterventionAssociation : RouteDirection
  pathogenicMechanismAssociation : RouteDirection
  receptorSensitizationAssociation : RouteDirection

record MastCellMechanismRoute : Set where
  constructor mast-cell-mechanism-route
  field
    source : Source.AttributedSource
    input : RouteInput
    target : RouteTarget
    endpoint : RouteEndpoint
    direction : RouteDirection
    evidenceSurface : String
    routeReading : String
    exactTargetIdentityPaid : Bool
    humanIBSEfficacyPaid : Bool

open MastCellMechanismRoute public

quailAlbumenPAR2Route : MastCellMechanismRoute
quailAlbumenPAR2Route = mast-cell-mechanism-route
  Gut.lianto2018Source
  quailAlbumenExposure
  par2MAPKNFkBCellSignalling
  degranulationMediatorRelease
  suppressiveInterventionAssociation
  "HMC-1 cell assays plus mouse PCA"
  "Quail albumen suppressed degranulation mediators and altered PAR2-associated MAPK/NF-kB signalling in the tested model; this does not identify a unique molecular target or establish human IBS efficacy."
  false false

microbialHistamineH4Route : MastCellMechanismRoute
microbialHistamineH4Route = mast-cell-mechanism-route
  Gut.dePalma2022Source
  microbialHistamine
  histamineH4Receptor
  visceralHypersensitivityAndMastCellAccumulation
  pathogenicMechanismAssociation
  "human IBS microbiome stratification plus microbiota-transfer/gnotobiotic mouse mechanism"
  "Microbial histamine/H4 signalling is retained as a bounded visceral-hypersensitivity route in the acquired IBS evidence."
  true false

fecalLPSTLR4Route : MastCellMechanismRoute
fecalLPSTLR4Route = mast-cell-mechanism-route
  Transfer.gao2025Source
  fecalLPS
  mastCellTLR4
  colonicBarrierDysfunction
  pathogenicMechanismAssociation
  "human IBS-D low-FODMAP mechanistic intervention plus fecal-supernatant, pharmacologic, knockout and mast-cell-reconstitution mouse experiments"
  "Fecal LPS/TLR4 activation of colonic mast cells is retained as a distinct barrier-dysfunction route; it is not identified with microbial histamine/H4 signalling."
  true false

histamineH1TRPV1Route : MastCellMechanismRoute
histamineH1TRPV1Route = mast-cell-mechanism-route
  Gut.wouters2016Source
  releasedHistamine
  histamineH1TRPV1SensoryAxis
  visceralSensoryNeuronSensitization
  receptorSensitizationAssociation
  "human IBS biopsy/sensory-neuron mechanism plus randomized ebastine intervention"
  "Histamine H1-mediated TRPV1 sensitization is a sensory route downstream of histamine and is distinct from H4, TLR4 and the quail cell-signalling surface."
  true false

data SameMastCellWordImpliesSameMechanismPermission : Set where
sameMastCellWordDoesNotIdentifyMechanism :
  SameMastCellWordImpliesSameMechanismPermission → ⊥
sameMastCellWordDoesNotIdentifyMechanism ()

data SuppressingOneRouteTreatsAllHistamineIBSPermission : Set where
oneRouteSuppressionDoesNotTreatAllIBS :
  SuppressingOneRouteTreatsAllHistamineIBSPermission → ⊥
oneRouteSuppressionDoesNotTreatAllIBS ()

record GutMastCellMechanismRouteAtlas : Set where
  constructor gut-mast-cell-mechanism-route-atlas
  field
    routes : List MastCellMechanismRoute
    receptorAndTriggerIdentityRetained : Bool
    receptorAndTriggerIdentityRetainedIsTrue : receptorAndTriggerIdentityRetained ≡ true
    compartmentAndEndpointIdentityRetained : Bool
    compartmentAndEndpointIdentityRetainedIsTrue : compartmentAndEndpointIdentityRetained ≡ true
    quailRouteDoesNotAutoBridgeToHumanIBS : Bool
    quailRouteDoesNotAutoBridgeToHumanIBSIsTrue : quailRouteDoesNotAutoBridgeToHumanIBS ≡ true
    interventionShouldMeasureMultipleRoutesWhenClaimRequiresThem : Bool
    interventionShouldMeasureMultipleRoutesWhenClaimRequiresThemIsTrue :
      interventionShouldMeasureMultipleRoutesWhenClaimRequiresThem ≡ true

canonicalGutMastCellMechanismRouteAtlas : GutMastCellMechanismRouteAtlas
canonicalGutMastCellMechanismRouteAtlas = gut-mast-cell-mechanism-route-atlas
  (quailAlbumenPAR2Route ∷ microbialHistamineH4Route ∷ fecalLPSTLR4Route ∷ histamineH1TRPV1Route ∷ [])
  true refl true refl true refl true refl
