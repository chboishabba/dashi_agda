module DASHI.ComputerScience.FlyChlorpyrifosMultigenerationSourceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity

------------------------------------------------------------------------
-- CHLORPYRIFOS MULTIGENERATION DROSOPHILA SOURCE
--
-- Sharma & Mohanty 2025 is retained as a longitudinal pesticide-exposure
-- manifestation rather than flattened into a generic chlorpyrifos endpoint.
-- The source reports oral exposure, fecundity/development/lifespan/locomotion,
-- tissue observations and a generation-dependent attenuation of adverse effects.
-- DASHI does not reinterpret that attenuation as absence of toxicity or prove a
-- molecular resistance mechanism beyond the paper's own experimental framing.
------------------------------------------------------------------------

source : Attribution.AttributedSource
source =
  Attribution.mkDOISource
    "Sharma and Mohanty"
    "Sublethal and transgenerational effects of chlorpyrifos on various biological parameters of Drosophila melanogaster"
    "The Journal of Basic and Applied Zoology"
    "2025"
    "10.1186/s41936-025-00452-7"
    "https://link.springer.com/article/10.1186/s41936-025-00452-7"
    Attribution.academicArticleSource
    "pays only the source-defined oral chlorpyrifos exposure, F1/F10 longitudinal comparisons, life-history, locomotor, tissue and histological observations"
    Attribution.publicAttribution

sourceReceipt : Snowball.SourceRoleSnowballReceipt source
sourceReceipt = Snowball.canonicalSourceRoleSnowballReceipt source

articleQid : Identity.ExternalIdentityDemand
articleQid =
  Identity.mkOptionalIdentityDemand
    "Fly chlorpyrifos longitudinal attribution"
    "Sharma-Mohanty 2025 article Wikidata identity"
    "Sublethal and transgenerational effects of chlorpyrifos on various biological parameters of Drosophila melanogaster"
    Identity.wikidataQid
    (Identity.unresolved "article-level QID not independently verified")

drosophilaQid : Identity.ExternalIdentityDemand
drosophilaQid =
  Identity.mkOptionalIdentityDemand
    "Fly chlorpyrifos longitudinal attribution"
    "Drosophila melanogaster taxon identity"
    "Drosophila melanogaster"
    Identity.wikidataQid
    (Identity.verified "Wikidata" "Q130888")

data LongitudinalGenerationRole : Set where
  firstGenerationObservation : LongitudinalGenerationRole
  tenthGenerationObservation : LongitudinalGenerationRole

data LongitudinalEndpoint : Set where
  fecundityEndpoint
  developmentalDurationEndpoint
  locomotorEndpoint
  lifespanEndpoint
  gutMalpighianEndpoint
  larvalBrainHistologyEndpoint : LongitudinalEndpoint

record ChlorpyrifosLongitudinalObservation : Set where
  constructor chlorpyrifos-longitudinal-observation
  field
    generationRole : LongitudinalGenerationRole
    exposureDefinition : String
    endpoint : LongitudinalEndpoint
    sourceLocator : String
    sourceBoundedReading : String
open ChlorpyrifosLongitudinalObservation public

f1FecundityObservation : ChlorpyrifosLongitudinalObservation
f1FecundityObservation = chlorpyrifos-longitudinal-observation
  firstGenerationObservation
  "oral chlorpyrifos; source first established LC50 from 0.5-5 ppm and then selected two sublethal concentrations"
  fecundityEndpoint
  "Sharma & Mohanty 2025 Results / F1 exposure comparisons"
  "source reports significantly lower fecundity under the tested chlorpyrifos conditions"

f10LongitudinalObservation : ChlorpyrifosLongitudinalObservation
f10LongitudinalObservation = chlorpyrifos-longitudinal-observation
  tenthGenerationObservation
  "continued source-defined chlorpyrifos exposure through the longitudinal experiment"
  locomotorEndpoint
  "Sharma & Mohanty 2025 F10 comparison"
  "source reports adverse effects were less severe after ten generations and interprets this in terms of developed resistance"

------------------------------------------------------------------------
-- WrongType / longitudinal firewalls.
------------------------------------------------------------------------

data F10AttenuationEqualsNoToxicity : Set where
data LongitudinalAttenuationProvesMolecularMechanism : Set where
data SameDoseMakesGenerationsExchangeable : Set where
data NeuralHistologyEqualsBehaviour : Set where

afterTenGenerationsDoesNotMeanNoToxicity : F10AttenuationEqualsNoToxicity → ⊥
afterTenGenerationsDoesNotMeanNoToxicity ()

attenuationDoesNotByItselfProveMolecularMechanism :
  LongitudinalAttenuationProvesMolecularMechanism → ⊥
attenuationDoesNotByItselfProveMolecularMechanism ()

sameDoseDoesNotMakeGenerationsExchangeable : SameDoseMakesGenerationsExchangeable → ⊥
sameDoseDoesNotMakeGenerationsExchangeable ()

neuralHistologyDoesNotEqualBehaviour : NeuralHistologyEqualsBehaviour → ⊥
neuralHistologyDoesNotEqualBehaviour ()

record FlyChlorpyrifosMultigenerationBoundary : Set where
  constructor fly-chlorpyrifos-multigeneration-boundary
  field
    oralExposurePaid : Bool
    multigenerationRoleRetained : Bool
    neuralReproductiveLifeHistoryCoordinatesSeparated : Bool
    articleQidMayRemainUnresolved : Bool
    generationRoleCanBeErased : Bool
    adaptationEqualsNoToxicity : Bool
    attenuationProvesMolecularResistanceMechanism : Bool
    citationCreatesAuthority : Bool
open FlyChlorpyrifosMultigenerationBoundary public

canonicalFlyChlorpyrifosMultigenerationBoundary : FlyChlorpyrifosMultigenerationBoundary
canonicalFlyChlorpyrifosMultigenerationBoundary =
  fly-chlorpyrifos-multigeneration-boundary
    true true true true
    false false false false
