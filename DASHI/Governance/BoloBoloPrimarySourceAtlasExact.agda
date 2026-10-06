module DASHI.Governance.BoloBoloPrimarySourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- PRIMARY SOURCE ATLAS: p.m., bolo'bolo, 30th Anniversary Edition.
--
-- Provenance class: PRIMARY SOURCE.
-- Edition inspected: Autonomedia / Ardent Press, 2011 text,
-- ISBN 9781570272417.  The libcom-hosted PDF is a reproduction of that
-- edition.  Source claims below are attributed to p.m.; they are not DASHI
-- empirical findings and are not silently upgraded into optimality claims.
------------------------------------------------------------------------

record BoloBoloPrimarySourceAtlas : Set where
  constructor boloBoloPrimarySourceAtlas
  field
    sourceAuthor : String
    sourceTitle : String
    sourceEdition : String
    sourceISBN : String
    sourceURL : String

    boloApproximatePopulation : Nat
    kanaLowerPopulation : Nat
    kanaUpperPopulation : Nat
    boloApproximateKanaCount : Nat
    tegaLowerBoloCount : Nat
    tegaUpperBoloCount : Nat

    kanaDescribedAsFrequentSubdivision : Bool
    boloDescribedAsTooLargeForImmediateLivingTogether : Bool
    tegaDescribedAsPossibleConfederationOfBolos : Bool
    tegaDescribedAsBottomUp : Bool
    boloIndependenceDescribedAsLimitingTegaPower : Bool

    transitionRequiresCarefulEvaluation : Bool
    transitionRequiresCollectiveOrganization : Bool
    transitionRequiresAutonomousInstitutions : Bool
    automaticEscalatorToBetterFutureRejected : Bool

open BoloBoloPrimarySourceAtlas public

canonicalBoloBoloPrimarySourceAtlas : BoloBoloPrimarySourceAtlas
canonicalBoloBoloPrimarySourceAtlas =
  boloBoloPrimarySourceAtlas
    "p.m."
    "bolo'bolo"
    "30th Anniversary Edition / 2011 English text"
    "9781570272417"
    "https://files.libcom.org/files/bolo'bolo%20(30th%20Anniversary%20Edition).pdf"
    500
    15
    30
    20
    10
    20
    true
    true
    true
    true
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- Source-layer vocabulary.
--
-- This finite vocabulary is DASHI's indexing of source passages.  The labels
-- are not claimed to be the author's own formal type system.
------------------------------------------------------------------------

data SourceInstitutionalLayer : Set where
  kanaLayer : SourceInstitutionalLayer
  boloLayer : SourceInstitutionalLayer
  tegaLayer : SourceInstitutionalLayer
  broaderCoordinationLayer : SourceInstitutionalLayer

data FederatedInterpretiveRole : Set where
  nestedLivingGroupRole : FederatedInterpretiveRole
  autonomousCommunityRole : FederatedInterpretiveRole
  localConfederalCoordinationRole : FederatedInterpretiveRole
  widerCoordinationRole : FederatedInterpretiveRole

sourceLayerInterpretation : SourceInstitutionalLayer → FederatedInterpretiveRole
sourceLayerInterpretation kanaLayer = nestedLivingGroupRole
sourceLayerInterpretation boloLayer = autonomousCommunityRole
sourceLayerInterpretation tegaLayer = localConfederalCoordinationRole
sourceLayerInterpretation broaderCoordinationLayer = widerCoordinationRole

------------------------------------------------------------------------
-- Attribution firewall.
------------------------------------------------------------------------

record BoloBoloPrimarySourceBoundary : Set where
  constructor boloBoloPrimarySourceBoundary
  field
    sourceNumbersProveEmpiricalOptimality : Bool
    sourceNumbersProveUniversalHumanScale : Bool
    sourceArchitectureProvesPoliticalLegitimacy : Bool
    sourceArchitectureProvesEcologicalViability : Bool
    sourceArchitectureEqualsDASHIFederationOntology : Bool
    sourceProvidesNestedCommunityDesign : Bool
    sourceProvidesBottomUpCoordinationDesign : Bool
    sourceExplicitlyRejectsAutomaticTransitionSuccess : Bool
    dashiInterpretiveLayerMappingIsDerived : Bool

open BoloBoloPrimarySourceBoundary public

canonicalBoloBoloPrimarySourceBoundary : BoloBoloPrimarySourceBoundary
canonicalBoloBoloPrimarySourceBoundary =
  boloBoloPrimarySourceBoundary
    false
    false
    false
    false
    false
    true
    true
    true
    true

sourceBoloPopulationIsApproximate :
  boloApproximatePopulation canonicalBoloBoloPrimarySourceAtlas ≡ 500
sourceBoloPopulationIsApproximate = refl

sourceKanaRangeLower :
  kanaLowerPopulation canonicalBoloBoloPrimarySourceAtlas ≡ 15
sourceKanaRangeLower = refl

sourceKanaRangeUpper :
  kanaUpperPopulation canonicalBoloBoloPrimarySourceAtlas ≡ 30
sourceKanaRangeUpper = refl

sourceTegaRangeLower :
  tegaLowerBoloCount canonicalBoloBoloPrimarySourceAtlas ≡ 10
sourceTegaRangeLower = refl

sourceTegaRangeUpper :
  tegaUpperBoloCount canonicalBoloBoloPrimarySourceAtlas ≡ 20
sourceTegaRangeUpper = refl

canonicalBoloBoloPrimarySourceReceipt : GenericReceipt.GenericReceipt
canonicalBoloBoloPrimarySourceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo primary-source institutional atlas"
    "DASHI.Governance.BoloBoloPrimarySourceAtlasExact"
    "canonicalBoloBoloPrimarySourceBoundary"
    "records the source's approximate bolo/kana/tega scales, bottom-up coordination language, and explicit rejection of an automatic transition to a better future"
    "source numbers are proposals/descriptions rather than empirical optima; the DASHI layer-role mapping is derived and creates no legitimacy, ecological viability, or universal human-scale theorem"
    "agda -i . DASHI/Governance/BoloBoloPrimarySourceAtlasRegression.agda"
