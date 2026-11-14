module DASHI.Culture.PowersPlantationParadiseMobilityRegimeTransitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.PowersPlantationParadisePerformerComparisonExact as Comparison
import DASHI.Culture.PowersPlantationParadiseMethodologySourceAtlasExact as Methodology

------------------------------------------------------------------------
-- MOBILITY / MULTILINGUAL / REGIME-TRANSITION SURFACE
--
-- Current same-object payments remain descriptive.  This owner records the
-- coordinates required to compare performer/repertoire continuity across
-- places and later institutional regimes without treating mobility as a causal
-- effect or transporting one colony's rules into another.
------------------------------------------------------------------------

record MobilityCoordinate : Set where
  constructor mobility-coordinate
  field
    performerReference : String
    placeReference : String
    dateReference : String
    repertoireOrRoleReference : String
    languageReference : String
    sourceReference : String
    sameObjectHistoricalReceiptPaid : Bool

open MobilityCoordinate public

minetteMobilityCoordinate : MobilityCoordinate
minetteMobilityCoordinate =
  mobility-coordinate
    "Minette"
    "Port-au-Prince"
    "documented career surface, principally 1780s"
    "concert, opera-comique and benefit-performance roles retained in existing Minette owners"
    "French-language public theatre context unless a specific source pays otherwise"
    "Prest/Camier/Colonial Networks bounded same-object reconstruction"
    true

liseMobilityCoordinate : MobilityCoordinate
liseMobilityCoordinate =
  mobility-coordinate
    "Lise"
    "Les Cayes / Léogane / Saint-Marc / Port-au-Prince"
    "documented 1780s trajectory; exact event coordinates retained where sourced"
    "includes Thérèse at Saint-Marc, 6 February 1786"
    "French/Creole repertoire questions remain event-specific and must be source-paid"
    "Prest performer-comparison owner and cited Affiches coordinate"
    true

record RegimeCoordinate : Set where
  constructor regime-coordinate
  field
    regimeReference : String
    jurisdictionReference : String
    formalRuleReference : String
    realisedPracticeReference : String
    transportReceiptRequired : Bool
    transportReceiptRequiredIsTrue : transportReceiptRequired ≡ true

open RegimeCoordinate public

preRevolutionSaintDomingueRegime : RegimeCoordinate
preRevolutionSaintDomingueRegime =
  regime-coordinate
    "pre-revolutionary Saint-Domingue public-theatre regime"
    "French Saint-Domingue"
    "local rule-producing instruments remain a current acquisition target"
    "observed theatre/seating/practice evidence is separately receipted"
    true refl

revolutionaryTransitionRegime : RegimeCoordinate
revolutionaryTransitionRegime =
  regime-coordinate
    "revolutionary-era Saint-Domingue transition"
    "Saint-Domingue under changing revolutionary institutions"
    "rule changes require exact dated source receipts"
    "changed practice cannot be inferred from revolution by label alone"
    true refl

postMigrationComparativeRegime : RegimeCoordinate
postMigrationComparativeRegime =
  regime-coordinate
    "post-Saint-Domingue comparative destination regime"
    "New Orleans / Charleston or another explicitly sourced destination"
    "destination-specific access/performance rules must be acquired independently"
    "performer/repertoire continuity does not transfer institutional conditions"
    true refl

------------------------------------------------------------------------
-- Finite non-descent fixtures.
------------------------------------------------------------------------

data RegimeComparisonState : Set where
  sameCarrierOldRegime : RegimeComparisonState
  sameCarrierNewRegime : RegimeComparisonState

data CarrierReading : Set where
  continuingPerformerRepertoire : CarrierReading

data RegimeReading : Set where
  earlierInstitutionalRegime : RegimeReading
  laterInstitutionalRegime : RegimeReading

carrierReading : RegimeComparisonState → CarrierReading
carrierReading _ = continuingPerformerRepertoire

regimeReading : RegimeComparisonState → RegimeReading
regimeReading sameCarrierOldRegime = earlierInstitutionalRegime
regimeReading sameCarrierNewRegime = laterInstitutionalRegime

regimeReadingDiffers :
  regimeReading sameCarrierOldRegime ≡ regimeReading sameCarrierNewRegime → ⊥
regimeReadingDiffers ()

carrierContinuityDoesNotRecoverRegimeContinuity :
  INF.FactorsThrough carrierReading regimeReading → ⊥
carrierContinuityDoesNotRecoverRegimeContinuity =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameCarrierOldRegime
      sameCarrierNewRegime
      refl
      regimeReadingDiffers)

data AccessComparisonState : Set where
  sameRepertoireRestrictedAccess : AccessComparisonState
  sameRepertoireExpandedAccess : AccessComparisonState

data RepertoireReading : Set where sameRepertoire : RepertoireReading
data AccessRegimeReading : Set where restrictedAccess expandedAccess : AccessRegimeReading

repertoireReading : AccessComparisonState → RepertoireReading
repertoireReading _ = sameRepertoire

accessRegimeReading : AccessComparisonState → AccessRegimeReading
accessRegimeReading sameRepertoireRestrictedAccess = restrictedAccess
accessRegimeReading sameRepertoireExpandedAccess = expandedAccess

accessRegimeDiffers :
  accessRegimeReading sameRepertoireRestrictedAccess
  ≡ accessRegimeReading sameRepertoireExpandedAccess → ⊥
accessRegimeDiffers ()

repertoireContinuityDoesNotRecoverAccessContinuity :
  INF.FactorsThrough repertoireReading accessRegimeReading → ⊥
repertoireContinuityDoesNotRecoverAccessContinuity =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameRepertoireRestrictedAccess
      sameRepertoireExpandedAccess
      refl
      accessRegimeDiffers)

------------------------------------------------------------------------
-- Attribution boundaries.
------------------------------------------------------------------------

liseEventAnchor : Comparison.PerformerEventReceipt
liseEventAnchor = Comparison.liseSaintMarc1786Receipt

methodologyBoundary : Methodology.PowersMethodologySourceBoundary
methodologyBoundary = Methodology.canonicalPowersMethodologySourceBoundary

data MobilityCreatesCausalEffect : Set where

data ComparativePromptCreatesTransportReceipt : Set where

mobilityDoesNotCreateCausalEffect : MobilityCreatesCausalEffect → ⊥
mobilityDoesNotCreateCausalEffect ()

comparativePromptDoesNotCreateTransportReceipt :
  ComparativePromptCreatesTransportReceipt → ⊥
comparativePromptDoesNotCreateTransportReceipt ()

record PowersMobilityRegimeBoundary : Set where
  constructor powers-mobility-regime-boundary
  field
    multilingualCoordinateMustBeEventSpecific : Bool
    multilingualCoordinateMustBeEventSpecificIsTrue :
      multilingualCoordinateMustBeEventSpecific ≡ true
    performerContinuityImpliesRuleContinuity : Bool
    performerContinuityImpliesRuleContinuityIsFalse :
      performerContinuityImpliesRuleContinuity ≡ false
    repertoireContinuityImpliesAccessContinuity : Bool
    repertoireContinuityImpliesAccessContinuityIsFalse :
      repertoireContinuityImpliesAccessContinuity ≡ false
    mobilityCreatesCausalEffect : Bool
    mobilityCreatesCausalEffectIsFalse : mobilityCreatesCausalEffect ≡ false
    comparativeScholarshipCreatesLocalTransportReceipt : Bool
    comparativeScholarshipCreatesLocalTransportReceiptIsFalse :
      comparativeScholarshipCreatesLocalTransportReceipt ≡ false

canonicalPowersMobilityRegimeBoundary : PowersMobilityRegimeBoundary
canonicalPowersMobilityRegimeBoundary =
  powers-mobility-regime-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
