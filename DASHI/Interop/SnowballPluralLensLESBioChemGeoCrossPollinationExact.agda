module DASHI.Interop.SnowballPluralLensLESBioChemGeoCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SnowballPluralLensInvariantExact as Snowball
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Attribution
import DASHI.Core.SnowballAtomWrongTypeScaleInvariantExact as Scale
import DASHI.Core.IntersectionalNonFactorability as INF

import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as TwoEyed
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as Kimmerer
import DASHI.Wikimedia.IbrahimTwoEyedZizekLacanIrigarayMaboWoogarooExact as Critical

import DASHI.Environment.LESSituatedSocioEcologicalHyperfabricExact as LES
import DASHI.Environment.LESCountryExternalityRealisationExact as LESCountry
import DASHI.Biology.DeepTimeCarbonBiosphereFossilFuelBidiExact as Biology
import DASHI.Chemistry.DeepTimeCarbonReservoirFluxBalanceExact as Chemistry
import DASHI.Geology.SaltGeochemistryExact as Geology
import DASHI.Law.SensibLawWoogarooAdmissibleFactorsWrongTypeAtomBridgeExact as Woogaroo

------------------------------------------------------------------------
-- CROSS-DOMAIN SNOWBALL PLURAL-LENS OWNER
--
-- This module does NOT define a universal list of axes.  Each consumer/domain
-- supplies its own Axis type and PluralLens.  The only global requirement is:
-- whenever a locally relevant distinction is admitted, every later projection
-- that claims adequacy for that consumer/query must retain it or explicitly
-- reopen the residual.
--
-- LES, biology, chemistry and geology are therefore finite witnesses of the
-- same abstract discipline, not templates whose current coordinate lists are
-- declared complete.
------------------------------------------------------------------------

record DomainLensInstantiation : Set₁ where
  constructor domain-lens-instantiation
  field
    domainName : String
    Axis : Set
    lens : Snowball.PluralLens Axis
    discoveryAdmissionReference : String
    attributionReference : String
    atomScaleReference : String
    factorsThroughAuditReference : String
    presentAxisVocabularyClaimedComplete : Bool
    presentAxisVocabularyClaimedCompleteIsFalse :
      presentAxisVocabularyClaimedComplete ≡ false

open DomainLensInstantiation public

retainsEveryAdmittedRelevantAxis :
  (D : DomainLensInstantiation) →
  (axis : Axis D) →
  Snowball.relevant (lens D) axis ≡ true →
  Snowball.retained (lens D) axis ≡ true
retainsEveryAdmittedRelevantAxis D =
  Snowball.relevantIsRetained (lens D)

------------------------------------------------------------------------
-- Cross-domain methodological roles.  These are operators/diagnostics, not
-- mutually reducible theories and not source-authority transfers.
------------------------------------------------------------------------

record PluralMethodFamily : Set where
  constructor plural-method-family
  field
    twoEyedCoordinationRetained : Bool
    ideologyFrameInspectionRetained : Bool
    lacanianSubjectPositionRetained : Bool
    irigarayGrammarDifferenceRetained : Bool
    maboRecognitionCreationDistinctionRetained : Bool
    woogarooConsumerIndexedAtomRoutingRetained : Bool
    intersectionalNonFactorabilityRetained : Bool
    attributionProvenanceRetained : Bool
    methodsCollapsedToSingleMasterLens : Bool
    methodsCollapsedToSingleMasterLensIsFalse :
      methodsCollapsedToSingleMasterLens ≡ false

open PluralMethodFamily public

canonicalPluralMethodFamily : PluralMethodFamily
canonicalPluralMethodFamily =
  plural-method-family
    true true true true true true true true false refl

------------------------------------------------------------------------
-- LES is the strongest already-constructed finite regression: its current
-- coarse observation cannot recover the full planning signature, and separate
-- witnesses establish that history, ecological relation, provenance and
-- justice can each remain essential.  Snowball reads those witnesses as
-- DISCOVERY receipts, not as a closed universal axis vocabulary.
------------------------------------------------------------------------

lesCoarseProjectionStillNonFactorising :
  INF.FactorsThrough LES.fullCoarseObservation LES.fullPlanningSignature → ⊥
lesCoarseProjectionStillNonFactorising =
  LES.fullCoarseSummaryCannotRecoverFullPlanningSignature

record LESAsSnowballWitness : Set where
  constructor les-as-snowball-witness
  field
    existingFactorsThroughDefectReused : Bool
    historyWitnessMayDiscoverAxis : Bool
    relationWitnessMayDiscoverAxis : Bool
    provenanceWitnessMayDiscoverAxis : Bool
    justiceWitnessMayDiscoverAxis : Bool
    thoseFourAxesClaimedUniversallyComplete : Bool
    thoseFourAxesClaimedUniversallyCompleteIsFalse :
      thoseFourAxesClaimedUniversallyComplete ≡ false
    predictionAdequacySeparateFromAuthority : Bool

canonicalLESAsSnowballWitness : LESAsSnowballWitness
canonicalLESAsSnowballWitness =
  les-as-snowball-witness true true true true true false refl true

------------------------------------------------------------------------
-- Biology / chemistry / geology: preserve semantic scale and history.
--
-- The same carbon/material carrier can be observed as biological history,
-- reservoir/flux chemistry, geological provenance, industrial feedstock or
-- socio-ecological consequence.  None of those projections is globally the
-- atom for all consumers.  A later consumer may force another coordinate to
-- snowball if its answer does not factor through the current projection.
------------------------------------------------------------------------

record BioChemGeoScaleBoundary : Set where
  constructor bio-chem-geo-scale-boundary
  field
    biologicalHistoryIsChemicalStateIdentity : Bool
    biologicalHistoryIsChemicalStateIdentityIsFalse :
      biologicalHistoryIsChemicalStateIdentity ≡ false
    chemicalReservoirIsGeologicalProvenanceIdentity : Bool
    chemicalReservoirIsGeologicalProvenanceIdentityIsFalse :
      chemicalReservoirIsGeologicalProvenanceIdentity ≡ false
    geologyIsOnlyCurrentChemistry : Bool
    geologyIsOnlyCurrentChemistryIsFalse :
      geologyIsOnlyCurrentChemistry ≡ false
    currentMaterialStateExhaustsDeepTimeHistory : Bool
    currentMaterialStateExhaustsDeepTimeHistoryIsFalse :
      currentMaterialStateExhaustsDeepTimeHistory ≡ false
    domainSpecificAtomsMayDifferByConsumer : Bool
    missingRelevantScaleMustSnowball : Bool
    sourceRoleMustSurviveScaleChangeWhenRelevant : Bool

open BioChemGeoScaleBoundary public

canonicalBioChemGeoScaleBoundary : BioChemGeoScaleBoundary
canonicalBioChemGeoScaleBoundary =
  bio-chem-geo-scale-boundary
    false refl
    false refl
    false refl
    false refl
    true true true

------------------------------------------------------------------------
-- Country / Mabo / Woogaroo regression over the physical domains.
--
-- Physical knowledge about habitat, water, soil, species, carbon, salt or
-- geology may be necessary for a consumer while remaining insufficient for
-- legal/custodial authority.  Conversely, legal recognition cannot fabricate
-- the physical process.  The plural lens carries both if the query needs both.
------------------------------------------------------------------------

record CountryPhysicalAuthorityBoundary : Set where
  constructor country-physical-authority-boundary
  field
    physicalEvidenceCreatesCustodialAuthority : Bool
    physicalEvidenceCreatesCustodialAuthorityIsFalse :
      physicalEvidenceCreatesCustodialAuthority ≡ false
    stateRecognitionCreatesCountryAuthority : Bool
    stateRecognitionCreatesCountryAuthorityIsFalse :
      stateRecognitionCreatesCountryAuthority ≡ false
    custodialAuthorityDeterminesChemicalMechanism : Bool
    custodialAuthorityDeterminesChemicalMechanismIsFalse :
      custodialAuthorityDeterminesChemicalMechanism ≡ false
    habitatObservationAlonePaysEveryLegalConsumer : Bool
    habitatObservationAlonePaysEveryLegalConsumerIsFalse :
      habitatObservationAlonePaysEveryLegalConsumer ≡ false
    joinedConsumerMayRequireBothPhysicalAndAuthorityAxes : Bool

open CountryPhysicalAuthorityBoundary public

canonicalCountryPhysicalAuthorityBoundary : CountryPhysicalAuthorityBoundary
canonicalCountryPhysicalAuthorityBoundary =
  country-physical-authority-boundary
    false refl false refl false refl false refl true

woogarooSpeciesPresenceStillCannotPayNCA13 :
  INF.FactorsThrough Woogaroo.projectThreatenedSpeciesPresence Woogaroo.nca13Answer → ⊥
woogarooSpeciesPresenceStillCannotPayNCA13 =
  Woogaroo.speciesPresenceCannotFactorToNCA13

------------------------------------------------------------------------
-- Global execution rule for the Dewey/Wikipedia pass.
------------------------------------------------------------------------

record DeweyWikiSnowballPassInvariant : Set where
  constructor dewey-wiki-snowball-pass-invariant
  field
    categoryTraversalMayDiscoverCandidateAxis : Bool
    wikipediaParentageCreatesAxisAuthority : Bool
    wikipediaParentageCreatesAxisAuthorityIsFalse :
      wikipediaParentageCreatesAxisAuthority ≡ false
    sourceAttributionMayGateAdmission : Bool
    factorsThroughFailureMayForceRefinement : Bool
    wrongSemanticScaleMayForceRefinement : Bool
    domainCrossPollinationMayForceRefinement : Bool
    presentNamedAxesClaimedComplete : Bool
    presentNamedAxesClaimedCompleteIsFalse :
      presentNamedAxesClaimedComplete ≡ false

open DeweyWikiSnowballPassInvariant public

canonicalDeweyWikiSnowballPassInvariant : DeweyWikiSnowballPassInvariant
canonicalDeweyWikiSnowballPassInvariant =
  dewey-wiki-snowball-pass-invariant
    true false refl true true true true false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OneDomainLensIsUniversalLens : Set where
data CrossPollinationErasesSourceRole : Set where
data PhysicalAgreementImpliesEpistemicFusion : Set where
data CurrentAxisListClosesFutureDiscovery : Set where

oneDomainLensDoesNotBecomeUniversal : OneDomainLensIsUniversalLens → ⊥
oneDomainLensDoesNotBecomeUniversal ()

crossPollinationDoesNotEraseAttribution : CrossPollinationErasesSourceRole → ⊥
crossPollinationDoesNotEraseAttribution ()

physicalAgreementDoesNotRequireEpistemicFusion :
  PhysicalAgreementImpliesEpistemicFusion → ⊥
physicalAgreementDoesNotRequireEpistemicFusion ()

currentAxisListDoesNotCloseDiscovery : CurrentAxisListClosesFutureDiscovery → ⊥
currentAxisListDoesNotCloseDiscovery ()
