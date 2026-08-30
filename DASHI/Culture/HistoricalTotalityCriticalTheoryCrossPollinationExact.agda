module DASHI.Culture.HistoricalTotalityCriticalTheoryCrossPollinationExact where

------------------------------------------------------------------------
-- HISTORICAL TOTALITY x CRITICAL-THEORY ATLAS CROSS-POLLINATION
--
-- This is an integration owner, not a claim that the imported philosophers
-- form one doctrine.  The Core source registry remains the authority for the
-- bounded historical/theoretical source roles.  The exact finite separation
-- and non-factorability results remain DASHI constructions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.CriticalRelationalGrammarSourceRegistryExact as Sources
import DASHI.Core.CriticalRelationalGrammarCapstoneExact as Critical
import DASHI.Core.TrinhSubjectInMakingNoncollapseExact as Trinh
import DASHI.Core.LugonesPurityCurdlingNonfactorabilityExact as Lugones
import DASHI.Core.CriticalSocialEcologyObserverRegimeExact as Ecology
import DASHI.Culture.HistoricalSocialTotalityBidiExact as Totality

------------------------------------------------------------------------
-- Integration levels must remain disjoint.
------------------------------------------------------------------------

data IntegrationLevel : Set where
  historicalSourceProposition
  boundedInterpretiveBridge
  reusableFormalPattern
  finiteDASHITheorem
  empiricalPopulationClaim
  : IntegrationLevel

sourceNotTheorem : historicalSourceProposition ≡ finiteDASHITheorem → ⊥
sourceNotTheorem ()

interpretationNotEmpiricalLaw : boundedInterpretiveBridge ≡ empiricalPopulationClaim → ⊥
interpretationNotEmpiricalLaw ()

patternNotHistoricalDoctrine : reusableFormalPattern ≡ historicalSourceProposition → ⊥
patternNotHistoricalDoctrine ()

------------------------------------------------------------------------
-- Existing critical-theory theorem surfaces can constrain the totality layer
-- structurally without being re-described as historical source propositions.
------------------------------------------------------------------------

trinhPublicCategoryStillDoesNotRecoverSubjectFormation :
  INF.FactorsThrough Trinh.publicCategory Trinh.subjectFormation → ⊥
trinhPublicCategoryStillDoesNotRecoverSubjectFormation =
  Critical.trinhCategoryDoesNotRecoverSubjectFormation

lugonesCurdlingStillBlocksPureEndpointReduction :
  Lugones.PureEndpointFactorisation → ⊥
lugonesCurdlingStillBlocksPureEndpointReduction =
  Critical.lugonesAntiPureFactorisation

inclusiveReadingStillDoesNotRecoverMaterialAffordance :
  INF.FactorsThrough Ecology.feministObserver Ecology.realizedRemain → ⊥
inclusiveReadingStillDoesNotRecoverMaterialAffordance =
  Critical.inclusiveRhetoricDoesNotDetermineAccessibility

cultureStillDoesNotRecoverUniqueSubject :
  INF.FactorsThrough Totality.culturalObserver Totality.subjectRoute → ⊥
cultureStillDoesNotRecoverUniqueSubject =
  Totality.cultureCannotRecoverUniqueSubjectRoute

civilisationStillDoesNotRecoverPoliticalDestiny :
  INF.FactorsThrough Totality.civilisationalObserver Totality.politicalTrajectory → ⊥
civilisationStillDoesNotRecoverPoliticalDestiny =
  Totality.civilisationCannotRecoverPoliticalDestiny

------------------------------------------------------------------------
-- Source registry is consumed as provenance, not as proof authority.
------------------------------------------------------------------------

record CriticalTheorySourceWeld : Set where
  constructor critical-theory-source-weld
  field
    registryBoundary : Sources.RegistryBoundary
    registryBoundaryIsCanonical :
      registryBoundary ≡ Sources.canonicalRegistryBoundary
    criticalGrammarBoundary : Critical.CriticalRelationalGrammarBoundary
    criticalGrammarBoundaryIsCanonical :
      criticalGrammarBoundary ≡ Critical.canonicalCriticalRelationalGrammarBoundary
    totalityBoundary : Totality.HistoricalSocialTotalityBoundary
    totalityBoundaryIsCanonical :
      totalityBoundary ≡ Totality.canonicalHistoricalSocialTotalityBoundary
    sourcePropositionsRemainSourceBound : Bool
    sourcePropositionsRemainSourceBoundIsTrue :
      sourcePropositionsRemainSourceBound ≡ true
    formalSimilarityDoesNotMergeAuthors : Bool
    formalSimilarityDoesNotMergeAuthorsIsTrue :
      formalSimilarityDoesNotMergeAuthors ≡ true
    formalTheoremDoesNotBecomeEmpiricalClaim : Bool
    formalTheoremDoesNotBecomeEmpiricalClaimIsTrue :
      formalTheoremDoesNotBecomeEmpiricalClaim ≡ true

canonicalCriticalTheorySourceWeld : CriticalTheorySourceWeld
canonicalCriticalTheorySourceWeld =
  critical-theory-source-weld
    Sources.canonicalRegistryBoundary refl
    Critical.canonicalCriticalRelationalGrammarBoundary refl
    Totality.canonicalHistoricalSocialTotalityBoundary refl
    true refl true refl true refl

------------------------------------------------------------------------
-- Cross-philosopher non-collapse.
--
-- Shared words such as subject, other, third, void, hierarchy, difference,
-- contradiction or relation do not identify the authors' historical concepts.
------------------------------------------------------------------------

data PhilosophicalRegister : Set where
  beauvoirSubjectOther
  lacanianIdentificationDiscourse
  irigarayanRelationalDifference
  crenshawIntersectionality
  anzalduanBorderlands
  lugonesPurityCurdling
  bhabhaThirdSpace
  trinhSubjectInMaking
  badiouVoidCountAsOne
  bookchinSocialEcologyHierarchy
  : PhilosophicalRegister

beauvoirNotLacan : beauvoirSubjectOther ≡ lacanianIdentificationDiscourse → ⊥
beauvoirNotLacan ()

lacanNotIrigaray : lacanianIdentificationDiscourse ≡ irigarayanRelationalDifference → ⊥
lacanNotIrigaray ()

anzalduaNotBhabha : anzalduanBorderlands ≡ bhabhaThirdSpace → ⊥
anzalduaNotBhabha ()

badiouNotBookchin : badiouVoidCountAsOne ≡ bookchinSocialEcologyHierarchy → ⊥
badiouNotBookchin ()

------------------------------------------------------------------------
-- Boundary: atlas != synthesis != empirical history.
------------------------------------------------------------------------

record HistoricalTotalityCriticalTheoryBoundary : Set where
  constructor historical-totality-critical-theory-boundary
  field
    manyPhilosophersMaySupplyComparisonSurfaces : Bool
    sameFormalPatternMeansSameDoctrine : Bool
    sameKeywordMeansSameConcept : Bool
    theoreticalSourceProvesPopulationClaim : Bool
    criticalTheoryAloneRecoversHistoricalCause : Bool
    subjectCategoryRecoversFormationRoute : Bool
    inclusiveRhetoricRecoversMaterialAccessibility : Bool
    civilisationalIdentityRecoversPoliticalDestiny : Bool
    sourceRegistryRetainsAuthorityForAttribution : Bool

canonicalHistoricalTotalityCriticalTheoryBoundary :
  HistoricalTotalityCriticalTheoryBoundary
canonicalHistoricalTotalityCriticalTheoryBoundary =
  historical-totality-critical-theory-boundary
    true false false false false false false false true
