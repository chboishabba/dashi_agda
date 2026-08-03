module DASHI.Culture.Cuisine.CuisineFormalismTests where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Culture.Cuisine.QualitativeSensoryCore as Q
import DASHI.Culture.Cuisine.DishIdentityLineageCore as D
import DASHI.Culture.Cuisine.CompositionProvenanceCore as C
import DASHI.Culture.Cuisine.CuisineFormalismBundle as B
import DASHI.Culture.Cuisine.ControlledSuccessCore as Success
import DASHI.Culture.Cuisine.CuisineKnowledgeEcology as Ecology
import DASHI.Culture.Cuisine.CuisineKnowledgeSourceAtlas as Sources
import DASHI.Culture.Cuisine.MoleProcessArchitecture as Process
import DASHI.Culture.Cuisine.SituatedMoleWorld as Situated
import DASHI.Culture.Preservation.ControlledDisclosureCore as Disclosure

------------------------------------------------------------------------
-- Focused regression witnesses for the nontrivial finite parts.
------------------------------------------------------------------------

umamiInteractionRegression :
  Q.interactionTerm Q.kombuKatsuobushiUmami ≡ 6
umamiInteractionRegression = refl

umamiCombinedRegression :
  Q.combinedIntensity Q.kombuKatsuobushiUmami ≡ 11
umamiCombinedRegression = refl

dashiProfileUmamiRegression :
  Q.tasteIntensity Q.dashiSensoryProfile Q.umami ≡ 11
dashiProfileUmamiRegression = refl

funkReadingContextRegression :
  Q.firstReading Q.fermentedFunkDivergentReading ≡ Q.trainedFunkReading
funkReadingContextRegression = refl

funkSafetySeparationRegression :
  Q.safetyStatus (Q.firstBoundary Q.sameFunkCueDifferentSafety) ≡ Q.safetyVerified
funkSafetySeparationRegression = refl

carbonaraCreamClassificationRegression :
  D.classify D.carbonaraCandidateEnvelope D.cream ≡ D.canonicallyExcluded
carbonaraCreamClassificationRegression = refl

proteinCompositionRegression :
  C.totalAmount C.proteinCompositionExample ≡ 12
proteinCompositionRegression = refl

mornayPathRegression : D.SaucePath D.bechamel D.mornay
mornayPathRegression = D.mornayDerivesFromBechamel

bordelaisePathRegression : D.SaucePath D.espagnole D.bordelaise
bordelaisePathRegression = D.bordelaiseDerivesFromEspagnole

nonCollapseRegression : B.CuisineNonCollapse
nonCollapseRegression = B.canonicalCuisineNonCollapse

------------------------------------------------------------------------
-- Situated-mole, attribution, controlled-success and preservation regressions.
------------------------------------------------------------------------

sourceCountRegression :
  Sources.canonicalCuisineKnowledgeSourceCount ≡ 22
sourceCountRegression = refl

castilloDOIDoesNotCreateAuthority :
  Source.citationCreatesAuthority Sources.castilloCisnerosEnMiMeroMole
  ≡ false
castilloDOIDoesNotCreateAuthority = refl

fryThenRehydrateRouteRegression :
  Process.ProcessRoute
    Process.rawChileState
    Process.friedThenRehydratedChileState
fryThenRehydrateRouteRegression = Process.fryThenRehydrateRoute

rehydrateThenFryRouteRegression :
  Process.ProcessRoute
    Process.rawChileState
    Process.rehydratedThenFriedChileState
rehydrateThenFryRouteRegression = Process.rehydrateThenFryRoute

candidateMoleRouteRegression :
  Process.ProcessRoute
    Process.rawComponentAssemblyState
    Process.serviceStableMoleState
candidateMoleRouteRegression = Process.canonicalCandidateMoleRoute

permanentSuspensionBlockedRegression :
  Process.permanentSuspensionClaim Process.canonicalCandidateMultiphaseMole
  ≡ false
permanentSuspensionBlockedRegression = refl

plateInverseBlockedRegression :
  Situated.completeInverseFromPlateClaim Situated.canonicalSituatedMoleWorld
  ≡ false
plateInverseBlockedRegression = refl

patternMindUniversalismBlockedRegression :
  Situated.patternMindUniversalClaim
    Situated.canonicalRelationalCrossPollination
  ≡ false
patternMindUniversalismBlockedRegression = refl

highPublicationRiskFailsClosedRegression :
  Success.publicationDecision Success.highPublicationRisk
  ≡ Success.abstainDecision
highPublicationRiskFailsClosedRegression = refl

unknownPublicationRiskFailsClosedRegression :
  Success.publicationDecision Success.unknownPublicationRisk
  ≡ Success.abstainDecision
unknownPublicationRiskFailsClosedRegression = refl

controlledPublicationRiskIsLimitedRegression :
  Success.publicationDecision Success.controlledPublicationRisk
  ≡ Success.limitedProjectionDecision
controlledPublicationRiskIsLimitedRegression = refl

publicProjectionIsGeneratedRegression :
  Ecology.candidateCuisinePublicArtifact
  ≡ Disclosure.buildProjection
      Ecology.candidateCuisineProjectionPolicy
      Ecology.candidateCuisineArchive
publicProjectionIsGeneratedRegression = refl

archivePublicDistinctionRegression :
  Ecology.archiveIsNotPublicViewClaim Ecology.canonicalCuisineKnowledgeEcology
  ≡ true
archivePublicDistinctionRegression = refl
