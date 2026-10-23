module DASHI.Cognition.PsychotronicsSuccorAttributionRegression where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Cognition.PsychotronicsSuccorSourceAtlasExact as Atlas

------------------------------------------------------------------------
-- Definitional regressions for a historical source atlas, NOT an empirical
-- test and NOT a substitute for an Agda kernel check at the branch head.
------------------------------------------------------------------------

croftCoUseIsOnlyAnAttributedReport :
  Atlas.relationClass Atlas.croftCloudbusterRelation ≡
  Atlas.reportedCoUseByActor
croftCoUseIsOnlyAnAttributedReport = refl

lakhovskyIsOnlyAnalogy :
  Atlas.relationClass Atlas.lakhovskyCopperRelation ≡
  Atlas.hardwareAnalogyOnly
lakhovskyIsOnlyAnalogy = refl

gatewayMatrixIsOnlyTextualAnalogy :
  Atlas.relationClass Atlas.gatewayTimelineRelation ≡
  Atlas.thematicResemblanceOnly
gatewayMatrixIsOnlyTextualAnalogy = refl

mayAndJulyAreSameAuthorialRoot :
  Atlas.root Atlas.croftReportedEntities ≡
  Atlas.root Atlas.croftCircuitDescription
mayAndJulyAreSameAuthorialRoot = refl

julyAndAnthologyAreSameAuthorialRoot :
  Atlas.root Atlas.croftCircuitDescription ≡
  Atlas.root Atlas.croftCoLocatedDevice
julyAndAnthologyAreSameAuthorialRoot = refl

patentCannotImportProof :
  Attribution.citationImportsProof Atlas.lakhovskyPatent ≡ false
patentCannotImportProof =
  Atlas.allSourcesRemainNonPromoting Atlas.lakhovskyPatent

armyReportCannotCreateAuthority :
  Attribution.citationCreatesAuthority Atlas.gateway1983 ≡ false
armyReportCannotCreateAuthority =
  Atlas.allSourcesRemainNonAuthoritative Atlas.gateway1983

museumArticleCannotCreateAuthority :
  Attribution.citationCreatesAuthority Atlas.reichMuseum ≡ false
museumArticleCannotCreateAuthority =
  Atlas.allSourcesRemainNonAuthoritative Atlas.reichMuseum

croftLinkDoesNotCreateNewPhysics :
  Atlas.newPhysicsEstablished Atlas.croftCloudbusterRelation ≡ false
croftLinkDoesNotCreateNewPhysics = refl

gatewaySimilarityDoesNotProveTransmission :
  Atlas.historicalTransmissionProved Atlas.gatewayTimelineRelation ≡ false
gatewaySimilarityDoesNotProveTransmission = refl

archiveIsNotAnIndependentCroftReplication :
  Atlas.root Atlas.croftCoLocatedDevice ≡ Atlas.croftAuthorRoot
archiveIsNotAnIndependentCroftReplication = refl
