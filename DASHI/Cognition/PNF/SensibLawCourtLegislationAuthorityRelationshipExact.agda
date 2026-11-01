module DASHI.Cognition.PNF.SensibLawCourtLegislationAuthorityRelationshipExact where

------------------------------------------------------------------------
-- COURT / PARLIAMENT / CONSTITUTION / COMMON-LAW RELATIONSHIP
--
-- This module represents the user's diagram without collapsing institutional
-- functions. It does not assert that courts may generally order Parliament to
-- enact legislation, nor that every desired reform is judicially unavailable.
--
-- Stable legal sources:
--   * Commonwealth of Australia Constitution Act, ss 51, 71, 72, 75-76, 109;
--     canonical text: https://www.legislation.gov.au/C2004Q00685/latest/text
--   * Mabo v Queensland (No 1) [1988] HCA 69; 166 CLR 186.
--   * Mabo v Queensland (No 2) [1992] HCA 23; 175 CLR 1.
--   * Native Title Act 1993 (Cth), C2004A04665.
--   * Donoghue v Stevenson [1932] AC 562, common-law development calibration.
--
-- The relation graph is DASHI reconstruction of institutional interactions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge
import DASHI.Cognition.PNF.SensibLawMaboRecognitionCreationFootholdExact as Mabo

constitutionAuthority : Edge.SourceIdentity
constitutionAuthority = Edge.source-identity
  "Parliament of the United Kingdom / Australian constitutional order"
  "Commonwealth of Australia Constitution Act"
  "C2004Q00685; https://www.legislation.gov.au/C2004Q00685/latest/text"
  Edge.constitutionalText

data Institution : Set where
  constitution : Institution
  parliament : Institution
  court : Institution
  executive : Institution
  commonLaw : Institution
  statuteBook : Institution


data InstitutionalRelationKind : Set where
  grantsOrLimitsPower : InstitutionalRelationKind
  legislates : InstitutionalRelationKind
  interprets : InstitutionalRelationKind
  applies : InstitutionalRelationKind
  invalidatesForConstitutionalInconsistency : InstitutionalRelationKind
  developsCommonLaw : InstitutionalRelationKind
  modifiesOrDisplacesCommonLaw : InstitutionalRelationKind
  systematisesRecognisedRight : InstitutionalRelationKind
  supervisesByAppeal : InstitutionalRelationKind


record InstitutionalRelation : Set where
  constructor institutional-relation
  field
    from : Institution
    to : Institution
    relation : InstitutionalRelationKind
    proposition : String
    authority : Edge.SourceIdentity
    directSourceProposition : Bool
    dashStructuralSummary : Bool

open InstitutionalRelation public

constitutionLimitsParliament : InstitutionalRelation
constitutionLimitsParliament = institutional-relation
  constitution parliament grantsOrLimitsPower
  "legislative power is constitutionally constituted and limited"
  constitutionAuthority true false

parliamentLegislates : InstitutionalRelation
parliamentLegislates = institutional-relation
  parliament statuteBook legislates
  "Parliament enacts legislation within constitutional power"
  constitutionAuthority true false

courtsInterpretAndApply : InstitutionalRelation
courtsInterpretAndApply = institutional-relation
  court statuteBook interprets
  "courts interpret and apply enacted law in cases within judicial power"
  constitutionAuthority false true

courtsDevelopCommonLaw : InstitutionalRelation
courtsDevelopCommonLaw = institutional-relation
  court commonLaw developsCommonLaw
  "courts state, distinguish and legitimately develop common-law rules"
  Edge.donoghueAuthority false true

statutesMayModifyCommonLaw : InstitutionalRelation
statutesMayModifyCommonLaw = institutional-relation
  parliament commonLaw modifiesOrDisplacesCommonLaw
  "valid applicable legislation may modify or displace common-law rules"
  constitutionAuthority false true

maboNo1ConstitutionalCheck : InstitutionalRelation
maboNo1ConstitutionalCheck = institutional-relation
  constitution statuteBook invalidatesForConstitutionalInconsistency
  "Mabo (No 1) is a calibration of statutory validity/inconsistency rather than common-law native-title recognition"
  Mabo.maboNo1Authority true false

nativeTitleActAfterMabo : InstitutionalRelation
nativeTitleActAfterMabo = institutional-relation
  parliament commonLaw systematisesRecognisedRight
  "the Native Title Act created a statutory system around the post-Mabo recognition architecture"
  Edge.nativeTitleActAuthority false true

------------------------------------------------------------------------
-- Availability of a judicial route depends on an existing legal foothold.
------------------------------------------------------------------------

data FootholdKind : Set where
  constitutionalFoothold : FootholdKind
  statutoryConstructionFoothold : FootholdKind
  commonLawRecognitionFoothold : FootholdKind
  incrementalCommonLawFoothold : FootholdKind
  noCurrentJudicialFootholdShown : FootholdKind


record JudicialRouteAvailability : Set where
  constructor judicial-route-availability
  field
    target : String
    foothold : FootholdKind
    source : Edge.SourceIdentity
    alreadyAvailable : Bool
    legislationNecessaryForThisExactRoute : Bool
    legislationNecessityProved : Bool

open JudicialRouteAvailability public

maboRouteAvailability : JudicialRouteAvailability
maboRouteAvailability = judicial-route-availability
  "recognition/survival of pre-existing native title"
  commonLawRecognitionFoothold
  Edge.maboAuthority
  true false true

climateRouteAvailability : JudicialRouteAvailability
climateRouteAvailability = judicial-route-availability
  "candidate broad Commonwealth climate-policy negligence duty"
  noCurrentJudicialFootholdShown
  Edge.pabaiAuthority
  false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data StrongNormativeArgumentMeansExistingLegalObligation : Set where
data CourtCanGenerallyCommandParliamentToLegislate : Set where
data FailedCurrentJudicialRouteProvesLegislationNecessaryForAllReformulations : Set where
data CourtDevelopmentAndLegislationAreSameOperation : Set where

normativeArgumentDoesNotCreateCurrentLaw : StrongNormativeArgumentMeansExistingLegalObligation → ⊥
normativeArgumentDoesNotCreateCurrentLaw ()

noGeneralParliamentCommandEncoded : CourtCanGenerallyCommandParliamentToLegislate → ⊥
noGeneralParliamentCommandEncoded ()

failedRouteDoesNotUniversaliseLegislationNecessity :
  FailedCurrentJudicialRouteProvesLegislationNecessaryForAllReformulations → ⊥
failedRouteDoesNotUniversaliseLegislationNecessity ()

courtAndParliamentRemainDifferentProducers : CourtDevelopmentAndLegislationAreSameOperation → ⊥
courtAndParliamentRemainDifferentProducers ()
