module DASHI.Education.DigitalESDStudyClaimPilotExtensionRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Education.DigitalESDStudyClaimPilotExtensionExact as Ext
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDCurrentScholarlySnowballExact as Sources
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

holstSourceRegression :
  Ceiling.StudyClaimProfile.source Ext.holstPilotProfile
  ≡ Sources.holstSDG47MonitoringSource
holstSourceRegression = refl

holstDocumentCorpusNRegression :
  Ceiling.StudyClaimProfile.enrolledOrReportedN Ext.holstPilotProfile
  ≡ Ceiling.explicitlyReportedNat 11061 "latest cumulative monitoring corpus; Methods 3.1"
holstDocumentCorpusNRegression = refl

holstClaimRegression :
  Ceiling.StudyClaimProfile.strongestSupportedClaim Ext.holstPilotProfile
  ≡ Ceiling.implicationConeClaim Cone.restatesMeasuredResult
holstClaimRegression = refl

fishlockSourceRegression :
  Ceiling.StudyClaimProfile.source Ext.fishlockPilotProfile
  ≡ Acquisition.fishlockRightToRepairEducationSource
fishlockSourceRegression = refl

fishlockRegisteredNRegression :
  Ceiling.StudyClaimProfile.enrolledOrReportedN Ext.fishlockPilotProfile
  ≡ Ceiling.explicitlyReportedNat 40 "registered first-year students in the module"
fishlockRegisteredNRegression = refl

fishlockSurveyNRegression :
  Ext.fishlockSurveyAnalysisN
  ≡ Ceiling.explicitlyReportedNat 14 "anonymous questionnaire respondents"
fishlockSurveyNRegression = refl

fishlockFocusGroupNRegression :
  Ext.fishlockFocusGroupAnalysisN
  ≡ Ceiling.explicitlyReportedNat 5 "focus-group participants"
fishlockFocusGroupNRegression = refl

colladoSourceRegression :
  Ceiling.StudyClaimProfile.source Ext.colladoPilotProfile
  ≡ Acquisition.colladoLongitudinalESDSource
colladoSourceRegression = refl

colladoClaimRegression :
  Ceiling.StudyClaimProfile.strongestSupportedClaim Ext.colladoPilotProfile
  ≡ Ceiling.implicationConeClaim Cone.associatesTreatmentAndOutcome
colladoClaimRegression = refl

colladoSampleDebtRegression :
  Ceiling.StudyClaimProfile.enrolledOrReportedN Ext.colladoPilotProfile
  ≡ Ceiling.natNotReported "exact enrolled/group sample counts not recovered from currently accessible same-object publisher/repository text"
colladoSampleDebtRegression = refl
