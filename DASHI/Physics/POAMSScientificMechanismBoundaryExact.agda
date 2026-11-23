module DASHI.Physics.POAMSScientificMechanismBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificMechanismEvidenceBidiExact as S

------------------------------------------------------------------------
-- POAMS SCIENTIFIC CONTENT / BOUNDARY
--
-- NASA/TM-20205010911 reports a reformulation of the Pope-Osborne Angular
-- Momentum Synthesis theory, a predicted non-Newtonian spin-coupled force, and
-- rudimentary/preliminary measurements appearing consistent with that model.
-- NASA explicitly says better methodologies and measurements are needed.
------------------------------------------------------------------------

angularMomentumConservation : S.ScientificMechanismReceipt
angularMomentumConservation = S.scientific-mechanism-receipt
  "angular momentum mechanics"
  "for a closed mechanical system, change of total angular momentum is governed by external torque; internal exchanges do not create net angular momentum"
  S.establishedBackgroundLaw
  S.established
  "standard classical mechanics background used as a comparison boundary"
  "This background law does not by itself validate or refute a particular claimed anomalous-force apparatus; the system boundary and external couplings must be specified."

poamsReformulation : S.ScientificMechanismReceipt
poamsReformulation = S.scientific-mechanism-receipt
  "POAMS"
  "NASA MSFC reformulated the Pope-Osborne theory into a form predicting a non-Newtonian spin-coupled force associated with nucleon alignment"
  S.mathematicalReformulation
  S.sourceBacked
  "NASA/TM-20205010911 / M-1531"
  "This is an accurate receipt of the NASA TM's model description, not a statement that the predicted force is established physics."

poamsPreliminaryObservation : S.ScientificMechanismReceipt
poamsPreliminaryObservation = S.scientific-mechanism-receipt
  "POAMS validation experiment"
  "rudimentary and preliminary data were reported as appearing consistent with predictions of a spin-coupled force"
  S.experimentalObservation
  S.preliminary
  "NASA/TM-20205010911 abstract and experimental discussion"
  "The report itself characterises the data as rudimentary/preliminary and calls for additional carefully controlled research."

poamsSourceInterpretation : S.ScientificMechanismReceipt
poamsSourceInterpretation = S.scientific-mechanism-receipt
  "POAMS validation experiment"
  "the reported preliminary observations were interpreted by the authors as consistent with the reformulated POAMS prediction"
  S.preliminaryConsistencyClaim
  S.preliminary
  "NASA/TM-20205010911"
  "Consistency with a model is weaker than identification of the mechanism, exclusion of conventional couplings, or independent replication."

poamsNeedsIndependentReplication : S.ScientificReverseObligation
poamsNeedsIndependentReplication = S.scientific-reverse-obligation
  "POAMS spin-coupled-force claim"
  S.independentReplicationReceipt
  "recover independent experiments with explicit apparatus geometry, force/torque calibration, vibration/electromagnetic/thermal controls, uncertainty budget, blinding where applicable, and reproducible signal scaling"
  "whether an anomalous effect survives independent controlled replication"
  "the proposed spin-coupled mechanism merely from NASA authorship or preliminary consistency"

poamsNeedsMechanismWeld : S.ScientificReverseObligation
poamsNeedsMechanismWeld = S.scientific-reverse-obligation
  "POAMS spin-coupled-force claim"
  S.mechanismToObservationWeld
  "show that observed force/torque scaling follows a distinctive quantitative prediction of the nucleon-alignment model while excluding ordinary mechanical, electromagnetic, thermal and metrological couplings"
  "mechanism-specific support"
  "world-truth of the mechanism from a nonzero or suggestive measurement alone"

record CurrentPOAMSScienceAssessment : Set where
  constructor current-poams-science-assessment
  field
    reformulationSourceBacked : Bool
    reformulationSourceBackedIsTrue : reformulationSourceBacked ≡ true
    preliminaryDataReported : Bool
    preliminaryDataReportedIsTrue : preliminaryDataReported ≡ true
    independentReplicationOwned : Bool
    independentReplicationOwnedIsFalse : independentReplicationOwned ≡ false
    establishedNewForceOwned : Bool
    establishedNewForceOwnedIsFalse : establishedNewForceOwned ≡ false

canonicalCurrentPOAMSScienceAssessment : CurrentPOAMSScienceAssessment
canonicalCurrentPOAMSScienceAssessment = current-poams-science-assessment
  true refl
  true refl
  false refl
  false refl
