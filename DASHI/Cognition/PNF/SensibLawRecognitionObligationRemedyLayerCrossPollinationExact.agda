module DASHI.Cognition.PNF.SensibLawRecognitionObligationRemedyLayerCrossPollinationExact where

------------------------------------------------------------------------
-- FACT -> LEGAL STATUS -> LEGAL OBLIGATION -> AVAILABLE REMEDY
--
-- Cross-domain topology only. Pabai, the 2024 ICJ Palestine advisory opinion,
-- and Mabo are not the same doctrine, forum, source type, or remedial system.
-- They are compared only for the non-collapse of recognition and remedy layers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.SensibLawPabaiRecognitionRemedyGapExact as Pabai
import DASHI.Cognition.PNF.SensibLawInternationalObligationDomesticRemedyTranslationExact as Intl
import DASHI.Cognition.PNF.SensibLawMaboRecognitionCreationFootholdExact as Mabo
import DASHI.Cognition.PNF.SensibLawReopenableRelationalAuthorityExact as Rel

data FactAutomaticallyCreatesLegalStatus : Set where
data LegalStatusAutomaticallyCreatesLegalObligation : Set where
data LegalObligationAutomaticallyCreatesAvailableRemedy : Set where
data AvailableRemedyAutomaticallyCreatesRealisedRepair : Set where

factDoesNotAutoCreateStatus : FactAutomaticallyCreatesLegalStatus → ⊥
factDoesNotAutoCreateStatus ()

statusDoesNotAutoCreateObligation : LegalStatusAutomaticallyCreatesLegalObligation → ⊥
statusDoesNotAutoCreateObligation ()

obligationDoesNotAutoCreateRemedy : LegalObligationAutomaticallyCreatesAvailableRemedy → ⊥
obligationDoesNotAutoCreateRemedy ()

remedyDoesNotAutoCreateRealisedRepair : AvailableRemedyAutomaticallyCreatesRealisedRepair → ⊥
remedyDoesNotAutoCreateRealisedRepair ()

pabaiRecognitionStillDoesNotCreateNegligenceRemedy :
  Pabai.FactRecognitionImpliesRemedy → ⊥
pabaiRecognitionStillDoesNotCreateNegligenceRemedy =
  Pabai.factRecognitionDoesNotCreateRemedy

icjObligationStillDoesNotAutoCreateAustralianCauseOfAction :
  Intl.InternationalObligationAutomaticallyCreatesDomesticCauseOfAction → ⊥
icjObligationStillDoesNotAutoCreateAustralianCauseOfAction =
  Intl.internationalObligationDoesNotAutoCreateDomesticAction

icjTranslationGapDoesNotEraseInternationalObligation :
  Intl.NoAutomaticDomesticRemedyMeansInternationalLawHasNoTeeth → ⊥
icjTranslationGapDoesNotEraseInternationalObligation =
  Intl.translationGapDoesNotEraseInternationalObligation

maboDoesNotNeedNewLegislativeRightForRecognition :
  Mabo.newLegislativeRightRequiredForRecognition Mabo.canonicalMaboFoothold ≡ false
maboDoesNotNeedNewLegislativeRightForRecognition = refl

noCommonLawDutyStillDoesNotEraseOtherNormativeOrders :
  Rel.NoCommonLawDutyMeansNoRelationalObligation → ⊥
noCommonLawDutyStillDoesNotEraseOtherNormativeOrders =
  Rel.noCommonLawDutyDoesNotEraseOtherObligationSystems

data PabaiEqualsICJDoctrine : Set where
data MaboEqualsPabaiDoctrine : Set where
data MaboEqualsICJDoctrine : Set where

pabaiNotICJ : PabaiEqualsICJDoctrine → ⊥
pabaiNotICJ ()

maboNotPabai : MaboEqualsPabaiDoctrine → ⊥
maboNotPabai ()

maboNotICJ : MaboEqualsICJDoctrine → ⊥
maboNotICJ ()
