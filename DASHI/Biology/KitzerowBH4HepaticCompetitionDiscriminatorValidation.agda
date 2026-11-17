module DASHI.Biology.KitzerowBH4HepaticCompetitionDiscriminatorValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.KitzerowBH4HepaticCompetitionDiscriminatorExact as Hepatic

sameSystemTwoBranchExperimentIsPaid :
  Hepatic.sameSystemPAHAndINOSMeasured Hepatic.canonicalHepaticCompetitionBoundary ≡ true
  × Hepatic.cellularBH4Measured Hepatic.canonicalHepaticCompetitionBoundary ≡ true
sameSystemTwoBranchExperimentIsPaid = refl , refl

strongFixedPoolCompetitionIsNotSupportedInThisHepaticContext :
  Hepatic.strongCompetitionAtAdequateSynthesisSupported Hepatic.canonicalHepaticCompetitionBoundary ≡ false
strongFixedPoolCompetitionIsNotSupportedInThisHepaticContext = refl

competitionEmergesWhenSupplyIsConstrained :
  Hepatic.conditionalCompetitionWhenBH4SynthesisBlocked Hepatic.canonicalHepaticCompetitionBoundary ≡ true
  × Hepatic.exogenousBH4RescuesConstrainedSystem Hepatic.canonicalHepaticCompetitionBoundary ≡ true
competitionEmergesWhenSupplyIsConstrained = refl , refl

adaptiveSupplyResponseIsObserved :
  Hepatic.phenylalanineInducesBiopterinSupplyResponse Hepatic.canonicalHepaticCompetitionBoundary ≡ true
adaptiveSupplyResponseIsObserved = refl

hepaticResultDoesNotCloseWholeAllocatorModel :
  Hepatic.hepaticTwoBranchResultProvesWholeBH4AllocatorModel Hepatic.canonicalHepaticCompetitionBoundary ≡ false
  × Hepatic.hepaticResultGeneralizesToHumanNeurobiology Hepatic.canonicalHepaticCompetitionBoundary ≡ false
  × Hepatic.hepaticResultPaysTH_TPH_AGMO Hepatic.canonicalHepaticCompetitionBoundary ≡ false
hepaticResultDoesNotCloseWholeAllocatorModel = refl , (refl , refl)
