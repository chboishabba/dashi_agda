module DASHI.Law.AustralianFamilyReportWriterRegulatoryImplementationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.AustralianFamilyReportWriterRegulatoryImplementationExact as Regulatory

------------------------------------------------------------------------
-- Contract: Part IIIAA / s 11K implementation status.
--
-- The Act can enact an enabling power while the current searched regulations
-- surface does not locate an implementing family-report-writer regime.  A
-- bounded negative search must not be promoted into proof of nonexistence.
------------------------------------------------------------------------

partIIIAAEnactedIsPaid : Regulatory.partIIIAAEnacted ≡ true
partIIIAAEnactedIsPaid = refl

section11KEnablingPowerIsPaid : Regulatory.section11KEnablingPowerPaid ≡ true
section11KEnablingPowerIsPaid = refl

currentRegulationsSurfaceWasChecked :
  Regulatory.currentRegulationsSurfaceChecked ≡ true
currentRegulationsSurfaceWasChecked = refl

implementingProvisionRemainsUnlocated :
  Regulatory.implementingProvisionLocated ≡ false
implementingProvisionRemainsUnlocated = refl

------------------------------------------------------------------------
-- Snowball widening: a broader Federal Register / AGD search was also run.
-- It located the Act / Schedule-7 enabling architecture and historical
-- consultation context, but did not locate a separate implementing instrument.
-- That still does not pay nonexistence.
------------------------------------------------------------------------

broaderImplementationSearchWasRun :
  Regulatory.broaderImplementationSearchPerformed ≡ true
broaderImplementationSearchWasRun = refl

broaderSearchStillDidNotLocateImplementingInstrument :
  Regulatory.broaderSearchLocatedImplementingInstrument ≡ false
broaderSearchStillDidNotLocateImplementingInstrument = refl

broaderSearchStillDoesNotProveAbsence :
  Regulatory.broaderSearchProvesAbsence ≡ false
broaderSearchStillDoesNotProveAbsence = refl

absenceIsNotProved :
  Regulatory.absenceOfImplementingProvisionProved ≡ false
absenceIsNotProved = refl

enablingPowerDoesNotAutomaticallyCreateOperativeRegime :
  Regulatory.EnablingPowerAutomaticallyOperativeRegime → ⊥
enablingPowerDoesNotAutomaticallyCreateOperativeRegime =
  Regulatory.enablingPowerDoesNotAutomaticallyCreateOperativeRegime

negativeSearchDoesNotProveAbsence :
  Regulatory.NegativeSearchAutomaticallyProvesAbsence → ⊥
negativeSearchDoesNotProveAbsence =
  Regulatory.negativeSearchDoesNotProveAbsence

regulatorConceptDoesNotDesignateRegulator :
  Regulatory.RegulatorConceptAutomaticallyDesignatesRegulator → ⊥
regulatorConceptDoesNotDesignateRegulator =
  Regulatory.regulatorConceptDoesNotAutomaticallyDesignateRegulator

possibleCourtConsequenceDoesNotCreateOperativeRule :
  Regulatory.PossibleCourtConsequenceAutomaticallyOperativeRule → ⊥
possibleCourtConsequenceDoesNotCreateOperativeRule =
  Regulatory.possibleCourtConsequenceDoesNotAutomaticallyBecomeOperativeRule

currentSearchReceiptIsExplicit : Regulatory.RegulatoryImplementationSearchReceipt
currentSearchReceiptIsExplicit = Regulatory.currentRegulatoryImplementationSearchReceipt

broaderSearchReceiptIsExplicit : Regulatory.BroaderRegulatorySearchReceipt
broaderSearchReceiptIsExplicit = Regulatory.currentBroaderRegulatorySearchReceipt
