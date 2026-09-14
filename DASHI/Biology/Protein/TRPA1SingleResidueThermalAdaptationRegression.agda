module DASHI.Biology.Protein.TRPA1SingleResidueThermalAdaptationRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Protein.TRPA1SingleResidueThermalAdaptationExact as TRPA1

siteMutationIsExplicit :
  TRPA1.TRPA1ThermalAdaptationBoundary.siteSpecificMutationCoordinatePaid
    TRPA1.canonicalTRPA1ThermalAdaptationBoundary
  ≡ true
siteMutationIsExplicit = refl

proteinIdentityAloneIsInsufficient :
  TRPA1.TRPA1ThermalAdaptationBoundary.proteinIdentityAloneDeterminesThermalResponse
    TRPA1.canonicalTRPA1ThermalAdaptationBoundary
  ≡ false
proteinIdentityAloneIsInsufficient = refl

singleResidueIsNotUniversalFunctionTheorem :
  TRPA1.TRPA1ThermalAdaptationBoundary.singleResidueDeterminesAllProteinFunction
    TRPA1.canonicalTRPA1ThermalAdaptationBoundary
  ≡ false
singleResidueIsNotUniversalFunctionTheorem = refl

mechanismPathIsTyped :
  TRPA1.TRPA1ThermalAdaptationBoundary.ca2Sp1Cadm1Mdga1PathPaid
    TRPA1.canonicalTRPA1ThermalAdaptationBoundary
  ≡ true
mechanismPathIsTyped = refl

thermalGateDoesNotEqualWholeOrganismSurvival :
  TRPA1.TRPA1ThermalAdaptationBoundary.thermalActivationAloneProvesEmbryoSurvival
    TRPA1.canonicalTRPA1ThermalAdaptationBoundary
  ≡ false
thermalGateDoesNotEqualWholeOrganismSurvival = refl

allicinAndHeatMechanismsStayDistinct :
  TRPA1.TRPA1ThermalAdaptationBoundary.allicinActivationIsSameMechanismAsThermalGating
    TRPA1.canonicalTRPA1ThermalAdaptationBoundary
  ≡ false
allicinAndHeatMechanismsStayDistinct = refl

sourceDoesNotCreateUniversalEvolutionLaw :
  TRPA1.TRPA1ThermalAdaptationBoundary.paperCreatesUniversalVertebrateAdaptationLaw
    TRPA1.canonicalTRPA1ThermalAdaptationBoundary
  ≡ false
sourceDoesNotCreateUniversalEvolutionLaw = refl
