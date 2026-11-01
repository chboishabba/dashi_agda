module DASHI.Culture.LopezRiosExistingPsychologyCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Culture.LopezRiosPsychologisationDialecticNonDescentExact as Lopez
import DASHI.Philosophy.MentalHealthWorkedExample as Mental
import DASHI.Philosophy.MentalHealthEvidenceAdapter as Evidence
import DASHI.Promotion.SystemicDistressReframingBoundary as Systemic
import DASHI.Reasoning.DevelopmentalAttunementPNFBridge as Developmental

------------------------------------------------------------------------
-- EXISTING PSYCHOLOGY CROSS-POLLINATION
--
-- This owner does not attribute the imported DASHI psychology theorems to
-- Lopez-Rios.  It records that the repo already has independently governed
-- psychology/mental-health surfaces whose boundaries are compatible with the
-- new psychologisation non-descent fixture.
------------------------------------------------------------------------

mentalHealthCaseRetained : Mental.MentalHealthCase
mentalHealthCaseRetained = Mental.canonicalMentalHealthCase

mentalHealthPromotionBoundaryRetained : Evidence.MentalHealthPromotionBoundary
mentalHealthPromotionBoundaryRetained = Evidence.canonicalMentalHealthPromotionBoundary

systemicDistressBoundaryRetained : Systemic.SystemicDistressBoundary
systemicDistressBoundaryRetained = Systemic.canonicalSystemicDistressBoundary

developmentalAttunementBoundaryRetained :
  Developmental.DevelopmentalAttunementAuthorityBoundary
developmentalAttunementBoundaryRetained =
  Developmental.canonicalDevelopmentalAttunementAuthorityBoundary

psychologisationBoundaryRetained : Lopez.LopezRiosPsychologisationDialecticBoundary
psychologisationBoundaryRetained = Lopez.canonicalLopezRiosPsychologisationDialecticBoundary

------------------------------------------------------------------------
-- Existing mental-health owners already block the two symmetric reductions:
-- individual-only defect closure and automatic systemic causal closure.
------------------------------------------------------------------------

existingMentalHealthNoAutomaticDiagnosis :
  Mental.automaticDiagnosisInferred Mental.canonicalMentalHealthCase ≡ false
existingMentalHealthNoAutomaticDiagnosis = Mental.canonicalNoAutomaticDiagnosis

existingMentalHealthNoAutomaticSystemicTruth :
  Mental.automaticSystemicTruthInferred Mental.canonicalMentalHealthCase ≡ false
existingMentalHealthNoAutomaticSystemicTruth = Mental.canonicalNoAutomaticSystemicTruth

existingSupportDoesNotPromoteClinicalClaim :
  Evidence.supportPlanAutomaticallyClinical Evidence.canonicalMentalHealthPromotionBoundary
  ≡ false
existingSupportDoesNotPromoteClinicalClaim =
  Evidence.canonicalSupportDoesNotAutomaticallyPromoteClinicalClaim

existingSystemicBoundaryDoesNotReduceEveryDiagnosisToCapitalism :
  Systemic.everyDiagnosisReducedToCapitalism Systemic.canonicalSystemicDistressBoundary
  ≡ false
existingSystemicBoundaryDoesNotReduceEveryDiagnosisToCapitalism = refl

existingDevelopmentalBoundaryDoesNotDiagnoseTraumaFromFragmentation :
  Developmental.fragmentationAloneDiagnosesTrauma
    Developmental.canonicalDevelopmentalAttunementAuthorityBoundary
  ≡ false
existingDevelopmentalBoundaryDoesNotDiagnoseTraumaFromFragmentation = refl

------------------------------------------------------------------------
-- The cross-pollinated architecture is therefore bidirectionally guarded:
--
--   individual observation alone  !-> structural causal closure
--   structural/systemic framing    !-> automatic diagnosis/total explanation
--
-- This is a DASHI synthesis, not a proposition imported from Lopez-Rios.
------------------------------------------------------------------------

data LopezRiosOwnsExistingDASHIPsychologyTheorems : Set where
data SystemicCritiqueAutomaticallyDiagnosesIndividual : Set where
data IndividualObservationAutomaticallyClosesStructuralCause : Set where

existingPsychologyNotAttributedBackToLopezRios :
  LopezRiosOwnsExistingDASHIPsychologyTheorems → ⊥
existingPsychologyNotAttributedBackToLopezRios ()

systemicCritiqueDoesNotAutomaticallyDiagnoseIndividual :
  SystemicCritiqueAutomaticallyDiagnosesIndividual → ⊥
systemicCritiqueDoesNotAutomaticallyDiagnoseIndividual ()

individualObservationDoesNotAutomaticallyCloseStructuralCause :
  IndividualObservationAutomaticallyClosesStructuralCause → ⊥
individualObservationDoesNotAutomaticallyCloseStructuralCause ()

record LopezRiosExistingPsychologyCrossPollinationBoundary : Set where
  constructor lopez-rios-existing-psychology-cross-pollination-boundary
  field
    existingMentalHealthMultiCausalityReused : Bool
    existingClinicalPromotionGatingReused : Bool
    existingSystemicReframingBoundaryReused : Bool
    existingDevelopmentalAttunementBoundaryReused : Bool
    individualOnlyCausalClosureAllowed : Bool
    systemicOnlyCausalClosureAllowed : Bool
    importedDASHIPsychologyAttributedToLopezRios : Bool

canonicalLopezRiosExistingPsychologyCrossPollinationBoundary :
  LopezRiosExistingPsychologyCrossPollinationBoundary
canonicalLopezRiosExistingPsychologyCrossPollinationBoundary =
  lopez-rios-existing-psychology-cross-pollination-boundary
    true true true true false false false
