module DASHI.Cognition.PNF.SensibLawLegalRecognitionObligationRemedyLatticeExact where

------------------------------------------------------------------------
-- FACT / STATUS / OBLIGATION / DUTY / REMEDY NON-COLLAPSE
--
-- Calibration sources:
--   * Mabo v Queensland (No 2) [1992] HCA 23; 175 CLR 1.
--   * Pabai v Commonwealth of Australia (No 2) [2025] FCA 796.
--   * International Court of Justice, Legal Consequences arising from the
--     Policies and Practices of Israel in the Occupied Palestinian Territory,
--     including East Jerusalem, Advisory Opinion, 19 July 2024,
--     General List No 186.
--
-- The generic lattice and no-collapse laws are DASHI formal reconstruction.
-- They do not assert that the three authorities instantiate identical doctrine.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge
import DASHI.Cognition.PNF.SensibLawPabaiRecognitionRemedyGapExact as Pabai

------------------------------------------------------------------------
-- Distinct juridical coordinates.
------------------------------------------------------------------------

data JuridicalCoordinate : Set where
  fact : JuridicalCoordinate
  legalStatus : JuridicalCoordinate
  legalObligation : JuridicalCoordinate
  privateLawDuty : JuridicalCoordinate
  causeOfAction : JuridicalCoordinate
  compensableHeadOfLoss : JuridicalCoordinate
  availableRemedy : JuridicalCoordinate
  domesticEnforceability : JuridicalCoordinate


record JuridicalReceipt : Set where
  constructor juridical-receipt
  field
    proposition : String
    coordinate : JuridicalCoordinate
    authority : Edge.SourceIdentity
    establishedAtThisCoordinate : Bool
    downstreamCoordinateAutomaticallyEstablished : Bool
    downstreamCoordinateAutomaticallyEstablishedIsFalse :
      downstreamCoordinateAutomaticallyEstablished ≡ false

open JuridicalReceipt public

------------------------------------------------------------------------
-- No automatic compilation through the remedial stack.
------------------------------------------------------------------------

data FactImpliesLegalStatus : Set where
data LegalStatusImpliesLegalObligation : Set where
data LegalObligationImpliesPrivateLawDuty : Set where
data PrivateLawDutyImpliesAvailableRemedy : Set where
data InternationalObligationImpliesAutomaticDomesticCauseOfAction : Set where
data NoPrivateLawDutyMeansNoNormativeObligation : Set where
\data NoDutyMeansNoLegalIntervention : Set where

factDoesNotAutomaticallyCreateStatus : FactImpliesLegalStatus → ⊥
factDoesNotAutomaticallyCreateStatus ()

statusDoesNotAutomaticallyCreateObligation : LegalStatusImpliesLegalObligation → ⊥
statusDoesNotAutomaticallyCreateObligation ()

obligationDoesNotAutomaticallyCreatePrivateDuty : LegalObligationImpliesPrivateLawDuty → ⊥
obligationDoesNotAutomaticallyCreatePrivateDuty ()

dutyDoesNotAutomaticallyCreateRemedy : PrivateLawDutyImpliesAvailableRemedy → ⊥
dutyDoesNotAutomaticallyCreateRemedy ()

internationalObligationDoesNotCompileAutomaticallyToDomesticAction :
  InternationalObligationImpliesAutomaticDomesticCauseOfAction → ⊥
internationalObligationDoesNotCompileAutomaticallyToDomesticAction ()

noPrivateDutyDoesNotProveNoObligation : NoPrivateLawDutyMeansNoNormativeObligation → ⊥
noPrivateDutyDoesNotProveNoObligation ()

noDutyDoesNotMeanNoIntervention : NoDutyMeansNoLegalIntervention → ⊥
noDutyDoesNotMeanNoIntervention ()

------------------------------------------------------------------------
-- Preservation of an existing loss allocation is itself representable.
------------------------------------------------------------------------

data LossBearer : Set where
  claimant : LossBearer
  defendant : LossBearer
  publicFund : LossBearer
  distributedOrUnresolved : LossBearer


record DistributionalEffect : Set where
  constructor distributional-effect
  field
    beforeDecision : LossBearer
    afterDecision : LossBearer
    legalRouteChanged : Bool
    existingAllocationPreserved : Bool

open DistributionalEffect public

pabaiFirstInstanceAllocation : DistributionalEffect
pabaiFirstInstanceAllocation = distributional-effect
  claimant claimant false true

preservationIsObservableOutcome :
  existingAllocationPreserved pabaiFirstInstanceAllocation ≡ true
preservationIsObservableOutcome = refl

------------------------------------------------------------------------
-- Mabo is a positive calibration for decomposition, not a universal recipe.
------------------------------------------------------------------------

data MaboPropertyNode : Set where
  crownSovereignty : MaboPropertyNode
  crownRadicalTitle : MaboPropertyNode
  crownBeneficialOwnershipOfAllLand : MaboPropertyNode
  antecedentNativeTitle : MaboPropertyNode
  survivingNativeTitle : MaboPropertyNode


record MaboDecompositionReceipt : Set where
  constructor mabo-decomposition-receipt
  field
    sovereigntyToRadicalTitleRetained : Bool
    sovereigntyToRadicalTitleRetainedIsTrue :
      sovereigntyToRadicalTitleRetained ≡ true
    radicalTitleAutomaticallyMeansBeneficialOwnershipAllLand : Bool
    radicalTitleAutomaticallyMeansBeneficialOwnershipAllLandIsFalse :
      radicalTitleAutomaticallyMeansBeneficialOwnershipAllLand ≡ false
    antecedentRightsCanSurviveSovereignty : Bool
    antecedentRightsCanSurviveSovereigntyIsTrue :
      antecedentRightsCanSurviveSovereignty ≡ true
    acquisitionOfSovereigntyItselfReopenedByMunicipalCourt : Bool
    acquisitionOfSovereigntyItselfReopenedByMunicipalCourtIsFalse :
      acquisitionOfSovereigntyItselfReopenedByMunicipalCourt ≡ false

open MaboDecompositionReceipt public

canonicalMaboDecomposition : MaboDecompositionReceipt
canonicalMaboDecomposition = mabo-decomposition-receipt
  true refl false refl true refl false refl

------------------------------------------------------------------------
-- Pabai weld: consume the existing exact owner instead of restating its facts.
------------------------------------------------------------------------

pabaiRecognisedHarmDoesNotFactorToRemedy :
  DASHI.Core.IntersectionalNonFactorability.FactorsThrough
    Pabai.harmRecognitionObserver Pabai.remedyState → ⊥
pabaiRecognisedHarmDoesNotFactorToRemedy =
  Pabai.harmRecognitionCannotDetermineNegligenceRemedy

------------------------------------------------------------------------
-- Structural analogy does not merge jurisdictions or doctrines.
------------------------------------------------------------------------

data MaboAndPabaiSameDoctrine : Set where
data PabaiAndICJSameRemedialRegime : Set where
data RecognitionGapProvesJudicialBadFaith : Set where

maboAndPabaiRemainDistinct : MaboAndPabaiSameDoctrine → ⊥
maboAndPabaiRemainDistinct ()

pabaiAndICJRemainDistinct : PabaiAndICJSameRemedialRegime → ⊥
pabaiAndICJRemainDistinct ()

recognitionGapDoesNotProveBadFaith : RecognitionGapProvesJudicialBadFaith → ⊥
recognitionGapDoesNotProveBadFaith ()
