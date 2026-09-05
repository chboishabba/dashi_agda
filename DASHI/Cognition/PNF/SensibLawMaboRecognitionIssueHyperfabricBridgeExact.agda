module DASHI.Cognition.PNF.SensibLawMaboRecognitionIssueHyperfabricBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawIssueIndexedAdjudicativeHyperfabricExact as Issue
import DASHI.Cognition.PNF.SensibLawMaboBrennanDawsonIssueResidualLiveExact as Mabo
import DASHI.Cognition.PNF.SensibLawMaboRecognitionCoordinateFactorisationExact as Factor

data MaboAdjudicativeResidual : Set where
  continuityResidual
  enforceabilityResidual
  recognitionRequirementResidual
  recognitionConductResidual
  exactTheoryResidual
  : MaboAdjudicativeResidual

coordinateResidual : Factor.RecognitionCoordinate → MaboAdjudicativeResidual
coordinateResidual Factor.antecedentRightExistence = continuityResidual
coordinateResidual Factor.continuityAcrossSovereignty = continuityResidual
coordinateResidual Factor.radicalTitleCompatibility = enforceabilityResidual
coordinateResidual Factor.enforceabilityAgainstCrown = enforceabilityResidual
coordinateResidual Factor.crownRecognitionRequirement = recognitionRequirementResidual
coordinateResidual Factor.recognitionByCrownConduct = recognitionConductResidual
coordinateResidual Factor.evidentialInferenceOfRecognition = recognitionConductResidual
coordinateResidual Factor.authorityInterpretation = exactTheoryResidual

data MaboProofObligation : Set where
  establishContinuityRule
  establishEnforceabilityStructure
  establishRecognitionRequirement
  establishRecognitionByConduct
  establishAuthorityInterpretation
  : MaboProofObligation

residualObligation : MaboAdjudicativeResidual → MaboProofObligation
residualObligation continuityResidual = establishContinuityRule
residualObligation enforceabilityResidual = establishEnforceabilityStructure
residualObligation recognitionRequirementResidual = establishRecognitionRequirement
residualObligation recognitionConductResidual = establishRecognitionByConduct
residualObligation exactTheoryResidual = establishAuthorityInterpretation

data MaboGenericDiscriminator : Set where
  continuityAuthorityDiscriminator
  radicalTitleDiscriminator
  recognitionDoctrineDiscriminator
  conductInferenceDiscriminator
  authorityInterpretationDiscriminator
  : MaboGenericDiscriminator

obligationDiscriminator : MaboProofObligation → MaboGenericDiscriminator
obligationDiscriminator establishContinuityRule = continuityAuthorityDiscriminator
obligationDiscriminator establishEnforceabilityStructure = radicalTitleDiscriminator
obligationDiscriminator establishRecognitionRequirement = recognitionDoctrineDiscriminator
obligationDiscriminator establishRecognitionByConduct = conductInferenceDiscriminator
obligationDiscriminator establishAuthorityInterpretation = authorityInterpretationDiscriminator

record MaboIssueHyperfabricReceipt : Set where
  constructor maboIssueHyperfabricReceipt
  field
    issue : Issue.LegalIssue
    sourceResidual : Mabo.MaboControversyResidual
    coordinate : Factor.RecognitionCoordinate
    residual : MaboAdjudicativeResidual
    residualExact : residual ≡ coordinateResidual coordinate
    obligation : MaboProofObligation
    obligationExact : obligation ≡ residualObligation residual
    discriminator : MaboGenericDiscriminator
    discriminatorExact : discriminator ≡ obligationDiscriminator obligation
    genericIssueReferencePreserved : issue ≡ Mabo.maboRecognitionIssue
open MaboIssueHyperfabricReceipt public

compileCoordinateToIssueHyperfabric : Factor.RecognitionCoordinate → MaboIssueHyperfabricReceipt
compileCoordinateToIssueHyperfabric c = maboIssueHyperfabricReceipt
  Mabo.maboRecognitionIssue Mabo.brennanDawsonResidual c
  (coordinateResidual c) refl
  (residualObligation (coordinateResidual c)) refl
  (obligationDiscriminator (residualObligation (coordinateResidual c))) refl
  refl

continuityHyperfabric : MaboIssueHyperfabricReceipt
continuityHyperfabric = compileCoordinateToIssueHyperfabric Factor.continuityAcrossSovereignty
recognitionConductHyperfabric : MaboIssueHyperfabricReceipt
recognitionConductHyperfabric = compileCoordinateToIssueHyperfabric Factor.recognitionByCrownConduct

continuityObligationIsSpecific : obligation continuityHyperfabric ≡ establishContinuityRule
continuityObligationIsSpecific = refl
recognitionConductObligationIsSpecific : obligation recognitionConductHyperfabric ≡ establishRecognitionByConduct
recognitionConductObligationIsSpecific = refl

data OneRecognitionResidualFitsEveryCoordinate : Set where
data CoordinateBridgeChangesIssueIdentity : Set where
data GenericHyperfabricBridgeAdjudicatesMabo : Set where

oneResidualDoesNotFitEveryRecognitionCoordinate : OneRecognitionResidualFitsEveryCoordinate → ⊥
oneResidualDoesNotFitEveryRecognitionCoordinate ()
coordinateBridgeDoesNotChangeIssueIdentity : CoordinateBridgeChangesIssueIdentity → ⊥
coordinateBridgeDoesNotChangeIssueIdentity ()
genericBridgeDoesNotAdjudicateMabo : GenericHyperfabricBridgeAdjudicatesMabo → ⊥
genericBridgeDoesNotAdjudicateMabo ()
