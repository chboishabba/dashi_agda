module DASHI.Law.SmithInterpretationConsumerLegalFollowRegression where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Law.SmithInterpretationConsumerLegalFollowExact as S
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.ITIRInvestigationAcquisitionParetoExact as INV
import DASHI.Law.SensibLawLegalFollowProofSearchBridgeExact as LegalFollow
import DASHI.Reasoning.JusticeLeeSensibLawAdversarialProofGraphBidiExact as Lee

------------------------------------------------------------------------
-- Representation parity / dominance.
------------------------------------------------------------------------

regressionSimpleFullParity :
  S.RepresentationParity
    S.smithMeaningConsumer
    S.simpleAccessibleSurface
    S.fullTechnicalSurface
regressionSimpleFullParity = S.simpleFullMeaningParity

regressionMultilingualAtLeastFull :
  S.AtLeastAsInformative
    S.smithMeaningConsumer
    S.multilingualPeerSurface
    S.fullTechnicalSurface
regressionMultilingualAtLeastFull =
  S.multilingualAtLeastAsInformativeAsFullForMeaning

regressionSimpleStrictlyDominatesElaborate :
  S.StrictlyMoreInformative
    S.smithMeaningConsumer
    S.simpleAccessibleSurface
    S.elaborateAmbiguousSurface
regressionSimpleStrictlyDominatesElaborate =
  S.simpleSurfaceStrictlyDominatesElaborateForMeaning

------------------------------------------------------------------------
-- Coarse lexical collapse cannot recover the operative legal distinction.
------------------------------------------------------------------------

regressionCoarseLabelCannotRecoverOperativeDecision :
  NF.FactorsThrough S.coarseARTProjection S.operativeARTDecision → ⊥
regressionCoarseLabelCannotRecoverOperativeDecision =
  S.coarseARTLabelCannotRecoverOperativeDecision

------------------------------------------------------------------------
-- Existing owner boundaries remain the authorities.
------------------------------------------------------------------------

regressionMDLNoShortCodeAuthority :
  MDL.lowerDescriptionLengthIsPhysicalTruth MDL.canonicalAdmissibleConsumerMDLBoundary
    ≡ false
regressionMDLNoShortCodeAuthority =
  MDL.lowerDescriptionLengthIsPhysicalTruthIsFalse MDL.canonicalAdmissibleConsumerMDLBoundary

regressionInvestigationNoScalar :
  INV.scalarScoreRequired INV.canonicalInvestigationAcquisitionBoundary ≡ false
regressionInvestigationNoScalar =
  INV.scalarScoreRequiredIsFalse INV.canonicalInvestigationAcquisitionBoundary

regressionLegalFollowAcquisitionNotPayment :
  LegalFollow.acquisitionEqualsResidualPayment
    LegalFollow.canonicalLegalFollowProofSearchBoundary ≡ false
regressionLegalFollowAcquisitionNotPayment =
  LegalFollow.acquisitionEqualsResidualPaymentIsFalse
    LegalFollow.canonicalLegalFollowProofSearchBoundary

regressionLeeMachineNotAdjudicator :
  Lee.epistemicCapabilityImpliesAdjudicativeAuthority Lee.canonicalAuthorityBoundary
    ≡ false
regressionLeeMachineNotAdjudicator =
  Lee.epistemicCapabilityImpliesAdjudicativeAuthorityIsFalse Lee.canonicalAuthorityBoundary

------------------------------------------------------------------------
-- Smith-specific attribution/technique boundary.
------------------------------------------------------------------------

regressionConformingMeaningPhase :
  S.techniquePhase S.conformingInterpretation ≡ S.meaningFormation
regressionConformingMeaningPhase = S.conformingIsMeaningFormation

regressionSeveranceApplicationPhase :
  S.techniquePhase S.severance ≡ S.applicationConstraint
regressionSeveranceApplicationPhase = S.severanceIsApplicationConstraint

regressionStructuralDefectNotSophistryIntent :
  S.structuralDistortionProvesSophistryIntent S.canonicalSmithInterpretationBoundary
    ≡ false
regressionStructuralDefectNotSophistryIntent =
  S.structuralDistortionProvesSophistryIntentIsFalse
    S.canonicalSmithInterpretationBoundary
