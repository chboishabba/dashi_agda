module DASHI.Law.SmithInterpretationConsumerLegalFollowValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.SmithInterpretationConsumerLegalFollowExact as S

------------------------------------------------------------------------
-- RED-first contract for the Smith interpretation max-cut.
------------------------------------------------------------------------

validationBoundary : S.SmithInterpretationBoundary
validationBoundary = S.canonicalSmithInterpretationBoundary

validationComplexityNoAuthority :
  S.complexityCreatesAuthority S.canonicalSmithInterpretationBoundary ≡ false
validationComplexityNoAuthority =
  S.complexityCreatesAuthorityIsFalse S.canonicalSmithInterpretationBoundary

validationPrecedentNotUniverse :
  S.precedentExhaustsInterpretationUniverse S.canonicalSmithInterpretationBoundary ≡ false
validationPrecedentNotUniverse =
  S.precedentExhaustsInterpretationUniverseIsFalse S.canonicalSmithInterpretationBoundary

validationExperimentProposalOnly :
  S.experimentalDiscriminatorCreatesTruth S.canonicalSmithInterpretationBoundary ≡ false
validationExperimentProposalOnly =
  S.experimentalDiscriminatorCreatesTruthIsFalse S.canonicalSmithInterpretationBoundary

validationParetoNoScalar :
  S.investigativeParetoUsesScalarScore S.canonicalSmithInterpretationBoundary ≡ false
validationParetoNoScalar =
  S.investigativeParetoUsesScalarScoreIsFalse S.canonicalSmithInterpretationBoundary

validationAcquisitionNotPayment :
  S.legalFollowAcquisitionPaysResidual S.canonicalSmithInterpretationBoundary ≡ false
validationAcquisitionNotPayment =
  S.legalFollowAcquisitionPaysResidualIsFalse S.canonicalSmithInterpretationBoundary

validationStructuralDefectNotIntent :
  S.structuralDistortionProvesSophistryIntent S.canonicalSmithInterpretationBoundary ≡ false
validationStructuralDefectNotIntent =
  S.structuralDistortionProvesSophistryIntentIsFalse S.canonicalSmithInterpretationBoundary

validationMachineNotJudge :
  S.machineSynthesisDeterminesJudgment S.canonicalSmithInterpretationBoundary ≡ false
validationMachineNotJudge =
  S.machineSynthesisDeterminesJudgmentIsFalse S.canonicalSmithInterpretationBoundary

validationSimpleDominance : S.StrictlyMoreInformative
  S.smithMeaningConsumer
  S.simpleAccessibleSurface
  S.elaborateAmbiguousSurface
validationSimpleDominance = S.simpleSurfaceStrictlyDominatesElaborateForMeaning

validationWideCounterexample : S.InterpretationCounterexample S.widePurposeConnectedConstruction
validationWideCounterexample = S.smithWideConstructionCounterexample

validationExperimentHandoff : S.DiscriminatorDesignHandoff
validationExperimentHandoff = S.smithDiscriminatorDesignHandoff

validationParetoHandoff : S.AcquisitionParetoHandoff
validationParetoHandoff = S.smithParetoAcquisitionHandoff
