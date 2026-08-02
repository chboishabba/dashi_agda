module DASHI.Physics.Closure.NSTriadKNStage3ConstructiveSeriesOrientationIntegration where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Martin Lundfall; Zachary Murray; Viktor Csimma; Robbert Krebbers;
-- Bas Spitters; Loukas Grafakos; Rodolfo H. Torres; Terence Tao; Minghui Liu;
-- Gabor Pataki; Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin; Raphael
-- Danchin; Errett Bishop; Douglas Bridges; Augustin-Louis Cauchy; Hermann
-- Amandus Schwarz; Agda standard-library contributors; DASHI repository
-- contributors.
-- Title: "Stage-3 constructive-series candidate, literal Schur-shell
-- substitution, affine falsification, unit-weight Check A and derived native-
-- spine output-relocation integration".
-- Venue/year: Reals-in-agda formal development, 2015; Constructive Analysis in
-- the Agda Proof Assistant, 2022; Logical Methods in Computer Science 9(1:1),
-- 2013; Journal of Functional Analysis 187 (2001), 1--24 and 199 (2003),
-- 379--385; Mathematical Programming / arXiv, 2015--2017; Annales
-- scientifiques de l'Ecole Normale Superieure 14 (1981); Springer, 1985 and
-- 2011; Agda standard library; DASHI formal development, 2026.
-- DOI: 10.2168/LMCS-9(1:1)2013; 10.1006/jfan.2001.3804;
-- 10.1016/S0022-1236(02)00098-8; 10.48550/arXiv.1507.00290;
-- 10.24033/asens.1404; 10.1007/978-3-642-61667-9;
-- 10.1007/978-3-642-16830-7; Murray arXiv:2205.08354 has no DOI; no DOI
-- located for Reals-in-agda; the integration receipt has no DOI.
-- Uses: constructive-real candidate comparison, literal power-law Schur
-- orientation, exact affine falsification and unit-weight recovery, recursive
-- rational geometric sums, the positive kernel, three normalized shell Schur
-- bounds, finite signed domination, base-two envelope derivation, absolute-
-- coefficient derivation and the native-spine composite theorem.
-- Relationship: the four former raw fields are now derived theorem outputs.
-- The concrete frontier is the native ordered/rational capability, coherent
-- base-two power and integer anchors, endpoint decay data, absolute-value order
-- laws, factor nonnegativity and one literal absolute-coefficient estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNConstructiveRealCandidateComparison as Reals
import DASHI.Physics.Closure.NSTriadKNGrafakosTorresPowerLawOrientation as Orientation
import DASHI.Physics.Closure.NSTriadKNOutputRelocationWeightedExponentIdentity as Weighted
import DASHI.Physics.Closure.NSTriadKNOutputRelocationLiteralShellSubstitution as Shells
import DASHI.Physics.Closure.NSTriadKNOutputRelocationAffineFamilySubstitution as AffineRows
import DASHI.Physics.Closure.NSTriadKNOutputRelocationAffineFarkasDecision as Decision
import DASHI.Physics.Closure.NSTriadKNOutputRelocationUnitWeightCheckA as Unit
import DASHI.Physics.Closure.NSTriadKNOutputRelocationIntegerGeometricEnvelope as Envelope
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPowerMonotonicityBridge as PowerBridge
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant
import DASHI.Physics.Closure.NSTriadKNOutputRelocationUnitWeightShellSchur as ShellSchur
import DASHI.Physics.Closure.NSTriadKNRationalFiniteSignedMajorant as Signed
import DASHI.Physics.Closure.NSTriadKNOutputRelocationConditionalCutoffUniformClosure as Conditional
import DASHI.Physics.Closure.NSTriadKNOutputRelocationAbsoluteCoefficientBridge as Absolute
import DASHI.Physics.Closure.NSTriadKNConstructiveRealSpineOutputRelocationDerivedClosure as Derived
import DASHI.Physics.Closure.NSTriadKNOutputRelocationCutoffUniformArchetypeProgram as Archetype

record ConstructiveSeriesOrientationReceipt : Set where
  constructor receipt
  field
    bothConstructiveCandidatesRecorded : Reals.bothAgdaCandidatesRecorded ≡ true
    lundfallLegacyPinRecorded : Reals.lundfallLegacyStdlibPinRecorded ≡ true
    lundfallDirectImportDeprioritized :
      Reals.lundfallDirectImportDeprioritized ≡ true
    murrayPreferredLiveCandidate :
      Reals.murrayCsimmaPreferredLiveCandidate ≡ true
    coqReferenceArchitectureRecorded :
      Reals.coqReferenceArchitectureRecorded ≡ true
    candidateComparisonDoesNotPromoteProof :
      Reals.candidateComparisonChangesProofStatus ≡ false
    physicalExponentIdentityClosed :
      Weighted.outputRelocationWeightedExponentIdentityClosed ≡ true
    schurSignOrientationClosed :
      Orientation.grafakosTorresSignOrientationClosed ≡ true
    literalThreeConditionTemplateClosed :
      Orientation.literalThreeConditionTemplateClosed ≡ true
    literalShellSubstitutionClosed :
      Shells.outputRelocationLiteralShellSubstitutionClosed ≡ true
    threeConditionAffineRowsClosed :
      Shells.outputRelocationThreeConditionAffineRowsClosed ≡ true
    affineFamilySubstitutionClosed :
      AffineRows.outputRelocationAffineFamilySubstitutionClosed ≡ true
    sixEpsilonSlopesClosed :
      AffineRows.outputRelocationSixEpsilonSlopesClosed ≡ true
    baseSystemClassified :
      Decision.outputRelocationBaseSystemClassified ≡ true
    directionSystemClassified :
      Decision.outputRelocationDirectionSystemClassified ≡ true
    sourceStyleCommonIntervalComputed :
      Decision.outputRelocationCommonIntervalComputed ≡ true
    sourceStyleAffineAnsatzInfeasible :
      Decision.currentHomogeneityPreservingAffineAnsatzInfeasible ≡ true
    noOverbroadFalsificationClaim :
      Decision.allPossibleThreeWeightAnsatzesInfeasible ≡ false
    unitWeightsAllowed : Unit.unitWeightsAllowedBySchurCarrier ≡ true
    unitWeightRowsReduced :
      Unit.outputRelocationUnitWeightSixRowsReduced ≡ true
    unitWeightSymbolicCheckAClosed :
      Unit.outputRelocationUnitWeightSymbolicCheckA ≡ true
    integerEnvelopeExponentsClosed :
      Envelope.outputRelocationIntegerEnvelopeExponentsClosed ≡ true
    rationalGeometricConstantsClosed :
      Envelope.outputRelocationRationalGeometricConstantsClosed ≡ true
    rationalFiniteSummationClosed :
      Envelope.outputRelocationRationalFiniteCutoffSummationClosed ≡ true
    arbitraryRatioGeometricTheoremNotRequired :
      Envelope.outputRelocationArbitraryRatioGeometricTheoremRequired ≡ false
    positiveKernelConstructed :
      Majorant.outputRelocationPositiveKernelConstructed ≡ true
    positiveKernelSummable :
      Majorant.outputRelocationPositiveKernelCutoffUniformlySummable ≡ true
    threeUnitWeightShellConditionsClosed :
      ShellSchur.outputRelocationThreeUnitWeightShellSchurConditionsClosed
      ≡ true
    finiteSignedDominationClosed :
      Signed.finiteTwoSidedTriangleDominationClosed ≡ true
    conditionalArchetypeTheoremClosed :
      Conditional.outputRelocationConditionalArchetypeTheoremClosed ≡ true
    allDownstreamOfShellBridgeClosed :
      Conditional.outputRelocationAllDownstreamOfShellBridgeClosed ≡ true
    twoPowerDominationTheoremsClosed :
      PowerBridge.outputRelocationTwoPowerDominationTheoremsClosed ≡ true
    absoluteMagnitudeToTwoSidedClosed :
      Absolute.absoluteMagnitudeToTwoSidedDominationClosed ≡ true
    fourFormerRawFieldsDerived :
      Derived.fourFormerRawBridgeFieldsDerived ≡ true
    nativeSpineDerivedClosureTheoremClosed :
      Derived.nativeSpineDerivedClosureTheoremClosed ≡ true
    finalArchetypeCutsetSpecified :
      Archetype.outputRelocationFinalArchetypeCutsetSpecified ≡ true
    concreteBaseTwoPowerDataStillOpen :
      Derived.concreteNativeBaseTwoPowerCapabilityClosed ≡ false
    concreteLiteralAbsoluteEstimateStillOpen :
      Derived.concreteLiteralAbsoluteCoefficientEstimateClosed ≡ false
    actualHsSeriesStillOpen :
      Envelope.outputRelocationActualHsCutoffUniformSeriesClosed ≡ false
    concreteAnalyticArchetypeStillOpen :
      Archetype.outputRelocationCutoffUniformArchetypeTheoremClosed ≡ false

open ConstructiveSeriesOrientationReceipt public

constructiveSeriesOrientationReceipt : ConstructiveSeriesOrientationReceipt
constructiveSeriesOrientationReceipt = receipt
  Reals.bothAgdaCandidatesRecordedIsTrue
  Reals.lundfallLegacyStdlibPinRecordedIsTrue
  Reals.lundfallDirectImportDeprioritizedIsTrue
  Reals.murrayCsimmaPreferredLiveCandidateIsTrue
  Reals.coqReferenceArchitectureRecordedIsTrue
  Reals.candidateComparisonChangesProofStatusIsFalse
  Weighted.outputRelocationWeightedExponentIdentityClosedIsTrue
  Orientation.grafakosTorresSignOrientationClosedIsTrue
  Orientation.literalThreeConditionTemplateClosedIsTrue
  Shells.outputRelocationLiteralShellSubstitutionClosedIsTrue
  Shells.outputRelocationThreeConditionAffineRowsClosedIsTrue
  AffineRows.outputRelocationAffineFamilySubstitutionClosedIsTrue
  AffineRows.outputRelocationSixEpsilonSlopesClosedIsTrue
  Decision.outputRelocationBaseSystemClassifiedIsTrue
  Decision.outputRelocationDirectionSystemClassifiedIsTrue
  Decision.outputRelocationCommonIntervalComputedIsTrue
  Decision.currentHomogeneityPreservingAffineAnsatzInfeasibleIsTrue
  Decision.allPossibleThreeWeightAnsatzesInfeasibleIsFalse
  Unit.unitWeightsAllowedBySchurCarrierIsTrue
  Unit.outputRelocationUnitWeightSixRowsReducedIsTrue
  Unit.outputRelocationUnitWeightSymbolicCheckAIsTrue
  Envelope.outputRelocationIntegerEnvelopeExponentsClosedIsTrue
  Envelope.outputRelocationRationalGeometricConstantsClosedIsTrue
  Envelope.outputRelocationRationalFiniteCutoffSummationClosedIsTrue
  Envelope.outputRelocationArbitraryRatioGeometricTheoremRequiredIsFalse
  Majorant.outputRelocationPositiveKernelConstructedIsTrue
  Majorant.outputRelocationPositiveKernelCutoffUniformlySummableIsTrue
  ShellSchur.outputRelocationThreeUnitWeightShellSchurConditionsClosedIsTrue
  Signed.finiteTwoSidedTriangleDominationClosedIsTrue
  Conditional.outputRelocationConditionalArchetypeTheoremClosedIsTrue
  Conditional.outputRelocationAllDownstreamOfShellBridgeClosedIsTrue
  PowerBridge.outputRelocationTwoPowerDominationTheoremsClosedIsTrue
  Absolute.absoluteMagnitudeToTwoSidedDominationClosedIsTrue
  Derived.fourFormerRawBridgeFieldsDerivedIsTrue
  Derived.nativeSpineDerivedClosureTheoremClosedIsTrue
  Archetype.outputRelocationFinalArchetypeCutsetSpecifiedIsTrue
  Derived.concreteNativeBaseTwoPowerCapabilityClosedIsFalse
  Derived.concreteLiteralAbsoluteCoefficientEstimateClosedIsFalse
  Envelope.outputRelocationActualHsCutoffUniformSeriesClosedIsFalse
  Archetype.outputRelocationCutoffUniformArchetypeTheoremClosedIsFalse

constructiveRealCandidateComparisonClosed : Bool
constructiveRealCandidateComparisonClosed = true

literalOutputRelocationShellSubstitutionClosed : Bool
literalOutputRelocationShellSubstitutionClosed = true

outputRelocationAffineEpsilonSlopesClosed : Bool
outputRelocationAffineEpsilonSlopesClosed = true

outputRelocationHighestAlphaDecisionClosed : Bool
outputRelocationHighestAlphaDecisionClosed = true

outputRelocationSourceStyleAffineAnsatzInfeasible : Bool
outputRelocationSourceStyleAffineAnsatzInfeasible = true

outputRelocationUnitWeightSymbolicCheckAClosed : Bool
outputRelocationUnitWeightSymbolicCheckAClosed = true

outputRelocationIntegerGeometricEnvelopeClosed : Bool
outputRelocationIntegerGeometricEnvelopeClosed = true

outputRelocationRationalFiniteSummationClosed : Bool
outputRelocationRationalFiniteSummationClosed = true

outputRelocationPositiveKernelProgramClosed : Bool
outputRelocationPositiveKernelProgramClosed = true

outputRelocationThreeShellSchurConditionsClosed : Bool
outputRelocationThreeShellSchurConditionsClosed = true

outputRelocationFiniteSignedDominationClosed : Bool
outputRelocationFiniteSignedDominationClosed = true

outputRelocationConditionalArchetypeClosed : Bool
outputRelocationConditionalArchetypeClosed = true

outputRelocationTwoPowerDominationTheoremsClosed : Bool
outputRelocationTwoPowerDominationTheoremsClosed = true

outputRelocationAbsoluteCoefficientDerivationClosed : Bool
outputRelocationAbsoluteCoefficientDerivationClosed = true

outputRelocationFourFormerRawBridgeFieldsDerived : Bool
outputRelocationFourFormerRawBridgeFieldsDerived = true

outputRelocationNativeSpineDerivedClosureTheoremClosed : Bool
outputRelocationNativeSpineDerivedClosureTheoremClosed = true

outputRelocationFinalArchetypeCutsetSpecified : Bool
outputRelocationFinalArchetypeCutsetSpecified = true

-- Compatibility aggregate leaves retained for downstream consumers.
nextLeafIsConcreteShellBridge : Bool
nextLeafIsConcreteShellBridge = true

nextLeafIsConstructivePowerMonotonicityBridge : Bool
nextLeafIsConstructivePowerMonotonicityBridge = true

nextLeafIsConcreteNativeSpineCapability : Bool
nextLeafIsConcreteNativeSpineCapability = true

nextLeafIsConcreteBaseTwoPowerData : Bool
nextLeafIsConcreteBaseTwoPowerData = true

nextLeafIsLiteralAbsoluteCoefficientEstimate : Bool
nextLeafIsLiteralAbsoluteCoefficientEstimate = true

nextLeafIsConstructiveDyadicTail : Bool
nextLeafIsConstructiveDyadicTail = false

nextLeafIsWeightAnsatzRevision : Bool
nextLeafIsWeightAnsatzRevision = false

nextLeafIsNumericBasesDirectionsAndDyadicTail : Bool
nextLeafIsNumericBasesDirectionsAndDyadicTail = false

-- Compatibility name: this denotes the concrete operator-level Check A, not
-- the already-closed symbolic unit-weight shell criterion.
outputRelocationCheckAClosed : Bool
outputRelocationCheckAClosed = false

constructiveRealCandidateComparisonClosedIsTrue :
  constructiveRealCandidateComparisonClosed ≡ true
constructiveRealCandidateComparisonClosedIsTrue = refl

literalOutputRelocationShellSubstitutionClosedIsTrue :
  literalOutputRelocationShellSubstitutionClosed ≡ true
literalOutputRelocationShellSubstitutionClosedIsTrue = refl

outputRelocationAffineEpsilonSlopesClosedIsTrue :
  outputRelocationAffineEpsilonSlopesClosed ≡ true
outputRelocationAffineEpsilonSlopesClosedIsTrue = refl

outputRelocationHighestAlphaDecisionClosedIsTrue :
  outputRelocationHighestAlphaDecisionClosed ≡ true
outputRelocationHighestAlphaDecisionClosedIsTrue = refl

outputRelocationSourceStyleAffineAnsatzInfeasibleIsTrue :
  outputRelocationSourceStyleAffineAnsatzInfeasible ≡ true
outputRelocationSourceStyleAffineAnsatzInfeasibleIsTrue = refl

outputRelocationUnitWeightSymbolicCheckAClosedIsTrue :
  outputRelocationUnitWeightSymbolicCheckAClosed ≡ true
outputRelocationUnitWeightSymbolicCheckAClosedIsTrue = refl

outputRelocationIntegerGeometricEnvelopeClosedIsTrue :
  outputRelocationIntegerGeometricEnvelopeClosed ≡ true
outputRelocationIntegerGeometricEnvelopeClosedIsTrue = refl

outputRelocationRationalFiniteSummationClosedIsTrue :
  outputRelocationRationalFiniteSummationClosed ≡ true
outputRelocationRationalFiniteSummationClosedIsTrue = refl

outputRelocationPositiveKernelProgramClosedIsTrue :
  outputRelocationPositiveKernelProgramClosed ≡ true
outputRelocationPositiveKernelProgramClosedIsTrue = refl

outputRelocationThreeShellSchurConditionsClosedIsTrue :
  outputRelocationThreeShellSchurConditionsClosed ≡ true
outputRelocationThreeShellSchurConditionsClosedIsTrue = refl

outputRelocationFiniteSignedDominationClosedIsTrue :
  outputRelocationFiniteSignedDominationClosed ≡ true
outputRelocationFiniteSignedDominationClosedIsTrue = refl

outputRelocationConditionalArchetypeClosedIsTrue :
  outputRelocationConditionalArchetypeClosed ≡ true
outputRelocationConditionalArchetypeClosedIsTrue = refl

outputRelocationTwoPowerDominationTheoremsClosedIsTrue :
  outputRelocationTwoPowerDominationTheoremsClosed ≡ true
outputRelocationTwoPowerDominationTheoremsClosedIsTrue = refl

outputRelocationAbsoluteCoefficientDerivationClosedIsTrue :
  outputRelocationAbsoluteCoefficientDerivationClosed ≡ true
outputRelocationAbsoluteCoefficientDerivationClosedIsTrue = refl

outputRelocationFourFormerRawBridgeFieldsDerivedIsTrue :
  outputRelocationFourFormerRawBridgeFieldsDerived ≡ true
outputRelocationFourFormerRawBridgeFieldsDerivedIsTrue = refl

outputRelocationNativeSpineDerivedClosureTheoremClosedIsTrue :
  outputRelocationNativeSpineDerivedClosureTheoremClosed ≡ true
outputRelocationNativeSpineDerivedClosureTheoremClosedIsTrue = refl

outputRelocationFinalArchetypeCutsetSpecifiedIsTrue :
  outputRelocationFinalArchetypeCutsetSpecified ≡ true
outputRelocationFinalArchetypeCutsetSpecifiedIsTrue = refl

nextLeafIsConcreteShellBridgeIsTrue :
  nextLeafIsConcreteShellBridge ≡ true
nextLeafIsConcreteShellBridgeIsTrue = refl

nextLeafIsConstructivePowerMonotonicityBridgeIsTrue :
  nextLeafIsConstructivePowerMonotonicityBridge ≡ true
nextLeafIsConstructivePowerMonotonicityBridgeIsTrue = refl

nextLeafIsConcreteNativeSpineCapabilityIsTrue :
  nextLeafIsConcreteNativeSpineCapability ≡ true
nextLeafIsConcreteNativeSpineCapabilityIsTrue = refl

nextLeafIsConcreteBaseTwoPowerDataIsTrue :
  nextLeafIsConcreteBaseTwoPowerData ≡ true
nextLeafIsConcreteBaseTwoPowerDataIsTrue = refl

nextLeafIsLiteralAbsoluteCoefficientEstimateIsTrue :
  nextLeafIsLiteralAbsoluteCoefficientEstimate ≡ true
nextLeafIsLiteralAbsoluteCoefficientEstimateIsTrue = refl

nextLeafIsConstructiveDyadicTailIsFalse :
  nextLeafIsConstructiveDyadicTail ≡ false
nextLeafIsConstructiveDyadicTailIsFalse = refl

nextLeafIsWeightAnsatzRevisionIsFalse : nextLeafIsWeightAnsatzRevision ≡ false
nextLeafIsWeightAnsatzRevisionIsFalse = refl

nextLeafIsNumericBasesDirectionsAndDyadicTailIsFalse :
  nextLeafIsNumericBasesDirectionsAndDyadicTail ≡ false
nextLeafIsNumericBasesDirectionsAndDyadicTailIsFalse = refl

outputRelocationCheckAClosedIsFalse : outputRelocationCheckAClosed ≡ false
outputRelocationCheckAClosedIsFalse = refl
