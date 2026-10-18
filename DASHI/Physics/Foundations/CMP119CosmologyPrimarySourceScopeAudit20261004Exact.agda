{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPrimarySourceScopeAudit20261004Exact where

------------------------------------------------------------------------
-- PRIMARY-SOURCE SCOPE AUDIT / 2026-10-04.
--
-- This file answers a deliberately narrower question than the max-cut owners:
-- do the currently imported Bałaban CMP109/116/119/122 source surfaces already
-- prove the six irreducible cosmology source theorems, or would claiming those
-- theorems add new mathematics/same-object physics?
--
-- Result: the imported source surfaces are strong enough for the RG/locality
-- machinery that feeds the compilers, but they do NOT determine the remaining
-- signed covariance, pair semantics, absolute same-sequence identities, or the
-- strict cosmological metric-response gap.  Existing finite countermodels and
-- proof-level receipts below make each failure mode explicit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel; promotable)

import DASHI.Physics.YangMills.BalabanCMP109116SourceContinuationRound103Exact as CMP109116
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as CMP119Expectation
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as CMP119Raw
import DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact as R110

import DASHI.Physics.Foundations.CMP119CosmologyE1LinearityDoesNotForceB4CovarianceExact as A1NoGo
import DASHI.Physics.Foundations.CMP119CosmologyA1UnsignedTangentSignFirewallExact as A1Sign
import DASHI.Physics.Foundations.CMP119CosmologyR109PairObservableUnderdeterminationExact as A2NoGo
import DASHI.Physics.Foundations.CMP119CosmologyA2LocalCWilsonPresentationCompilerExact as A2
import DASHI.Physics.Foundations.CMP119CosmologyR109AbsoluteExpectationAnchorNoGoExact as B1NoGo
import DASHI.Physics.Foundations.CMP119CosmologyB1SelectedSameSequenceMaxCutExact as B1
import DASHI.Physics.Foundations.CMP119CosmologyEq223ERBMetricVariationUnderdeterminationExact as B2ERBNoGo
import DASHI.Physics.Foundations.CMP119CosmologyEq223VacuumMetricSignUnderdeterminationExact as B2VacuumNoGo
import DASHI.Physics.Foundations.CMP119CosmologyB2StrictSourceGapEventuallyPaysTailExact as B2
import DASHI.Physics.Foundations.CMP119CosmologyIrreducibleSourceTheorems20261004Exact as Frontier

------------------------------------------------------------------------
-- What the cited source layer DOES own.
------------------------------------------------------------------------

cmp109116ContinuationSourceLevel : ProofLevel
cmp109116ContinuationSourceLevel =
  CMP109116.cmp116PartIIContinuesPartIEffectiveActionLevel

cmp109116LiteralRepositoryInstantiationLevel : ProofLevel
cmp109116LiteralRepositoryInstantiationLevel =
  CMP109116.literalRepositoryCMP109116ContinuationInstantiationLevel

cmp116119CompatibleExpectationSourceLevel : ProofLevel
cmp116119CompatibleExpectationSourceLevel =
  CMP119Expectation.cmp116CMP119CompatibleExpectationSourceLevel

cmp122ActiveRawSourceInstantiationLevel : ProofLevel
cmp122ActiveRawSourceInstantiationLevel =
  CMP119Raw.cmp122Theorem1ToActiveRawSourceStateLevel

literalStressCompletionProvenanceLevel : ProofLevel
literalStressCompletionProvenanceLevel =
  R110.literalCMP119StressCompletionProvenanceLevel

cmp109116LiteralInstantiationPromotable : Bool
cmp109116LiteralInstantiationPromotable =
  promotable cmp109116LiteralRepositoryInstantiationLevel

cmp122ActiveRawSourceInstantiationPromotable : Bool
cmp122ActiveRawSourceInstantiationPromotable =
  promotable cmp122ActiveRawSourceInstantiationLevel

literalStressCompletionProvenancePromotable : Bool
literalStressCompletionProvenancePromotable =
  promotable literalStressCompletionProvenanceLevel

------------------------------------------------------------------------
-- A1: imported first-variation linearity/localized-action structure does not
-- determine the signed B4 covariance law.  Axis flips require an independent
-- basis sign that an unsigned component permutation cannot supply.
------------------------------------------------------------------------

a1LinearityAloneForcesSignedCovariance : Bool
a1LinearityAloneForcesSignedCovariance =
  A1NoGo.additiveFirstVariationLinearityForcesSymmetryCovariance

a1UnsignedPermutationAlonePaysSignedReadout : Bool
a1UnsignedPermutationAlonePaysSignedReadout =
  A1Sign.unsignedComponentPermutationAlonePaysA1

a1StillNeedsNewSignedSourceLaw : Bool
a1StillNeedsNewSignedSourceLaw =
  A1Sign.terminalA1SourceLawMustBeSignedReadoutCovariance

------------------------------------------------------------------------
-- A2: CMP116/119 local analytic insertion theory controls a source-native pair,
-- but the pair carrier contains no Configuration -> R evaluator.  The Local-C
-- Wilson application pays observable choice/admissibility only AFTER a
-- same-object semantics theorem identifies the Round109 pair with that image.
------------------------------------------------------------------------

a2BarePairCarriesObservableEvaluator : Bool
a2BarePairCarriesObservableEvaluator =
  A2NoGo.r109PairCarrierContainsSelectedObservableEvaluator

a2WilsonCompilerPaysObservableAndAdmissibility : Bool
a2WilsonCompilerPaysObservableAndAdmissibility =
  A2.localCStressEncodingPaysObservableChoice

a2PairToLocalCMeaningAlreadyPaid : Bool
a2PairToLocalCMeaningAlreadyPaid =
  A2.a2Round109PairToLocalCObservableSemanticsPaid

a2StillNeedsSameObjectSemantics : Bool
a2StillNeedsSameObjectSemantics =
  A2.remainingA2SourceDebtIsPairToObservableSameObjectSemantics

------------------------------------------------------------------------
-- B1: Round109 difference/tail data are translation-invariant and therefore
-- cannot fix an absolute finite expectation or the R136 endpoint.  The direct
-- tail inequality is compiler output only once the three same-sequence facts
-- in B1SelectedSameSequenceMaxCut are supplied.
------------------------------------------------------------------------

b1DifferenceDataFixAbsoluteLevel : Bool
b1DifferenceDataFixAbsoluteLevel =
  B1NoGo.round109DifferenceDataFixAbsoluteAdditiveConstant

b1AbsoluteAnchorIsAdditionalInformation : Bool
b1AbsoluteAnchorIsAdditionalInformation =
  B1NoGo.absoluteExpectationAnchorIsGenuineAdditionalInformation

b1Round109FiniteTailSemanticsStillSource : Bool
b1Round109FiniteTailSemanticsStillSource =
  B1.round109FiniteTailSemanticsIsSourceLeaf

b1CompletionEndpointIdentityStillSource : Bool
b1CompletionEndpointIdentityStillSource =
  B1.completionEndpointIdentityIsSourceLeaf

b1AllCutoffR144AttachmentStillSource : Bool
b1AllCutoffR144AttachmentStillSource =
  B1.allCutoffR144FiniteAttachmentIsSourceLeaf

------------------------------------------------------------------------
-- B2: CMP119/CMP122 Section-2 object identity, localization and small-coupling
-- regularity do not determine a metric trace or the vacuum metric sign.  Both
-- can be varied while holding the raw Eq.(2.23) source object fixed.
------------------------------------------------------------------------

b2RawSourceFixesERBMetricTrace : Bool
b2RawSourceFixesERBMetricTrace = false

b2RawSourceFixesVacuumMetricSign : Bool
b2RawSourceFixesVacuumMetricSign = false

b2NeedsSourceBackedERBMetricVariation : Bool
b2NeedsSourceBackedERBMetricVariation = true

b2NeedsSourceBackedVacuumMetricVariation : Bool
b2NeedsSourceBackedVacuumMetricVariation = true

b2StrictCoefficientGapStillSourcePhysics : Bool
b2StrictCoefficientGapStillSourcePhysics =
  B2.strictCoefficientGapIsSourcePhysics

------------------------------------------------------------------------
-- Final source audit.
------------------------------------------------------------------------

irreducibleSourceTheoremCount : Nat
irreducibleSourceTheoremCount = Frontier.irreducibleSourceTheoremCount

remainingAdapterConstructionCount : Nat
remainingAdapterConstructionCount = 0

currentPrimarySourceSurfaceClosesAllIrreducibleCosmologyTheorems : Bool
currentPrimarySourceSurfaceClosesAllIrreducibleCosmologyTheorems = false

claimingAllSixClosedFromCurrentImportedSourceWouldAddNewMathematics : Bool
claimingAllSixClosedFromCurrentImportedSourceWouldAddNewMathematics = true
