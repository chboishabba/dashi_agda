module DASHI.Analysis.RiemannG2HASingleSourceProducerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.RiemannG2ConstructedComplexAnalyticCarrierAdapterExact as Carrier
import DASHI.Analysis.RiemannG2CanonicalTestModulationProofRelevantExact as StrongHA
import DASHI.Analysis.RiemannG2SourceNativePhiHatModulationAdapterExact as Source
import DASHI.Analysis.RiemannG2HAConsumerQuotientActiveSearchExact as HA
import DASHI.Analysis.RiemannG2HARecoveryDependencyFrontierExact as Frontier
import DASHI.Analysis.RiemannG2HAProofCarryingRecoveryTraceExact as Trace

------------------------------------------------------------------------
-- SINGLE-SOURCE-PRODUCER BIDI CUT FOR H_A
--
-- Recent Monster/zeta recovery work exposed a useful general BIDI correction:
-- if a literal producer already contains several coordinates and a theorem
-- bundle indexed by that SAME producer supplies the remaining consequences,
-- those coordinates are compiler outputs of one recovered object rather than
-- independent scientific inputs.
--
-- The RH H_A source adapter has exactly that shape:
--
--   P : SourceNativePhiHatModulation
--       owns source-test identity + parameterized source action;
--
--   SourceNativePhiHatModulationProof P
--       owns admissibility + canonical H_X agreement
--       + same-formula spectral shift + same-Weil-transform shift.
--
-- Hence the mathematical H_A source search can be collapsed to one dependent
-- producer package.  Provenance remains a separate audit coordinate.
------------------------------------------------------------------------

record ActualHASingleSourceProducer
    (analytic : Analytic.AnalyticSubstrate)
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula)
    : Set₁ where
  field
    sourceObject :
      Source.SourceNativePhiHatModulation analytic space formula compat
    sourceProof :
      Source.SourceNativePhiHatModulationProof sourceObject

open ActualHASingleSourceProducer public

------------------------------------------------------------------------
-- 1. The old six-coordinate mathematical recovery state is compiler output.
------------------------------------------------------------------------

singleProducerMathematicalTerminal :
  ∀ {analytic space formula compat} →
  ActualHASingleSourceProducer analytic space formula compat →
  HA.HARecoveryState
singleProducerMathematicalTerminal producer = HA.mathReadyAnonymous

singleProducerClosesMathematicalConsumer :
  ∀ {analytic space formula compat} →
  (producer : ActualHASingleSourceProducer analytic space formula compat) →
  Frontier.MathematicalHAClosed (singleProducerMathematicalTerminal producer)
singleProducerClosesMathematicalConsumer producer = tt

singleProducerRecoveryPath :
  ∀ {analytic space formula compat} →
  ActualHASingleSourceProducer analytic space formula compat →
  Trace.RecoveryPath Frontier.allMissingState HA.mathReadyAnonymous
singleProducerRecoveryPath producer =
  Trace.recoveryThen Trace.recoverImplementation
    (Trace.recoveryThen Trace.recoverAction
      (Trace.recoveryThen Trace.recoverAdmissibilityProof
        (Trace.recoveryThen Trace.recoverHXAgreementProof
          (Trace.recoveryThen Trace.recoverFormulaShiftProof
            (Trace.recoveryThen Trace.recoverWeilShiftProof Trace.recoveryDone)))))

------------------------------------------------------------------------
-- 2. More importantly, the producer compiles to the actual theorem-bearing H_A
--    object, not merely to a status ledger.
------------------------------------------------------------------------

singleProducerToProofRelevantCanonicalHA :
  ∀ {analytic space formula compat C F realization} →
  ActualHASingleSourceProducer analytic space formula compat →
  StrongHA.ProofRelevantCanonicalTestModulation
    analytic space formula compat C F realization
singleProducerToProofRelevantCanonicalHA producer =
  HA.sourceNativeToProofRelevantCanonicalHA
    (sourceObject producer)
    (sourceProof producer)

------------------------------------------------------------------------
-- 3. Search consequences.
------------------------------------------------------------------------

data HASingleProducerSearchAction : Set where
  recoverLiteralSourceNativeProducer
  separatelyRecoverImplementationIdentity
  separatelyRecoverParameterizedAction
  separatelyRecoverAdmissibility
  separatelyRecoverCanonicalHXAgreement
  separatelyRecoverSameFormulaShift
  separatelyRecoverSameWeilTransformShift
  recoverIndependentSourceProvenance
  compileProofRelevantHA
  : HASingleProducerSearchAction

data SearchStatus : Set where
  live pruned downstream parallel : SearchStatus

searchStatus : HASingleProducerSearchAction → SearchStatus
searchStatus recoverLiteralSourceNativeProducer = live
searchStatus separatelyRecoverImplementationIdentity = pruned
searchStatus separatelyRecoverParameterizedAction = pruned
searchStatus separatelyRecoverAdmissibility = pruned
searchStatus separatelyRecoverCanonicalHXAgreement = pruned
searchStatus separatelyRecoverSameFormulaShift = pruned
searchStatus separatelyRecoverSameWeilTransformShift = pruned
searchStatus recoverIndependentSourceProvenance = parallel
searchStatus compileProofRelevantHA = downstream

identitySearchPruned :
  searchStatus separatelyRecoverImplementationIdentity ≡ pruned
identitySearchPruned = refl

actionSearchPruned :
  searchStatus separatelyRecoverParameterizedAction ≡ pruned
actionSearchPruned = refl

sameFormulaSearchPruned :
  searchStatus separatelyRecoverSameFormulaShift ≡ pruned
sameFormulaSearchPruned = refl

------------------------------------------------------------------------
-- 4. Provenance remains orthogonal to mathematical closure.
------------------------------------------------------------------------

singleProducerDoesNotCloseSourceAudit :
  ∀ {analytic space formula compat} →
  (producer : ActualHASingleSourceProducer analytic space formula compat) →
  Frontier.SourceAuditClosed (singleProducerMathematicalTerminal producer) → ⊥
singleProducerDoesNotCloseSourceAudit producer x = x

record HASingleSourceProducerBoundary : Set where
  constructor ha-single-source-producer-boundary
  field
    sixMathematicalCoordinatesAreIndependentScientificInputs : Bool
    sixMathematicalCoordinatesAreIndependentScientificInputsIsFalse :
      sixMathematicalCoordinatesAreIndependentScientificInputs ≡ false

    oneDependentSourceProducerCanGenerateMathematicalHA : Bool
    oneDependentSourceProducerCanGenerateMathematicalHAIsTrue :
      oneDependentSourceProducerCanGenerateMathematicalHA ≡ true

    theoremBundleMustBeIndexedBySameSourceObject : Bool
    theoremBundleMustBeIndexedBySameSourceObjectIsTrue :
      theoremBundleMustBeIndexedBySameSourceObject ≡ true

    provenanceIsGeneratedByMathematicalProducer : Bool
    provenanceIsGeneratedByMathematicalProducerIsFalse :
      provenanceIsGeneratedByMathematicalProducer ≡ false

    actualSingleSourceProducerRecoveredHere : Bool
    actualSingleSourceProducerRecoveredHereIsFalse :
      actualSingleSourceProducerRecoveredHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalHASingleSourceProducerBoundary : HASingleSourceProducerBoundary
canonicalHASingleSourceProducerBoundary =
  ha-single-source-producer-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "Cross-pollinate the recent Monster/zeta single-producer lesson at search-architecture level only. The literal RH source-native modulation object already jointly owns source-test identity and action, and its proof object is dependent on that exact producer and jointly owns the four theorem consequences. Therefore the six mathematical H_A recovery coordinates are best read as projections/compiler outputs of one dependent producer package, not six independent scientific source leaves. Recover that one literal source producer, compile the existing proof-relevant H_A, and keep provenance as a parallel audit payment. This owner does not recover the producer and does not derive RH."
