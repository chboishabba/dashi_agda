module DASHI.Analysis.RiemannG2HASourceProducerHyperedgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannFormulaAnalyticCompatibility as Compat
import DASHI.Analysis.RiemannG2SourceNativePhiHatModulationAdapterExact as Source
import DASHI.Analysis.RiemannG2HAConsumerQuotientActiveSearchExact as HA
import DASHI.Analysis.RiemannG2HARecoveryDependencyFrontierExact as Frontier
import DASHI.Analysis.RiemannG2HAProofCarryingRecoveryTraceExact as Trace

------------------------------------------------------------------------
-- SOURCE PRODUCER GRANULARITY
--
-- The coordinate frontier is useful for dependency analysis, but the actual
-- source-native compiler already reveals a stronger producer shape:
--
--   SourceNativePhiHatModulation P
--      owns BOTH source-test identity and the parameterized source action;
--
--   SourceNativePhiHatModulationProof P
--      owns ALL FOUR theorem-bearing consequences for that SAME P.
--
-- Therefore source recovery should not assume that six coordinates must be
-- acquired by six unrelated searches.  A theorem-bearing source object may pay
-- several dependency coordinates at once.  This owner makes those joint
-- producer hyperedges explicit without claiming that either source object has
-- already been recovered from the external companion project.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Recovery-path composition.
------------------------------------------------------------------------

appendRecoveryPath :
  ∀ {start middle finish} →
  Trace.RecoveryPath start middle →
  Trace.RecoveryPath middle finish →
  Trace.RecoveryPath start finish
appendRecoveryPath Trace.recoveryDone right = right
appendRecoveryPath (Trace.recoveryThen step rest) right =
  Trace.recoveryThen step (appendRecoveryPath rest right)

------------------------------------------------------------------------
-- 2. The source-native object is a TWO-coordinate producer hyperedge.
------------------------------------------------------------------------

record SourceBaseProducer
    (analytic : Analytic.AnalyticSubstrate)
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula)
    : Set₁ where
  constructor source-base-producer
  field
    producer : Source.SourceNativePhiHatModulation analytic space formula compat

open SourceBaseProducer public

sourceBaseProducerWidth : Nat
sourceBaseProducerWidth = suc (suc zero)

sourceBaseProducerPaysTwoRecoveryCoordinates :
  ∀ {analytic space formula compat} →
  SourceBaseProducer analytic space formula compat →
  Trace.RecoveryPath Frontier.allMissingState Frontier.postTransportState
sourceBaseProducerPaysTwoRecoveryCoordinates receipt =
  Trace.implementationThenAction

------------------------------------------------------------------------
-- 3. The proof object is a FOUR-coordinate theorem hyperedge on the SAME P.
------------------------------------------------------------------------

record SourceProofBundle
    {analytic : Analytic.AnalyticSubstrate}
    {space : Weil.WeilTestSpace}
    {formula : Explicit.RiemannExplicitFormula space}
    {compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula}
    (P : Source.SourceNativePhiHatModulation analytic space formula compat)
    : Set₁ where
  constructor source-proof-bundle
  field
    proof : Source.SourceNativePhiHatModulationProof P

open SourceProofBundle public

sourceProofBundleWidth : Nat
sourceProofBundleWidth = suc (suc (suc (suc zero)))

sourceProofBundlePaysFourRecoveryCoordinates :
  ∀ {analytic space formula compat}
    {P : Source.SourceNativePhiHatModulation analytic space formula compat} →
  SourceProofBundle P →
  Trace.RecoveryPath Frontier.postTransportState HA.mathReadyAnonymous
sourceProofBundlePaysFourRecoveryCoordinates bundle =
  Trace.recoveryThen Trace.recoverAdmissibilityProof
    (Trace.recoveryThen Trace.recoverHXAgreementProof
      (Trace.recoveryThen Trace.recoverFormulaShiftProof
        (Trace.recoveryThen Trace.recoverWeilShiftProof Trace.recoveryDone)))

------------------------------------------------------------------------
-- 4. Same-object source compiler path.
--
-- The proof bundle is indexed by the exact source object P.  Thus the combined
-- path cannot silently use one source-test/action object for transport and an
-- unrelated object for admissibility or shift proofs.
------------------------------------------------------------------------

record CompleteSourceMathematicalProducer
    (analytic : Analytic.AnalyticSubstrate)
    (space : Weil.WeilTestSpace)
    (formula : Explicit.RiemannExplicitFormula space)
    (compat : Compat.RiemannFormulaAnalyticCompatibility analytic space formula)
    : Set₁ where
  constructor complete-source-mathematical-producer
  field
    P : Source.SourceNativePhiHatModulation analytic space formula compat
    PProof : Source.SourceNativePhiHatModulationProof P

open CompleteSourceMathematicalProducer public

completeSourceProducerPaysMathematicalHARecovery :
  ∀ {analytic space formula compat} →
  CompleteSourceMathematicalProducer analytic space formula compat →
  Trace.RecoveryPath Frontier.allMissingState HA.mathReadyAnonymous
completeSourceProducerPaysMathematicalHARecovery receipt =
  appendRecoveryPath
    (sourceBaseProducerPaysTwoRecoveryCoordinates
      (source-base-producer (P receipt)))
    (sourceProofBundlePaysFourRecoveryCoordinates
      (source-proof-bundle (PProof receipt)))

completeSourceProducerClosesMathematicalConsumer :
  ∀ {analytic space formula compat} →
  CompleteSourceMathematicalProducer analytic space formula compat →
  Frontier.MathematicalHAClosed HA.mathReadyAnonymous
completeSourceProducerClosesMathematicalConsumer receipt = tt

completeSourceProducerDoesNotCloseSourceAuditByItself :
  ∀ {analytic space formula compat} →
  CompleteSourceMathematicalProducer analytic space formula compat →
  Frontier.SourceAuditClosed HA.mathReadyAnonymous → ⊥
completeSourceProducerDoesNotCloseSourceAuditByItself receipt x = x

------------------------------------------------------------------------
-- 5. Producer-level search language.
------------------------------------------------------------------------

data HAProducerSearchTarget : Set where
  recoverSourceNativeObject
  recoverSourceNativeProofBundle
  recoverIndependentSourceProvenance
  compileMathematicalHA
  : HAProducerSearchTarget

producerCoordinateWidth : HAProducerSearchTarget → Nat
producerCoordinateWidth recoverSourceNativeObject = sourceBaseProducerWidth
producerCoordinateWidth recoverSourceNativeProofBundle = sourceProofBundleWidth
producerCoordinateWidth recoverIndependentSourceProvenance = suc zero
producerCoordinateWidth compileMathematicalHA = zero

baseProducerWidthIsTwo :
  producerCoordinateWidth recoverSourceNativeObject ≡ suc (suc zero)
baseProducerWidthIsTwo = refl

proofProducerWidthIsFour :
  producerCoordinateWidth recoverSourceNativeProofBundle
  ≡ suc (suc (suc (suc zero)))
proofProducerWidthIsFour = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record HASourceProducerHyperedgeBoundary : Set where
  constructor ha-source-producer-hyperedge-boundary
  field
    oneRecoveryCoordinateRequiresOneIndependentSourceSearch : Bool
    oneRecoveryCoordinateRequiresOneIndependentSourceSearchIsFalse :
      oneRecoveryCoordinateRequiresOneIndependentSourceSearch ≡ false

    sourceNativeObjectJointlyOwnsIdentityAndAction : Bool
    sourceNativeObjectJointlyOwnsIdentityAndActionIsTrue :
      sourceNativeObjectJointlyOwnsIdentityAndAction ≡ true

    sourceNativeProofJointlyOwnsFourTheoremConsequences : Bool
    sourceNativeProofJointlyOwnsFourTheoremConsequencesIsTrue :
      sourceNativeProofJointlyOwnsFourTheoremConsequences ≡ true

    proofBundleMayReferToDifferentSourceObjectThanTransport : Bool
    proofBundleMayReferToDifferentSourceObjectThanTransportIsFalse :
      proofBundleMayReferToDifferentSourceObjectThanTransport ≡ false

    completeSourceProducerAlreadyRecoveredOnThisBranch : Bool
    completeSourceProducerAlreadyRecoveredOnThisBranchIsFalse :
      completeSourceProducerAlreadyRecoveredOnThisBranch ≡ false

    sourceProvenanceAutomaticallyFollowsFromMathematicalProducer : Bool
    sourceProvenanceAutomaticallyFollowsFromMathematicalProducerIsFalse :
      sourceProvenanceAutomaticallyFollowsFromMathematicalProducer ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalHASourceProducerHyperedgeBoundary : HASourceProducerHyperedgeBoundary
canonicalHASourceProducerHyperedgeBoundary =
  ha-source-producer-hyperedge-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    "Refine the H_A search graph from coordinate-level leaves to actual source-producer hyperedges. The existing SourceNativePhiHatModulation record jointly owns source-test identity and source action; its proof object, indexed by that exact same producer P, jointly owns admissibility, canonical-H_X agreement, same-formula spectral shift and same-Weil-transform shift. Consequently one recovered source object can pay two recovery coordinates and one recovered theorem bundle can pay four more. Search should target those real producer objects before assuming six unrelated proof hunts. Neither object is claimed recovered here, provenance remains an independent audit payment, and RH is not derived."
