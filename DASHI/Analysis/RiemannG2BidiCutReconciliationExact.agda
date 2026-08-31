module DASHI.Analysis.RiemannG2BidiCutReconciliationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannAristotleG2CurrentCutExact as G2
import DASHI.Analysis.RiemannAristotleCurrentFrontierExact as Frontier
import DASHI.Analysis.RiemannAristotleFiniteNearCoreSchurCompilerExact as Schur
import DASHI.Analysis.RiemannG2LiteralSpectralZeroWeldExact as Spectral
import DASHI.Core.FrontierRelationStrengthBidiExact as Relation

------------------------------------------------------------------------
-- BIDI RECONCILIATION OF TWO RH FRONTIER DESCRIPTIONS
--
-- `RiemannAristotleG2CurrentCutExact` names a concrete sufficient harmonic
-- producer: a target-centred weighted local-zero cosine/exponential-sum bound.
-- `RiemannAristotleCurrentFrontierExact` names the consumer-facing payment after
-- deterministic Schur elimination: a bound on the finite post-Schur near-core
-- energy ||E D_near(J)||^2.
--
-- They are not competing frontiers and they are not definitionally the same
-- theorem.  The scalar harmonic estimate is one candidate producer for the
-- post-Schur finite-near payment.  This file makes that BIDI direction explicit.
------------------------------------------------------------------------

data FrontierLevel : Set where
  scalarLocalZeroProducer
  finitePostSchurNearConsumer
  jointNearFarMarginConsumer
  finalRHConsumer
  : FrontierLevel

record G2ScalarToFiniteSchurBridge : Set₁ where
  constructor g2ScalarToFiniteSchurBridge
  field
    ScalarEstimate : Set
    scalarEstimate : ScalarEstimate

    FiniteNearEnergyBound : Set
    finiteNearEnergyBound : FiniteNearEnergyBound

    literalNearCarrierIdentity : Set
    taperWeightIdentity : Set
    scalarToThreeTaperAssembly : Set
    schurEliminationTransport : Set
    boundTransport : Set

    bridgeReference : String

open G2ScalarToFiniteSchurBridge public

------------------------------------------------------------------------
-- Current statuses inherited from their authoritative owners.
------------------------------------------------------------------------

g2ScalarProducerStillOpen :
  G2.targetCenteredLocalZeroExponentialSumBoundClosed
    G2.canonicalAristotleG2CurrentCut ≡ false
g2ScalarProducerStillOpen =
  G2.targetCenteredLocalZeroExponentialSumBoundClosedIsFalse
    G2.canonicalAristotleG2CurrentCut

finitePostSchurNearConsumerStillOpen :
  Frontier.finiteSignedNearSchurCancellationClosed
    Frontier.canonicalAristotleCurrentFrontier ≡ false
finitePostSchurNearConsumerStillOpen =
  Frontier.finiteSignedNearSchurCancellationClosedIsFalse
    Frontier.canonicalAristotleCurrentFrontier

jointNearFarMarginStillOpen :
  Frontier.jointFiniteNearFarMarginClosed
    Frontier.canonicalAristotleCurrentFrontier ≡ false
jointNearFarMarginStillOpen =
  Frontier.jointFiniteNearFarMarginClosedIsFalse
    Frontier.canonicalAristotleCurrentFrontier

finiteSchurConsumerCompilerAlreadyClosed :
  Schur.scalarPerturbationConsumerClosedInAgda
    Schur.canonicalFiniteNearCoreSchurBoundary ≡ true
finiteSchurConsumerCompilerAlreadyClosed =
  Schur.scalarPerturbationConsumerClosedInAgdaIsTrue
    Schur.canonicalFiniteNearCoreSchurBoundary

------------------------------------------------------------------------
-- Route relation.
------------------------------------------------------------------------

scalarToSchurRelation : Relation.RelationKind
scalarToSchurRelation = Relation.exactLemmaConsumerBridge

-- This constructor is intentionally available only once the exact bridge
-- record is inhabited.  Naming both expressions as "the remaining RH bound"
-- is not sufficient.
record AdmittedG2ScalarRoute : Set₁ where
  constructor admittedG2ScalarRoute
  field
    bridge : G2ScalarToFiniteSchurBridge
    exactConsumerBridge : Relation.TheoremTransferCapability scalarToSchurRelation
    routeReference : String

open AdmittedG2ScalarRoute public

------------------------------------------------------------------------
-- The new spectral-zero weld sits upstream of this route.  Even a successful
-- explicit-formula same-object identification does not skip the scalar-to-Schur
-- transport or prove signed cancellation automatically.
------------------------------------------------------------------------

spectralWeldAloneCannotCloseFiniteNear :
  Relation.TheoremTransferCapability Spectral.literalSpectralWeldRelation → ⊥
spectralWeldAloneCannotCloseFiniteNear =
  Relation.sameObjectAloneCannotDirectlyTransferTheorem

scalarToFiniteSchurBridgeRecovered : Bool
scalarToFiniteSchurBridgeRecovered = false

scalarToFiniteSchurBridgeRecoveredIsFalse :
  scalarToFiniteSchurBridgeRecovered ≡ false
scalarToFiniteSchurBridgeRecoveredIsFalse = refl

record G2BidiCutBoundary : Set where
  constructor g2BidiCutBoundary
  field
    scalarLeafAndPostSchurLeafAreDefinitionallySameTheorem : Bool
    scalarLeafAndPostSchurLeafAreDefinitionallySameTheoremIsFalse :
      scalarLeafAndPostSchurLeafAreDefinitionallySameTheorem ≡ false

    scalarLeafCanBeAProducerForPostSchurLeaf : Bool
    scalarLeafCanBeAProducerForPostSchurLeafIsTrue :
      scalarLeafCanBeAProducerForPostSchurLeaf ≡ true

    finiteSchurCompilerIsAlreadyTheResearchBottleneck : Bool
    finiteSchurCompilerIsAlreadyTheResearchBottleneckIsFalse :
      finiteSchurCompilerIsAlreadyTheResearchBottleneck ≡ false

    actualResearchPaymentIsFiniteSignedNearBound : Bool
    actualResearchPaymentIsFiniteSignedNearBoundIsTrue :
      actualResearchPaymentIsFiniteSignedNearBound ≡ true

canonicalG2BidiCutBoundary : G2BidiCutBoundary
canonicalG2BidiCutBoundary =
  g2BidiCutBoundary
    false refl
    true refl
    false refl
    true refl
