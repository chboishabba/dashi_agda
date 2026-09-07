module DASHI.Analysis.RiemannG2ConcreteProducerPairToPrizeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set₂)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2CertifiedFiniteNearToOffPaymentExact as Off
import DASHI.Analysis.RiemannG2FreshSameTaperGammaEnvelopeCompilerExact as Gamma
import DASHI.Analysis.RiemannG2PoleQuotientProducerAllowanceTargetExact as Payment
import DASHI.Analysis.RiemannG2AllowancePaymentsToAnalyticCoresExact as Factor
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic

------------------------------------------------------------------------
-- CONCRETE PRODUCER PAIR -> TWO MINIMAL ANALYTIC CORES
--
-- This owner removes the last API-level gap between the two concrete preferred
-- producer families and the prize-facing high-zero compiler.
--
-- Off is supplied by the proof-carrying finite-near route.
-- Gamma is supplied by a fresh envelope on the literal final taper.
-- Both first compile their historical terminal payment records; the generic
-- factorization owner then projects those payments into the minimal analytic
-- cores plus representation attachments, definitionally preserving the same
-- payment data.
------------------------------------------------------------------------

record ConcreteHighOrdinateProducerPair : Set₂ where
  field
    offSpace : Weil.WeilTestSpace
    offFormula : Explicit.RiemannExplicitFormula offSpace
    offWindow : Window.PoleNearTargetWindow offSpace offFormula
    offSurface : NearFar.OrderedAdditiveNearFarSurface
    offTransport : Transport.ExplicitCutoffNearFarAgdaTransport offSurface

    offPacket :
      Off.CertifiedFiniteNearUpperOffPacket
        offSpace offFormula offWindow offSurface offTransport

    gammaEnvelope : Gamma.FreshSameTaperGammaEnvelope
    gammaAllowance :
      Gamma.FreshSameTaperGammaAllowanceInput gammaEnvelope

    producerReference : String

open ConcreteHighOrdinateProducerPair public

concreteOffPayment :
  ConcreteHighOrdinateProducerPair →
  Payment.PoleQuotientOffAllowancePayment
concreteOffPayment pair =
  Off.compileCertifiedFiniteNearUpperOffPayment (offPacket pair)

concreteGammaPayment :
  ConcreteHighOrdinateProducerPair →
  Payment.PoleQuotientGammaAllowancePayment
concreteGammaPayment pair =
  Gamma.compileFreshSameTaperGammaAllowancePayment
    (gammaEnvelope pair)
    (gammaAllowance pair)

concreteOffCore :
  ConcreteHighOrdinateProducerPair → Core.OffAnalyticCore
concreteOffCore pair =
  Factor.offPaymentToAnalyticCore (concreteOffPayment pair)

concreteGammaCore :
  ConcreteHighOrdinateProducerPair → Core.GammaAnalyticCore
concreteGammaCore pair =
  Factor.gammaPaymentToAnalyticCore (concreteGammaPayment pair)

concreteTwoAnalyticCores :
  ConcreteHighOrdinateProducerPair →
  Core.FinalPoleQuotientTwoAnalyticCores
concreteTwoAnalyticCores pair = record
  { Core.offCore = concreteOffCore pair
  ; Core.gammaCore = concreteGammaCore pair
  ; Core.analyticReference = producerReference pair
  }

concreteAnalyticCoreAttachments :
  (pair : ConcreteHighOrdinateProducerPair) →
  Core.FinalPoleQuotientAnalyticCoreAttachments
    (concreteTwoAnalyticCores pair)
concreteAnalyticCoreAttachments pair = record
  { Core.offAttachment =
      Factor.offPaymentToRepresentationAttachment (concreteOffPayment pair)
  ; Core.gammaAttachment =
      Factor.gammaPaymentToRepresentationAttachment (concreteGammaPayment pair)
  ; Core.attachmentReference = producerReference pair
  }

concreteOffPaymentRoundTrip :
  (pair : ConcreteHighOrdinateProducerPair) →
  Core.compileOffAllowancePayment
    (concreteOffCore pair)
    (Factor.offPaymentToRepresentationAttachment (concreteOffPayment pair))
  ≡ concreteOffPayment pair
concreteOffPaymentRoundTrip pair =
  Factor.offPaymentRoundTrip (concreteOffPayment pair)

concreteGammaPaymentRoundTrip :
  (pair : ConcreteHighOrdinateProducerPair) →
  Core.compileGammaAllowancePayment
    (concreteGammaCore pair)
    (Factor.gammaPaymentToRepresentationAttachment (concreteGammaPayment pair))
  ≡ concreteGammaPayment pair
concreteGammaPaymentRoundTrip pair =
  Factor.gammaPaymentRoundTrip (concreteGammaPayment pair)

------------------------------------------------------------------------
-- FINAL HIGH-ORDINATE COMPLETION
--
-- The final same-object/order/cluster completion remains a distinct payment.
-- Once supplied, the concrete producer pair reaches contradiction directly.
------------------------------------------------------------------------

record CompletedConcreteHighOrdinateProducerPair : Set₂ where
  field
    pair : ConcreteHighOrdinateProducerPair
    completion :
      Core.FinalPoleQuotientAnalyticCompletion
        (concreteTwoAnalyticCores pair)
        (concreteAnalyticCoreAttachments pair)

open CompletedConcreteHighOrdinateProducerPair public

concretePairContradiction :
  CompletedConcreteHighOrdinateProducerPair → ⊥
concretePairContradiction completed =
  Core.compileAnalyticCoresToHighOrdinateContradiction
    (concreteTwoAnalyticCores (pair completed))
    (concreteAnalyticCoreAttachments (pair completed))
    (completion completed)

------------------------------------------------------------------------
-- SAME-SUBSTRATE PRIZE-FACING ADAPTER
--
-- A producer family indexed by the actual high nontrivial zero and an off-line
-- hypothesis now compiles directly to the existing HighOffLineAnalyticCoreProducer.
-- Consequently there is no additional theorem interface between concrete Off /
-- Gamma producer packets and the already-owned high/low RH compiler.
------------------------------------------------------------------------

record ConcreteHighOffLineProducer
    (analytic : Analytic.AnalyticSubstrate)
    (High : Universal.AnalyticNontrivialZero analytic → Set) : Set₂ where
  field
    completedForOffLine :
      (ρ : Universal.AnalyticNontrivialZero analytic) →
      High ρ →
      Neg (Universal.analyticCritical ρ) →
      CompletedConcreteHighOrdinateProducerPair

open ConcreteHighOffLineProducer public

compileConcreteHighOffLineProducer :
  {analytic : Analytic.AnalyticSubstrate} →
  {High : Universal.AnalyticNontrivialZero analytic → Set} →
  ConcreteHighOffLineProducer analytic High →
  Universal.HighOffLineAnalyticCoreProducer analytic High
compileConcreteHighOffLineProducer producer = record
  { Universal.coresForOffLineHigh = λ ρ high offLine →
      concreteTwoAnalyticCores
        (pair (completedForOffLine producer ρ high offLine))
  ; Universal.attachmentsForOffLineHigh = λ ρ high offLine →
      concreteAnalyticCoreAttachments
        (pair (completedForOffLine producer ρ high offLine))
  ; Universal.completionForOffLineHigh = λ ρ high offLine →
      completion (completedForOffLine producer ρ high offLine)
  }

concreteHighOffLineContradiction :
  {analytic : Analytic.AnalyticSubstrate} →
  {High : Universal.AnalyticNontrivialZero analytic → Set} →
  ConcreteHighOffLineProducer analytic High →
  (ρ : Universal.AnalyticNontrivialZero analytic) →
  High ρ →
  Neg (Universal.analyticCritical ρ) →
  ⊥
concreteHighOffLineContradiction producer =
  Universal.highOffLineAnalyticCoreContradiction
    (compileConcreteHighOffLineProducer producer)

compileConcretePrizeFacingRH :
  (analytic : Analytic.AnalyticSubstrate) →
  (Low High : Universal.AnalyticNontrivialZero analytic → Set) →
  ((ρ : Universal.AnalyticNontrivialZero analytic) → Low ρ ⊎ High ρ) →
  ((ρ : Universal.AnalyticNontrivialZero analytic) →
    Low ρ → Universal.analyticCritical ρ) →
  Universal.CriticalLineStable analytic →
  ConcreteHighOffLineProducer analytic High →
  Analytic.RiemannHypothesisFor analytic
compileConcretePrizeFacingRH
  analytic Low High cover lowCritical stable producer =
  Universal.analyticCoreHighLowCompletionImpliesRH
    analytic
    Low
    High
    cover
    lowCritical
    stable
    (compileConcreteHighOffLineProducer producer)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ConcreteProducerPairBoundary : Set where
  constructor concrete-producer-pair-boundary
  field
    certifiedOffPacketNeedsSeparateAnalyticCoreProof : Bool
    certifiedOffPacketNeedsSeparateAnalyticCoreProofIsFalse :
      certifiedOffPacketNeedsSeparateAnalyticCoreProof ≡ false

    freshGammaEnvelopeNeedsHistorical8889Identity : Bool
    freshGammaEnvelopeNeedsHistorical8889IdentityIsFalse :
      freshGammaEnvelopeNeedsHistorical8889Identity ≡ false

    concretePairCompilesTwoMinimalAnalyticCores : Bool
    concretePairCompilesTwoMinimalAnalyticCoresIsTrue :
      concretePairCompilesTwoMinimalAnalyticCores ≡ true

    finalCompletionStillIndependent : Bool
    finalCompletionStillIndependentIsTrue :
      finalCompletionStillIndependent ≡ true

    concreteHighZeroFamilyCompilesPrizeFacingProducer : Bool
    concreteHighZeroFamilyCompilesPrizeFacingProducerIsTrue :
      concreteHighZeroFamilyCompilesPrizeFacingProducer ≡ true

    concreteOffPacketInhabitedHere : Bool
    concreteOffPacketInhabitedHereIsFalse :
      concreteOffPacketInhabitedHere ≡ false

    concreteGammaEnvelopeInhabitedHere : Bool
    concreteGammaEnvelopeInhabitedHereIsFalse :
      concreteGammaEnvelopeInhabitedHere ≡ false

    finalRHDerivedHere : Bool
    finalRHDerivedHereIsFalse : finalRHDerivedHere ≡ false

canonicalConcreteProducerPairBoundary : ConcreteProducerPairBoundary
canonicalConcreteProducerPairBoundary =
  concrete-producer-pair-boundary
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
