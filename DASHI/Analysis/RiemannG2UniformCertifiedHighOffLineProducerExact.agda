module DASHI.Analysis.RiemannG2UniformCertifiedHighOffLineProducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Set₂)

import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window
import DASHI.Analysis.RiemannAristotlePoleQuotientOffOrdinateNearFarBidiExact as NearFar
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2CertifiedFiniteNearToOffPaymentExact as CertifiedOff
import DASHI.Analysis.RiemannG2FreshSameTaperGammaEnvelopeCompilerExact as FreshGamma
import DASHI.Analysis.RiemannG2AllowancePaymentsToAnalyticCoresExact as Factor
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core

------------------------------------------------------------------------
-- ONE CERTIFIED OFF WITNESS -> CURRENT OFF CORE + ATTACHMENT
------------------------------------------------------------------------

record CertifiedOffCoreWitness : Set₂ where
  field
    space : Weil.WeilTestSpace
    formula : Explicit.RiemannExplicitFormula space
    window : Window.PoleNearTargetWindow space formula
    surface : NearFar.OrderedAdditiveNearFarSurface
    transport : Transport.ExplicitCutoffNearFarAgdaTransport surface
    packet :
      CertifiedOff.CertifiedFiniteNearUpperOffPacket
        space formula window surface transport

open CertifiedOffCoreWitness public

compiledOffCore : CertifiedOffCoreWitness -> Core.OffAnalyticCore
compiledOffCore witness =
  Factor.certifiedFiniteNearUpperToOffAnalyticCore
    (CertifiedOffCoreWitness.packet witness)

compiledOffAttachment :
  (witness : CertifiedOffCoreWitness) ->
  Core.OffRepresentationAttachment (compiledOffCore witness)
compiledOffAttachment witness =
  Factor.certifiedFiniteNearUpperToOffAttachment
    (CertifiedOffCoreWitness.packet witness)

------------------------------------------------------------------------
-- ONE FRESH SAME-TAPER GAMMA WITNESS -> CURRENT GAMMA CORE + ATTACHMENT
------------------------------------------------------------------------

record FreshGammaCoreWitness : Set₂ where
  field
    envelope : FreshGamma.FreshSameTaperGammaEnvelope
    allowanceInput : FreshGamma.FreshSameTaperGammaAllowanceInput envelope

open FreshGammaCoreWitness public

compiledGammaCore : FreshGammaCoreWitness -> Core.GammaAnalyticCore
compiledGammaCore witness =
  Factor.freshGammaEnvelopeToAnalyticCore
    (FreshGammaCoreWitness.envelope witness)
    (FreshGammaCoreWitness.allowanceInput witness)

compiledGammaAttachment :
  (witness : FreshGammaCoreWitness) ->
  Core.GammaRepresentationAttachment (compiledGammaCore witness)
compiledGammaAttachment witness =
  Factor.freshGammaEnvelopeToAttachment
    (FreshGammaCoreWitness.envelope witness)
    (FreshGammaCoreWitness.allowanceInput witness)

------------------------------------------------------------------------
-- ONE HIGH OFF-LINE CASE -> COMPLETE TWO-CORE CONTRADICTION PACKET
------------------------------------------------------------------------

compiledTwoCores :
  CertifiedOffCoreWitness ->
  FreshGammaCoreWitness ->
  Core.FinalPoleQuotientTwoAnalyticCores
compiledTwoCores off gamma =
  Core.final-pole-quotient-two-analytic-cores
    (compiledOffCore off)
    (compiledGammaCore gamma)
    "uniform certified high-off-line producer: compiled two analytic cores"

compiledTwoAttachments :
  (off : CertifiedOffCoreWitness) ->
  (gamma : FreshGammaCoreWitness) ->
  Core.FinalPoleQuotientAnalyticCoreAttachments
    (compiledTwoCores off gamma)
compiledTwoAttachments off gamma =
  Core.final-pole-quotient-analytic-core-attachments
    (compiledOffAttachment off)
    (compiledGammaAttachment gamma)
    "uniform certified high-off-line producer: compiled representation attachments"

record CertifiedHighOffLineCase : Set₂ where
  field
    offWitness : CertifiedOffCoreWitness
    gammaWitness : FreshGammaCoreWitness

    completion :
      Core.FinalPoleQuotientAnalyticCompletion
        (compiledTwoCores offWitness gammaWitness)
        (compiledTwoAttachments offWitness gammaWitness)

    caseReference : String

open CertifiedHighOffLineCase public

------------------------------------------------------------------------
-- CLAY-LEVEL QUANTIFIER: EVERY HIGH OFF-LINE ZERO GETS SUCH A CASE.
--
-- A finite certificate at one target is only an instance witness.  The
-- prize-facing high producer requires a certificate-producing family under the
-- high + off-line hypotheses for each nontrivial zero in the high region.
------------------------------------------------------------------------

record UniformCertifiedHighOffLineProducer
    (analytic : Analytic.AnalyticSubstrate)
    (High : Universal.AnalyticNontrivialZero analytic -> Set) : Set₂ where
  field
    certifiedCaseForOffLineHigh :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      High rho ->
      Neg (Universal.analyticCritical rho) ->
      CertifiedHighOffLineCase

    producerReference : String

open UniformCertifiedHighOffLineProducer public

compileUniformCertifiedHighOffLineProducer :
  {analytic : Analytic.AnalyticSubstrate} ->
  {High : Universal.AnalyticNontrivialZero analytic -> Set} ->
  UniformCertifiedHighOffLineProducer analytic High ->
  Universal.HighOffLineAnalyticCoreProducer analytic High
compileUniformCertifiedHighOffLineProducer producer = record
  { Universal.coresForOffLineHigh =
      λ rho high offLine ->
        let case0 = certifiedCaseForOffLineHigh producer rho high offLine
        in compiledTwoCores
          (CertifiedHighOffLineCase.offWitness case0)
          (CertifiedHighOffLineCase.gammaWitness case0)
  ; Universal.attachmentsForOffLineHigh =
      λ rho high offLine ->
        let case0 = certifiedCaseForOffLineHigh producer rho high offLine
        in compiledTwoAttachments
          (CertifiedHighOffLineCase.offWitness case0)
          (CertifiedHighOffLineCase.gammaWitness case0)
  ; Universal.completionForOffLineHigh =
      λ rho high offLine ->
        CertifiedHighOffLineCase.completion
          (certifiedCaseForOffLineHigh producer rho high offLine)
  }

uniformCertifiedHighOffLineContradiction :
  {analytic : Analytic.AnalyticSubstrate} ->
  {High : Universal.AnalyticNontrivialZero analytic -> Set} ->
  UniformCertifiedHighOffLineProducer analytic High ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  High rho ->
  Neg (Universal.analyticCritical rho) ->
  ⊥
uniformCertifiedHighOffLineContradiction producer =
  Universal.highOffLineAnalyticCoreContradiction
    (compileUniformCertifiedHighOffLineProducer producer)

record UniformCertifiedHighOffLineBoundary : Set where
  constructor uniform-certified-high-off-line-boundary
  field
    oneFixedFiniteCertificateIsClayLevelHighProducer : Bool
    oneFixedFiniteCertificateIsClayLevelHighProducerIsFalse :
      oneFixedFiniteCertificateIsClayLevelHighProducer ≡ false

    perHighOffLineCertificateFamilyRequired : Bool
    perHighOffLineCertificateFamilyRequiredIsTrue :
      perHighOffLineCertificateFamilyRequired ≡ true

    certifiedOffAndFreshGammaCasesCompilePrizeHighProducer : Bool
    certifiedOffAndFreshGammaCasesCompilePrizeHighProducerIsTrue :
      certifiedOffAndFreshGammaCasesCompilePrizeHighProducer ≡ true

    uniformProducerInhabitedHere : Bool
    uniformProducerInhabitedHereIsFalse :
      uniformProducerInhabitedHere ≡ false

    lowOrdinateCertificateManufacturedHere : Bool
    lowOrdinateCertificateManufacturedHereIsFalse :
      lowOrdinateCertificateManufacturedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalUniformCertifiedHighOffLineBoundary :
  UniformCertifiedHighOffLineBoundary
canonicalUniformCertifiedHighOffLineBoundary =
  uniform-certified-high-off-line-boundary
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "A one-off finite-window enclosure is not the Clay-level high theorem. The exact high theorem is a uniform producer: for every high nontrivial zero under an off-critical-line hypothesis, produce the certified finite-near Off witness, fresh same-taper Gamma witness, and final completion on that same case. This family compiles to HighOffLineAnalyticCoreProducer. The family is not inhabited here, low-ordinate certification is not manufactured, and RH is not derived."
