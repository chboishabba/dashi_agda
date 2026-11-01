module DASHI.Analysis.RiemannG2UniformTargetZeroCertifiedCaseGeneratorExact where

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
import DASHI.Analysis.RiemannG2UniformCertifiedHighOffLineProducerExact as Uniform
import DASHI.Analysis.RiemannG2FinalPoleQuotientAnalyticCoreExact as Core

------------------------------------------------------------------------
-- UNIFORM TARGET-ZERO OFF GENERATOR
--
-- This is the concrete dependent family hidden inside one abstract
-- CertifiedOffCoreWitness.  Every choice is made from the arbitrary target rho
-- under the high + off-line hypotheses.  In particular, a single fixed finite
-- packet cannot inhabit this interface.
------------------------------------------------------------------------

record UniformTargetZeroOffGenerator
    (analytic : Analytic.AnalyticSubstrate)
    (High : Universal.AnalyticNontrivialZero analytic -> Set) : Set₂ where
  field
    spaceFor :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      High rho ->
      Neg (Universal.analyticCritical rho) ->
      Weil.WeilTestSpace

    formulaFor :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      (high : High rho) ->
      (offLine : Neg (Universal.analyticCritical rho)) ->
      Explicit.RiemannExplicitFormula (spaceFor rho high offLine)

    windowFor :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      (high : High rho) ->
      (offLine : Neg (Universal.analyticCritical rho)) ->
      Window.PoleNearTargetWindow
        (spaceFor rho high offLine)
        (formulaFor rho high offLine)

    surfaceFor :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      High rho ->
      Neg (Universal.analyticCritical rho) ->
      NearFar.OrderedAdditiveNearFarSurface

    transportFor :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      (high : High rho) ->
      (offLine : Neg (Universal.analyticCritical rho)) ->
      Transport.ExplicitCutoffNearFarAgdaTransport
        (surfaceFor rho high offLine)

    certifiedOffPacketFor :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      (high : High rho) ->
      (offLine : Neg (Universal.analyticCritical rho)) ->
      CertifiedOff.CertifiedFiniteNearUpperOffPacket
        (spaceFor rho high offLine)
        (formulaFor rho high offLine)
        (windowFor rho high offLine)
        (surfaceFor rho high offLine)
        (transportFor rho high offLine)

    offGeneratorReference : String

open UniformTargetZeroOffGenerator public

compileTargetZeroOffWitness :
  {analytic : Analytic.AnalyticSubstrate} ->
  {High : Universal.AnalyticNontrivialZero analytic -> Set} ->
  UniformTargetZeroOffGenerator analytic High ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  (high : High rho) ->
  (offLine : Neg (Universal.analyticCritical rho)) ->
  Uniform.CertifiedOffCoreWitness
compileTargetZeroOffWitness generator rho high offLine = record
  { Uniform.space = spaceFor generator rho high offLine
  ; Uniform.formula = formulaFor generator rho high offLine
  ; Uniform.window = windowFor generator rho high offLine
  ; Uniform.surface = surfaceFor generator rho high offLine
  ; Uniform.transport = transportFor generator rho high offLine
  ; Uniform.packet = certifiedOffPacketFor generator rho high offLine
  }

------------------------------------------------------------------------
-- UNIFORM TARGET-ZERO GAMMA GENERATOR
--
-- The envelope and allowance fit are regenerated for the same arbitrary target
-- case.  Historical producer identity is deliberately absent.
------------------------------------------------------------------------

record UniformTargetZeroGammaGenerator
    (analytic : Analytic.AnalyticSubstrate)
    (High : Universal.AnalyticNontrivialZero analytic -> Set) : Set₂ where
  field
    gammaEnvelopeFor :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      High rho ->
      Neg (Universal.analyticCritical rho) ->
      FreshGamma.FreshSameTaperGammaEnvelope

    gammaAllowanceFor :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      (high : High rho) ->
      (offLine : Neg (Universal.analyticCritical rho)) ->
      FreshGamma.FreshSameTaperGammaAllowanceInput
        (gammaEnvelopeFor rho high offLine)

    gammaGeneratorReference : String

open UniformTargetZeroGammaGenerator public

compileTargetZeroGammaWitness :
  {analytic : Analytic.AnalyticSubstrate} ->
  {High : Universal.AnalyticNontrivialZero analytic -> Set} ->
  UniformTargetZeroGammaGenerator analytic High ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  (high : High rho) ->
  (offLine : Neg (Universal.analyticCritical rho)) ->
  Uniform.FreshGammaCoreWitness
compileTargetZeroGammaWitness generator rho high offLine = record
  { Uniform.envelope = gammaEnvelopeFor generator rho high offLine
  ; Uniform.allowanceInput = gammaAllowanceFor generator rho high offLine
  }

------------------------------------------------------------------------
-- SAME-CASE FINAL ASSEMBLY
------------------------------------------------------------------------

record UniformTargetZeroCertifiedCaseGenerator
    (analytic : Analytic.AnalyticSubstrate)
    (High : Universal.AnalyticNontrivialZero analytic -> Set) : Set₂ where
  field
    offGenerator : UniformTargetZeroOffGenerator analytic High
    gammaGenerator : UniformTargetZeroGammaGenerator analytic High

    completionFor :
      (rho : Universal.AnalyticNontrivialZero analytic) ->
      (high : High rho) ->
      (offLine : Neg (Universal.analyticCritical rho)) ->
      Core.FinalPoleQuotientAnalyticCompletion
        (Uniform.compiledTwoCores
          (compileTargetZeroOffWitness offGenerator rho high offLine)
          (compileTargetZeroGammaWitness gammaGenerator rho high offLine))
        (Uniform.compiledTwoAttachments
          (compileTargetZeroOffWitness offGenerator rho high offLine)
          (compileTargetZeroGammaWitness gammaGenerator rho high offLine))

    generatorReference : String

open UniformTargetZeroCertifiedCaseGenerator public

compileTargetZeroCertifiedCase :
  {analytic : Analytic.AnalyticSubstrate} ->
  {High : Universal.AnalyticNontrivialZero analytic -> Set} ->
  (generator : UniformTargetZeroCertifiedCaseGenerator analytic High) ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  (high : High rho) ->
  (offLine : Neg (Universal.analyticCritical rho)) ->
  Uniform.CertifiedHighOffLineCase
compileTargetZeroCertifiedCase generator rho high offLine = record
  { Uniform.offWitness =
      compileTargetZeroOffWitness
        (offGenerator generator) rho high offLine
  ; Uniform.gammaWitness =
      compileTargetZeroGammaWitness
        (gammaGenerator generator) rho high offLine
  ; Uniform.completion = completionFor generator rho high offLine
  ; Uniform.caseReference = generatorReference generator
  }

compileUniformTargetZeroCertifiedProducer :
  {analytic : Analytic.AnalyticSubstrate} ->
  {High : Universal.AnalyticNontrivialZero analytic -> Set} ->
  UniformTargetZeroCertifiedCaseGenerator analytic High ->
  Uniform.UniformCertifiedHighOffLineProducer analytic High
compileUniformTargetZeroCertifiedProducer generator = record
  { Uniform.certifiedCaseForOffLineHigh =
      compileTargetZeroCertifiedCase generator
  ; Uniform.producerReference = generatorReference generator
  }

uniformTargetZeroContradiction :
  {analytic : Analytic.AnalyticSubstrate} ->
  {High : Universal.AnalyticNontrivialZero analytic -> Set} ->
  UniformTargetZeroCertifiedCaseGenerator analytic High ->
  (rho : Universal.AnalyticNontrivialZero analytic) ->
  High rho ->
  Neg (Universal.analyticCritical rho) ->
  ⊥
uniformTargetZeroContradiction generator =
  Uniform.uniformCertifiedHighOffLineContradiction
    (compileUniformTargetZeroCertifiedProducer generator)

------------------------------------------------------------------------
-- BOUNDARY
------------------------------------------------------------------------

record UniformTargetZeroCertifiedCaseBoundary : Set where
  constructor uniform-target-zero-certified-case-boundary
  field
    oneFixedOffPacketSuffices : Bool
    oneFixedOffPacketSufficesIsFalse : oneFixedOffPacketSuffices ≡ false

    oneFixedGammaEnvelopeSuffices : Bool
    oneFixedGammaEnvelopeSufficesIsFalse : oneFixedGammaEnvelopeSuffices ≡ false

    offPacketMustDependOnArbitraryTargetCase : Bool
    offPacketMustDependOnArbitraryTargetCaseIsTrue :
      offPacketMustDependOnArbitraryTargetCase ≡ true

    gammaEnvelopeMustDependOnArbitraryTargetCase : Bool
    gammaEnvelopeMustDependOnArbitraryTargetCaseIsTrue :
      gammaEnvelopeMustDependOnArbitraryTargetCase ≡ true

    targetWindowRecoveryRouteRequiredByThisCompiler : Bool
    targetWindowRecoveryRouteRequiredByThisCompilerIsFalse :
      targetWindowRecoveryRouteRequiredByThisCompiler ≡ false

    directCertifiedFinitePacketAccepted : Bool
    directCertifiedFinitePacketAcceptedIsTrue :
      directCertifiedFinitePacketAccepted ≡ true

    generatorInhabitedHere : Bool
    generatorInhabitedHereIsFalse : generatorInhabitedHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalUniformTargetZeroCertifiedCaseBoundary :
  UniformTargetZeroCertifiedCaseBoundary
canonicalUniformTargetZeroCertifiedCaseBoundary =
  uniform-target-zero-certified-case-boundary
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    "The uniform Clay-facing high obligation is now exposed as two target-indexed producer families plus same-case completion. Off must generate the selected space/formula/window, transport and proof-carrying finite-near upper packet from each arbitrary high off-line rho. Gamma must generate a fresh exact-final-taper envelope and allowance fit for that same case. This compiler does not require the longer target-window reconstruction route: a directly produced literal window/packet is accepted. No such uniform generator is fabricated here, and RH remains open."
