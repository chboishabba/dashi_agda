module DASHI.Analysis.RiemannG2LiteralKernelConcreteCertificateBridgeCompilerValidation where

import DASHI.Core.ProofCarryingFiniteSumEnclosureExact as Cert
import DASHI.Analysis.RiemannG2ExplicitCutoffNearFarAgdaTransportCompilerExact as Transport
import DASHI.Analysis.RiemannG2LiteralComplementDirectTargetExact as Direct
import DASHI.Analysis.RiemannG2FinalNearLiteralKernelExact as Literal
import DASHI.Analysis.RiemannG2ConcreteCertificateFinalScalarBridgeExact as Concrete
import DASHI.Analysis.RiemannG2LiteralKernelConcreteCertificateBridgeCompilerExact as Compile

compiledBridgeCarriesExactFinalNearEquality :
  ∀ {S transport offInput carrier certificate}
    (kernel : Literal.FinalNearLiteralKernel
      {S = S} {transport = transport} offInput)
    (weld : Compile.LiteralKernelCertifiedFoldWeld
      {S = S} {transport = transport}
      {offInput = offInput}
      {carrier = carrier} {certificate = certificate}
      kernel) →
  Transport.nearResponseAt transport (Direct.chosenCutoff offInput)
  ≡
  Concrete.embed
    (Compile.compileConcreteCertificateFinalScalarBridge kernel weld)
    (Cert.foldScalars carrier
      (Cert.mapValues
        (Cert.ProofCarryingFiniteSumEnclosure.evaluateTerm certificate)
        (Cert.ProofCarryingFiniteSumEnclosure.terms certificate)))
compiledBridgeCarriesExactFinalNearEquality kernel weld =
  Concrete.finalNearIsEmbeddedCertifiedFold
    (Compile.compileConcreteCertificateFinalScalarBridge kernel weld)
