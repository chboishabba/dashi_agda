{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityPinnedConcreteLocalCTraceAnomalyExact where

import DASHI.Physics.Foundations.CMP119AntigravityPinnedLocalCTraceAnomalyBridgeExact as Bridge
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as Concrete
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

------------------------------------------------------------------------
-- PIN THE TRACE-ANOMALY READOUT TO THE ACTUAL CMP119 LOCAL-C PACKAGE
------------------------------------------------------------------------

PinnedCMP119ConcreteLocalCTraceAnomalyReadout :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group}
    (inputs :
      Concrete.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : SU2Trace.RealSU2TraceConvention embedding) →
  Set₁
PinnedCMP119ConcreteLocalCTraceAnomalyReadout
    inputs embedding convention =
  Bridge.SameFamilyLocalCTraceAnomalyReadout
    (Concrete.compileConcretePinnedLocalPackage inputs)
    embedding convention

PinnedCMP119FiniteToConcreteLocalCTraceAnomalyWeld :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group
      embedding convention}
    {inputs :
      Concrete.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group}
    (readout :
      PinnedCMP119ConcreteLocalCTraceAnomalyReadout
        inputs embedding convention) →
  Set₁
PinnedCMP119FiniteToConcreteLocalCTraceAnomalyWeld readout =
  Bridge.FiniteCMP119ToLocalCTraceAnomalyWeld readout

pinnedCMP119FiniteTraceIsSU2BetaF2ViaConcreteLocalC :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division S osInputs reconstruction group
      embedding convention}
    {inputs :
      Concrete.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = S} osInputs reconstruction group}
    {readout :
      PinnedCMP119ConcreteLocalCTraceAnomalyReadout
        inputs embedding convention}
    (weld :
      PinnedCMP119FiniteToConcreteLocalCTraceAnomalyWeld readout) →
  Bridge.selectedFiniteQuantumTraceNumerator weld
  Agda.Builtin.Equality.≡
  SU2Trace.realSU2TraceCoefficient embedding convention
  DASHI.Foundations.RealAnalysisAxioms.*ℝ
  Bridge.selectedFiniteF2Numerator weld
pinnedCMP119FiniteTraceIsSU2BetaF2ViaConcreteLocalC =
  Bridge.finiteCMP119TraceIsSU2BetaF2ViaPinnedLocalC
