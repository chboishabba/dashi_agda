{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPinnedLocalCRealTraceSignExact where

------------------------------------------------------------------------
-- PREFERRED ANOMALY SIGN PRODUCER FOR COSMOLOGY.
--
-- Keep the trace on the SAME pinned Local-C stress object.  The only extra
-- same-object sign weld is that the anomaly transport's selected finite F^2
-- numerator is the literal physical weighted F^2 numerator whose strict
-- positivity is already proved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _<ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityConcreteLocalCAnomalyTransportExact as Transport
import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as Trace
import DASHI.Physics.Foundations.CMP119AntigravityRealF2StrictPositivityFromFullSupportExact as F2Positive
import DASHI.Physics.Foundations.CMP119AntigravityRealCurvatureF2PointBridgeExact as F2
import DASHI.Physics.Foundations.CMP119AntigravityRealFullSupportHaarExact as FullSupport
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as GibbsPositive
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as Gibbs
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

record PinnedLocalCPhysicalF2Weld
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian Configuration Action : Set}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian}
    {embedding : Embed.OrderedRationalRealEmbedding}
    {convention : Trace.RealSU2TraceConvention embedding}
    (transport :
      Transport.ConcreteLocalCAntigravityAnomalyTransport
        localC embedding convention)
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    {laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure}
    {strict : Strict.RealStrictSignLaws}
    {gibbs :
      Gibbs.WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws}
    {exponential : GibbsPositive.StrictPositiveRealExponential}
    {fullSupport : FullSupport.FullSupportRealHaarAuthority measure}
    (f2Positivity :
      F2Positive.RealPhysicalF2StrictPositivityInput
        strict embedding gibbs exponential fullSupport)
    : Set₁ where
  field
    selectedLocalCF2IsPhysicalWeightedF2 :
      Transport.selectedFiniteF2Numerator transport
      ≡
      F2Positive.weightedF2Numerator
        {measure = measure}
        (F2.realFieldStrengthSquare
          (F2Positive.curvature f2Positivity))

open PinnedLocalCPhysicalF2Weld public

selectedLocalCF2Positive :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian Configuration Action
      localC embedding convention transport measure laws strict gibbs
      exponential fullSupport f2Positivity} →
  (weld :
    PinnedLocalCPhysicalF2Weld
      {ContinuumFamily = ContinuumFamily}
      {CurvaturePolynomial = CurvaturePolynomial}
      {LocalOperator = LocalOperator}
      {Position = Position}
      {OPECoefficient = OPECoefficient}
      {StressTensor = StressTensor}
      {Hamiltonian = Hamiltonian}
      {Configuration = Configuration} {Action = Action}
      {localC = localC} {embedding = embedding}
      {convention = convention} transport
      {measure = measure} {laws = laws} {strict = strict}
      {gibbs = gibbs} {exponential = exponential}
      {fullSupport = fullSupport} f2Positivity) →
  0ℝ <ℝ Transport.selectedFiniteF2Numerator transport
selectedLocalCF2Positive
    {strict = strict} {embedding = embedding}
    {fullSupport = fullSupport} {f2Positivity = f2Positivity} weld =
  subst
    (λ value → 0ℝ <ℝ value)
    (sym (selectedLocalCF2IsPhysicalWeightedF2 weld))
    (F2Positive.realPhysicalF2NumeratorStrictlyPositive
      strict embedding fullSupport f2Positivity)

selectedLocalCFiniteTraceNegative :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian Configuration Action
      localC embedding convention transport measure laws strict gibbs
      exponential fullSupport f2Positivity} →
  (weld :
    PinnedLocalCPhysicalF2Weld
      {ContinuumFamily = ContinuumFamily}
      {CurvaturePolynomial = CurvaturePolynomial}
      {LocalOperator = LocalOperator}
      {Position = Position}
      {OPECoefficient = OPECoefficient}
      {StressTensor = StressTensor}
      {Hamiltonian = Hamiltonian}
      {Configuration = Configuration} {Action = Action}
      {localC = localC} {embedding = embedding}
      {convention = convention} transport
      {measure = measure} {laws = laws} {strict = strict}
      {gibbs = gibbs} {exponential = exponential}
      {fullSupport = fullSupport} f2Positivity) →
  Transport.selectedFiniteQuantumTraceNumerator transport <ℝ 0ℝ
selectedLocalCFiniteTraceNegative
    {strict = strict} {embedding = embedding}
    {convention = convention} weld =
  subst
    (λ value → value <ℝ 0ℝ)
    (sym (Transport.selectedFiniteTraceIsSU2BetaF2 _))
    (Strict.negativeTimesPositive strict
      (Trace.realSU2TraceCoefficientNegative strict embedding convention)
      (selectedLocalCF2Positive weld))

pinnedLocalCStressTraceNegative :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian Configuration Action
      localC embedding convention transport measure laws strict gibbs
      exponential fullSupport f2Positivity} →
  (weld :
    PinnedLocalCPhysicalF2Weld
      {ContinuumFamily = ContinuumFamily}
      {CurvaturePolynomial = CurvaturePolynomial}
      {LocalOperator = LocalOperator}
      {Position = Position}
      {OPECoefficient = OPECoefficient}
      {StressTensor = StressTensor}
      {Hamiltonian = Hamiltonian}
      {Configuration = Configuration} {Action = Action}
      {localC = localC} {embedding = embedding}
      {convention = convention} transport
      {measure = measure} {laws = laws} {strict = strict}
      {gibbs = gibbs} {exponential = exponential}
      {fullSupport = fullSupport} f2Positivity) →
  Transport.stressTraceNumerator transport (Local.stressTensor localC) <ℝ 0ℝ
pinnedLocalCStressTraceNegative {transport = transport} weld =
  subst
    (λ value → value <ℝ 0ℝ)
    (Transport.finiteTraceIsLocalCStressTrace transport)
    (selectedLocalCFiniteTraceNegative weld)

anomalySignNowPinnedToLocalCStressObject : Bool
anomalySignNowPinnedToLocalCStressObject = true

remainingAnomalySignLeafIsPhysicalF2SameObjectWeld : Bool
remainingAnomalySignLeafIsPhysicalF2SameObjectWeld = true
