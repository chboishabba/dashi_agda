{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityConcreteLocalCAnomalyTransportExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityPinnedConcreteLocalCTraceAnomalyExact as ConcreteBridge
import DASHI.Physics.Foundations.CMP119AntigravityPinnedLocalCTraceAnomalyBridgeExact as Bridge
import DASHI.Physics.Foundations.CMP119AntigravityRealTraceAnomalySameObjectExact as Anomaly
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as Concrete
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

------------------------------------------------------------------------
-- HIGHEST-ALPHA LOCAL-C ANOMALY TRANSPORT
--
-- The pinned concrete Local-C package already supplies, on one reconstructed
-- CMP119 continuum family:
--
--   * a gauge-invariant local curvature-polynomial operator map;
--   * a local, symmetric, conserved stress tensor;
--   * the same reconstructed Hamiltonian / Ward-generator package.
--
-- Therefore antigravity does NOT need to reconstruct those broad objects.
-- Its remaining model-specific theorem is only to select the F^2 polynomial,
-- read out trace(T_ren) and N([F^2]_ren), attach the standard anomaly authority
-- to those exact Local-C objects, and identify the two selected finite CMP119
-- numerators with those same readouts.
------------------------------------------------------------------------

record ConcreteLocalCAntigravityAnomalyTransport
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set}
    (localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (convention : SU2Trace.RealSU2TraceConvention embedding) : Set₁ where
  field
    fieldStrengthSquarePolynomial : CurvaturePolynomial

    stressTraceNumerator : StressTensor → ℝ
    localOperatorNumerator : LocalOperator → ℝ

    anomalyAuthority :
      Anomaly.RenormalizedPureYMTraceAnomalyAuthority
        embedding convention

    authorityTraceIsLocalCStressTrace :
      Anomaly.renormalizedTraceNumerator anomalyAuthority
      ≡
      stressTraceNumerator (Local.stressTensor localC)

    authorityF2IsLocalCF2 :
      Anomaly.renormalizedF2Numerator anomalyAuthority
      ≡
      localOperatorNumerator
        (Local.localOperator localC fieldStrengthSquarePolynomial)

    selectedFiniteQuantumTraceNumerator : ℝ
    selectedFiniteF2Numerator : ℝ

    finiteTraceIsLocalCStressTrace :
      selectedFiniteQuantumTraceNumerator
      ≡
      stressTraceNumerator (Local.stressTensor localC)

    finiteF2IsLocalCF2 :
      selectedFiniteF2Numerator
      ≡
      localOperatorNumerator
        (Local.localOperator localC fieldStrengthSquarePolynomial)

open ConcreteLocalCAntigravityAnomalyTransport public

asPinnedLocalCReadout :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian embedding convention}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian} →
  ConcreteLocalCAntigravityAnomalyTransport localC embedding convention →
  Bridge.SameFamilyLocalCTraceAnomalyReadout
    localC embedding convention
asPinnedLocalCReadout transport = record
  { Bridge.SameFamilyLocalCTraceAnomalyReadout.fieldStrengthSquarePolynomial =
      fieldStrengthSquarePolynomial transport
  ; Bridge.SameFamilyLocalCTraceAnomalyReadout.stressTraceNumerator =
      stressTraceNumerator transport
  ; Bridge.SameFamilyLocalCTraceAnomalyReadout.localOperatorNumerator =
      localOperatorNumerator transport
  ; Bridge.SameFamilyLocalCTraceAnomalyReadout.anomalyAuthority =
      anomalyAuthority transport
  ; Bridge.SameFamilyLocalCTraceAnomalyReadout.authorityTraceIsSelectedLocalStress =
      authorityTraceIsLocalCStressTrace transport
  ; Bridge.SameFamilyLocalCTraceAnomalyReadout.authorityF2IsSelectedCurvatureOperator =
      authorityF2IsLocalCF2 transport
  }

asFiniteCMP119LocalCWeld :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian embedding convention}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian}
    (transport :
      ConcreteLocalCAntigravityAnomalyTransport
        localC embedding convention) →
  Bridge.FiniteCMP119ToLocalCTraceAnomalyWeld
    (asPinnedLocalCReadout transport)
asFiniteCMP119LocalCWeld transport = record
  { Bridge.FiniteCMP119ToLocalCTraceAnomalyWeld.selectedFiniteQuantumTraceNumerator =
      selectedFiniteQuantumTraceNumerator transport
  ; Bridge.FiniteCMP119ToLocalCTraceAnomalyWeld.selectedFiniteF2Numerator =
      selectedFiniteF2Numerator transport
  ; Bridge.FiniteCMP119ToLocalCTraceAnomalyWeld.finiteTraceIsLocalCStressTrace =
      finiteTraceIsLocalCStressTrace transport
  ; Bridge.FiniteCMP119ToLocalCTraceAnomalyWeld.finiteF2IsLocalCCurvatureF2 =
      finiteF2IsLocalCF2 transport
  }

selectedFiniteTraceIsSU2BetaF2 :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian embedding convention}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian}
    (transport :
      ConcreteLocalCAntigravityAnomalyTransport
        localC embedding convention) →
  selectedFiniteQuantumTraceNumerator transport
  ≡
  SU2Trace.realSU2TraceCoefficient embedding convention
  *ℝ
  selectedFiniteF2Numerator transport
selectedFiniteTraceIsSU2BetaF2 transport =
  Bridge.finiteCMP119TraceIsSU2BetaF2ViaPinnedLocalC
    (asFiniteCMP119LocalCWeld transport)

finiteTraceIsRenormalizedTrace :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian embedding convention}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian}
    (transport :
      ConcreteLocalCAntigravityAnomalyTransport
        localC embedding convention) →
  selectedFiniteQuantumTraceNumerator transport
  ≡
  Anomaly.renormalizedTraceNumerator (anomalyAuthority transport)
finiteTraceIsRenormalizedTrace transport =
  trans
    (finiteTraceIsLocalCStressTrace transport)
    (sym
      (authorityTraceIsLocalCStressTrace transport))

finiteF2IsRenormalizedF2 :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian embedding convention}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian}
    (transport :
      ConcreteLocalCAntigravityAnomalyTransport
        localC embedding convention) →
  selectedFiniteF2Numerator transport
  ≡
  Anomaly.renormalizedF2Numerator (anomalyAuthority transport)
finiteF2IsRenormalizedF2 transport =
  trans
    (finiteF2IsLocalCF2 transport)
    (sym
      (authorityF2IsLocalCF2 transport))
