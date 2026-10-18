{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3MarkedCurvatureLocalCRechartExact where

------------------------------------------------------------------------
-- R3 MAX-CUT: RECHART LOCAL-C ON THE EXISTING R129 COMPOSITE CARRIER.
--
-- `MarkedCurvatureCompositeFamily` already constructs
--
--   CurvaturePolynomial -> Composite
--
-- by the completed marked-source/nuclear-field compiler.  When Local-C's
-- LocalOperator carrier is that SAME `Composite`, retaining an independently
-- chosen `localOperator : CurvaturePolynomial -> Composite` creates an avoidable
-- same-object equality.
--
-- Rebuild only the Local-C presentation on the same carrier:
--   * use the marked-curvature operator map and its gauge/local predicates;
--   * retain the existing OPE functions, short-distance matching, stress tensor,
--     conservation and Hamiltonian generator data verbatim.
--
-- Then selected Local-C F^2 = marked-curvature F^2 is definitional (`refl`).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119MarkedCurvatureCompositeExact as Curvature
import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact as Nuclear

rechartLocalCOnMarkedCurvature :
  ∀ {ContinuumFamily CurvaturePolynomial Position OPECoefficient
      StressTensor Hamiltonian CompletedState Composite}
    {continuityScale : Nuclear.ContinuityScale} →
  Local.ContinuumLocalOperatorOPEStressTensor
    ContinuumFamily CurvaturePolynomial Composite Position
    OPECoefficient StressTensor Hamiltonian →
  Curvature.MarkedCurvatureCompositeFamily
    CurvaturePolynomial Position continuityScale CompletedState Composite →
  Local.ContinuumLocalOperatorOPEStressTensor
    ContinuumFamily CurvaturePolynomial Composite Position
    OPECoefficient StressTensor Hamiltonian
rechartLocalCOnMarkedCurvature base curvature = record
  { Local.ContinuumLocalOperatorOPEStressTensor.continuumFamily =
      Local.continuumFamily base
  ; Local.ContinuumLocalOperatorOPEStressTensor.localOperator =
      Curvature.localOperator curvature
  ; Local.ContinuumLocalOperatorOPEStressTensor.GaugeInvariant =
      Curvature.GaugeInvariant curvature
  ; Local.ContinuumLocalOperatorOPEStressTensor.LocalAt =
      Curvature.LocalAt curvature
  ; Local.ContinuumLocalOperatorOPEStressTensor.curvatureOperatorsGaugeInvariant =
      Curvature.localOperatorGaugeInvariant curvature
  ; Local.ContinuumLocalOperatorOPEStressTensor.curvatureOperatorsLocal =
      Curvature.localOperatorLocal curvature
  ; Local.ContinuumLocalOperatorOPEStressTensor.OPEAdmissible =
      Local.OPEAdmissible base
  ; Local.ContinuumLocalOperatorOPEStressTensor.coefficient =
      Local.coefficient base
  ; Local.ContinuumLocalOperatorOPEStressTensor.OPERemainder =
      Local.OPERemainder base
  ; Local.ContinuumLocalOperatorOPEStressTensor.opeRemainderMajorant =
      Local.opeRemainderMajorant base
  ; Local.ContinuumLocalOperatorOPEStressTensor.opeRemainderIsPhysicalRemainder =
      Local.opeRemainderIsPhysicalRemainder base
  ; Local.ContinuumLocalOperatorOPEStressTensor.ShortDistanceAFMatching =
      Local.ShortDistanceAFMatching base
  ; Local.ContinuumLocalOperatorOPEStressTensor.shortDistanceAFMatching =
      Local.shortDistanceAFMatching base
  ; Local.ContinuumLocalOperatorOPEStressTensor.stressTensor =
      Local.stressTensor base
  ; Local.ContinuumLocalOperatorOPEStressTensor.Symmetric =
      Local.Symmetric base
  ; Local.ContinuumLocalOperatorOPEStressTensor.ConservedInCorrelators =
      Local.ConservedInCorrelators base
  ; Local.ContinuumLocalOperatorOPEStressTensor.LocalStressTensor =
      Local.LocalStressTensor base
  ; Local.ContinuumLocalOperatorOPEStressTensor.stressTensorSymmetric =
      Local.stressTensorSymmetric base
  ; Local.ContinuumLocalOperatorOPEStressTensor.stressTensorConserved =
      Local.stressTensorConserved base
  ; Local.ContinuumLocalOperatorOPEStressTensor.stressTensorLocal =
      Local.stressTensorLocal base
  ; Local.ContinuumLocalOperatorOPEStressTensor.reconstructedHamiltonian =
      Local.reconstructedHamiltonian base
  ; Local.ContinuumLocalOperatorOPEStressTensor.SpatialIntegralT00Generates =
      Local.SpatialIntegralT00Generates base
  ; Local.ContinuumLocalOperatorOPEStressTensor.stressTensorGeneratesHamiltonian =
      Local.stressTensorGeneratesHamiltonian base
  }

markedCurvatureOperatorIsDefinitionallyLocalCOperator :
  ∀ {ContinuumFamily CurvaturePolynomial Position OPECoefficient
      StressTensor Hamiltonian CompletedState Composite continuityScale}
    (base :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial Composite Position
        OPECoefficient StressTensor Hamiltonian)
    (curvature :
      Curvature.MarkedCurvatureCompositeFamily
        CurvaturePolynomial Position continuityScale CompletedState Composite)
    polynomial →
  Local.localOperator
    (rechartLocalCOnMarkedCurvature base curvature) polynomial
  ≡ Curvature.localOperator curvature polynomial
markedCurvatureOperatorIsDefinitionallyLocalCOperator base curvature polynomial = refl

markedCurvatureGaugeInvariantIsDefinitionallyLocalC :
  ∀ {ContinuumFamily CurvaturePolynomial Position OPECoefficient
      StressTensor Hamiltonian CompletedState Composite continuityScale}
    (base :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial Composite Position
        OPECoefficient StressTensor Hamiltonian)
    (curvature :
      Curvature.MarkedCurvatureCompositeFamily
        CurvaturePolynomial Position continuityScale CompletedState Composite)
    polynomial →
  Local.GaugeInvariant (rechartLocalCOnMarkedCurvature base curvature)
    (Local.localOperator
      (rechartLocalCOnMarkedCurvature base curvature) polynomial)
markedCurvatureGaugeInvariantIsDefinitionallyLocalC base curvature polynomial =
  Curvature.localOperatorGaugeInvariant curvature polynomial

noPostHocLocalCF2OperatorEqualityRequired : Bool
noPostHocLocalCF2OperatorEqualityRequired = true

localCOPEStressHamiltonianDataPreservedByRechart : Bool
localCOPEStressHamiltonianDataPreservedByRechart = true
