{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsWilsonSameHMassGapRound552Exact where

------------------------------------------------------------------------
-- GOAL-1 B / ROUND552:
-- DIRECT CONTINUUM WILSON HALF-RATE -> SAME-H POSITIVE GAP
--
-- R551 gives the exact continuum Wilson inequality
--
--   |Cov(W_L,W_R;t)| <= 1/4 * (1/2)^t
--
-- on the same-family continuum correlation.  R302/R311 already provide the
-- reusable physical transfer-energy <-> decay-ratio coordinate.
--
-- The only non-compiler physical identity left here is that this coordinate is
-- attached to the actual reconstructed Hamiltonian consumed by the standard
-- OS/semigroup spectral theorem.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsWilsonContinuumClusteringRound551Exact as R551
import DASHI.Physics.YangMills.BalabanTransferEnergyDecayRatioCoordinateRound302Exact as R302
import DASHI.Physics.YangMills.BalabanPairwiseMassRateFromTransferCoordinateRound311Exact as R311
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap

record WilsonHalfRateClusteringSpectrumAuthority
    {Scale Volume Root State Observable Hamiltonian Energy : Set}
    {finite :
      DASHI.Physics.YangMills.BalabanWilsonTwoInsertionConnectedShellRound491Exact.WilsonTwoInsertionConnectedShell
        Scale Volume Root State Observable}
    (continuum : R551.WilsonContinuumClusteringInputs finite)
    (transfer : R311.SameHamiltonianTransferCoordinate Hamiltonian Energy)
    : Set₁ where
  field
    SpectrumSeparatedBy : Hamiltonian → Energy → Set

    halfRateWilsonClusteringTransfer :
      (∀ left right time →
        R551.continuumConnectedCovarianceMagnitude continuum left right time
        ℚ.≤
        DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact.quarter
        ℚ.*
        DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact.rationalPower
          DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact.half
          time) →
      SpectrumSeparatedBy
        (R311.reconstructedHamiltonian transfer)
        (R302.candidateEnergy (R311.coordinate transfer))

open WilsonHalfRateClusteringSpectrumAuthority public

compileWilsonHalfRateToMassGap :
  ∀ {Scale Volume Root State Observable Hamiltonian Energy}
    {finite :
      DASHI.Physics.YangMills.BalabanWilsonTwoInsertionConnectedShellRound491Exact.WilsonTwoInsertionConnectedShell
        Scale Volume Root State Observable}
    {continuum : R551.WilsonContinuumClusteringInputs finite}
    (transfer : R311.SameHamiltonianTransferCoordinate Hamiltonian Energy) →
  WilsonHalfRateClusteringSpectrumAuthority continuum transfer →
  OSGap.PhysicalMassGapCertificate Hamiltonian Energy
compileWilsonHalfRateToMassGap {continuum = continuum} transfer authority = record
  { OSGap.PhysicalMassGapCertificate.hamiltonian =
      R311.reconstructedHamiltonian transfer
  ; OSGap.PhysicalMassGapCertificate.gap =
      R302.candidateEnergy (R311.coordinate transfer)
  ; OSGap.PhysicalMassGapCertificate.Positive =
      R302.PositiveEnergy (R311.coordinate transfer)
  ; OSGap.PhysicalMassGapCertificate.gapPositive =
      R302.candidateEnergyPositive (R311.coordinate transfer)
  ; OSGap.PhysicalMassGapCertificate.SpectrumAboveVacuumGap =
      SpectrumSeparatedBy authority
        (R311.reconstructedHamiltonian transfer)
        (R302.candidateEnergy (R311.coordinate transfer))
  ; OSGap.PhysicalMassGapCertificate.spectrumAboveVacuumGap =
      halfRateWilsonClusteringTransfer authority
        (R551.continuumWilsonHalfRateBound continuum)
  }

round552WilsonClusteringToGapCompilerLevel : ProofLevel
round552WilsonClusteringToGapCompilerLevel = machineChecked

round552StandardHalfRateSpectralTransferLevel : ProofLevel
round552StandardHalfRateSpectralTransferLevel = standardImported

-- The same-H transfer coordinate remains the real physical attachment.
literalRound552SameHamiltonianTransferCoordinateLevel : ProofLevel
literalRound552SameHamiltonianTransferCoordinateLevel =
  R302.round302PhysicalTransferEnergyDecayCoordinateLevel
