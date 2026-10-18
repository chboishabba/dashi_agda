{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsWilsonMassGapCriticalPathRound553Exact where

------------------------------------------------------------------------
-- GOAL-1 B / ROUND553:
-- SOURCE-CORRECT WILSON MASS-GAP CRITICAL PATH
--
-- The preferred B theorem is now one direct proof object:
--
--   Wilson WEXT finite source
--      -> same-family continuum Wilson correlation
--      -> concrete half-rate clustering
--      -> SAME reconstructed-H transfer coordinate
--      -> standard spectral theorem
--      -> positive physical mass-gap certificate.
--
-- Historical printed-J, finite-Hamiltonian/Mosco, selected-J normalization and
-- independent mass-rate coordinates do not occur in this record.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanWilsonTwoInsertionConnectedShellRound491Exact as WEXT
import DASHI.Physics.YangMills.YangMillsWilsonContinuumClusteringRound551Exact as Continuum
import DASHI.Physics.YangMills.YangMillsWilsonSameHMassGapRound552Exact as Gap
import DASHI.Physics.YangMills.BalabanPairwiseMassRateFromTransferCoordinateRound311Exact as SameH
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS

record WilsonMassGapCriticalPath
    (Scale Volume Root State Observable Hamiltonian Energy : Set)
    : Set₂ where
  field
    finiteWilson :
      WEXT.WilsonTwoInsertionConnectedShell
        Scale Volume Root State Observable

    continuumWilson :
      Continuum.WilsonContinuumClusteringInputs finiteWilson

    sameHTransfer :
      SameH.SameHamiltonianTransferCoordinate Hamiltonian Energy

    spectralAuthority :
      Gap.WilsonHalfRateClusteringSpectrumAuthority
        continuumWilson sameHTransfer

open WilsonMassGapCriticalPath public

physicalMassGapCertificate :
  ∀ {Scale Volume Root State Observable Hamiltonian Energy} →
  WilsonMassGapCriticalPath
    Scale Volume Root State Observable Hamiltonian Energy →
  OS.PhysicalMassGapCertificate Hamiltonian Energy
physicalMassGapCertificate path =
  Gap.compileWilsonHalfRateToMassGap
    (sameHTransfer path)
    (spectralAuthority path)

round553MassGapCompilerLevel : ProofLevel
round553MassGapCompilerLevel =
  Gap.round552WilsonClusteringToGapCompilerLevel

round553WEXTLevel : ProofLevel
round553WEXTLevel =
  WEXT.round491WilsonTwoInsertionConnectedShellLevel

round553SameFamilyContinuumConvergenceLevel : ProofLevel
round553SameFamilyContinuumConvergenceLevel =
  Continuum.literalRound551SameFamilyWilsonCorrelationConvergenceLevel

round553WilsonTimeDistanceMeaningLevel : ProofLevel
round553WilsonTimeDistanceMeaningLevel =
  Continuum.literalRound551WilsonTimeDistanceMeaningLevel

round553SameHamiltonianTransferLevel : ProofLevel
round553SameHamiltonianTransferLevel =
  Gap.literalRound552SameHamiltonianTransferCoordinateLevel

round553StandardSpectralTransferLevel : ProofLevel
round553StandardSpectralTransferLevel =
  Gap.round552StandardHalfRateSpectralTransferLevel

printedJRouteRequired : Bool
printedJRouteRequired = false

finiteHamiltonianMoscoRouteRequired : Bool
finiteHamiltonianMoscoRouteRequired = false

independentMassRateCoordinateRequired : Bool
independentMassRateCoordinateRequired = false
