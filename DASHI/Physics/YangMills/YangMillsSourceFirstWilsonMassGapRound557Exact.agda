{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSourceFirstWilsonMassGapRound557Exact where

------------------------------------------------------------------------
-- GOAL-1 B / ROUND557:
-- SOURCE-FIRST WILSON COVARIANCE -> CONTINUUM HALF-RATE -> SAME-H GAP
--
-- R556 chooses the WEXT finite covariance to be the exact CMP119/T5 selected
-- covariance.  Therefore R278 compiles finite -> continuum covariance
-- convergence, and R551 compiles the finite WEXT bound to the continuum
-- half-rate bound without a separate same-family convergence theorem.
--
-- The only independent B payments left on this route are:
--
--   * the physical Wilson source-first WEXT carrier (including test
--     admissibility, time/support meaning and order closure);
--   * the SAME reconstructed-H transfer coordinate / standard spectral
--     attachment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceRound556Exact as R556
import DASHI.Physics.YangMills.YangMillsWilsonSameHMassGapRound552Exact as R552
import DASHI.Physics.YangMills.BalabanPairwiseMassRateFromTransferCoordinateRound311Exact as SameH
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS

record SourceFirstWilsonMassGapPath
    {Measure Observable Scale Volume Root Hamiltonian Energy : Set}
    (dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    (extension :
      R278.ScalarCovarianceConvergenceExtension dataSet)
    : Set₂ where
  field
    wilson :
      R556.IndexedSourceFirstWilsonCovarianceData
        {Measure = Measure} {Observable = Observable}
        {Scale = Scale} {Volume = Volume} {Root = Root}
        dataSet extension

    sameHTransfer :
      SameH.SameHamiltonianTransferCoordinate Hamiltonian Energy

    spectralAuthority :
      R552.WilsonHalfRateClusteringSpectrumAuthority
        (R556.indexedAsContinuumClustering wilson)
        sameHTransfer

open SourceFirstWilsonMassGapPath public

physicalMassGapCertificate :
  ∀ {Measure Observable Scale Volume Root Hamiltonian Energy
      dataSet extension} →
  SourceFirstWilsonMassGapPath
    {Measure = Measure} {Observable = Observable}
    {Scale = Scale} {Volume = Volume} {Root = Root}
    {Hamiltonian = Hamiltonian} {Energy = Energy}
    dataSet extension →
  OS.PhysicalMassGapCertificate Hamiltonian Energy
physicalMassGapCertificate path =
  R552.compileWilsonHalfRateToMassGap
    (sameHTransfer path)
    (spectralAuthority path)

round557FiniteToContinuumCovarianceCompilerLevel : ProofLevel
round557FiniteToContinuumCovarianceCompilerLevel =
  R556.round556SameFamilyCovarianceConvergenceCompilerLevel

round557ContinuumHalfRateCompilerLevel : ProofLevel
round557ContinuumHalfRateCompilerLevel =
  R556.round556WEXTCarrierIsExactSelectedCovarianceLevel

round557MassGapCompilerLevel : ProofLevel
round557MassGapCompilerLevel =
  R552.round552WilsonClusteringToGapCompilerLevel

literalRound557SourceFirstWilsonCarrierLevel : ProofLevel
literalRound557SourceFirstWilsonCarrierLevel =
  R556.literalRound556SourceFirstWilsonCarrierLevel

literalRound557SameHamiltonianTransferLevel : ProofLevel
literalRound557SameHamiltonianTransferLevel =
  R552.literalRound552SameHamiltonianTransferCoordinateLevel

separateContinuumWilsonConvergencePaymentRequired : Bool
separateContinuumWilsonConvergencePaymentRequired = false

printedJRouteRequired : Bool
printedJRouteRequired = false

finiteHamiltonianMoscoRouteRequired : Bool
finiteHamiltonianMoscoRouteRequired = false
