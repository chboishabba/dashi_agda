{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsDirectSourceOSSameSystemH6Exact where

------------------------------------------------------------------------
-- H6 SOURCE-FIRST: NONTRIVIALITY ON THE EXACT H3 OS SYSTEM.
--
-- Do not choose a second continuum Schwinger system for the Gaussian reductio.
-- For every literal compact-simple group, instantiate the existing Round77
-- local Ward / Gaussian / Maxwell contradiction on H3.sourceOSSystem from the
-- SAME H1/H2/H3/H5 package.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.YangMillsDirectSourceOSCompactSimpleH5Exact as H5
import DASHI.Physics.YangMills.YangMillsDirectSourceOSReconstructedSpectrumH3Exact as H3
import DASHI.Physics.YangMills.YangMillsContinuumOPEStressWardGaussianKernelExact as Local
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound77FiveAnalyticCutsetExact as R77
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS

record LiteralDirectSourceSameSystemNontriviality
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (source : H5.LiteralCompactSimpleDirectSourceContinuation Y)
    : Set₂ where
  field
    ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian : Set

    localPackage :
      ∀ G →
      let sameOS = H5.h3ForEveryLiteralGroup source G in
      Local.SameFamilyOPEStressWardGaussianKernel
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian
        (Top.Observable C)
        (H3.Point sameOS)
        ℚ
        (H3.sourceOSSystem sameOS)

    sameHBridge :
      ∀ G →
      R77.StandardGaussianMaxwellSameHGapBridge
        (localPackage G)

    interactingWitnessIsLiteralClayNontriviality :
      ∀ G →
      let sameOS = H5.h3ForEveryLiteralGroup source G in
      OS.InteractingContinuumWitness
        (Top.Observable C)
        (H3.Point sameOS)
        ℚ
        (H3.sourceOSSystem sameOS) →
      Top.IsNontrivialQuantumYangMills S G
        (Top.continuumMeasure Y G)
        (Top.schwinger Y G)

    interactingWitnessIsPreservedInLiteralLimit :
      ∀ G →
      let sameOS = H5.h3ForEveryLiteralGroup source G in
      OS.InteractingContinuumWitness
        (Top.Observable C)
        (H3.Point sameOS)
        ℚ
        (H3.sourceOSSystem sameOS) →
      Top.NontrivialityPreservedInLimit S G
        (Top.continuumMeasure Y G)

open LiteralDirectSourceSameSystemNontriviality public

round77Witness :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    {source : H5.LiteralCompactSimpleDirectSourceContinuation Y}
    (nontrivial :
      LiteralDirectSourceSameSystemNontriviality Y source)
    G →
  let sameOS = H5.h3ForEveryLiteralGroup source G in
  OS.InteractingContinuumWitness
    (Top.Observable C)
    (H3.Point sameOS)
    ℚ
    (H3.sourceOSSystem sameOS)
round77Witness nontrivial G =
  R77.round77InteractingWitnessFromLocalAndGap
    (localPackage nontrivial G)
    (sameHBridge nontrivial G)

asInteractingContinuumNontriviality :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    {source : H5.LiteralCompactSimpleDirectSourceContinuation Y} →
  LiteralDirectSourceSameSystemNontriviality Y source →
  Five.InteractingContinuumNontriviality Y
asInteractingContinuumNontriviality nontrivial = record
  { Five.InteractingContinuumNontriviality.nontrivialQuantumYangMills =
      λ G →
        interactingWitnessIsLiteralClayNontriviality
          nontrivial G (round77Witness nontrivial G)
  ; Five.InteractingContinuumNontriviality.nontrivialityPreservedInLimit =
      λ G →
        interactingWitnessIsPreservedInLiteralLimit
          nontrivial G (round77Witness nontrivial G)
  }

directH6GaussianWardGapCompilerLevel : ProofLevel
directH6GaussianWardGapCompilerLevel =
  R77.round77NontrivialityDependencyCompilerLevel

-- H6 physical payment: the minimal local Ward kernel and standard Gaussian
-- same-H bridge on the exact H3 OS system, plus interpretation of the resulting
-- interacting witness in the literal Y endpoint predicates.
directH6SameSystemPhysicalInstantiationLevel : ProofLevel
directH6SameSystemPhysicalInstantiationLevel = conditional
