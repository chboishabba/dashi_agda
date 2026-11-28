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
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.YangMillsDirectSourceOSCompactSimpleH5Exact as H5
import DASHI.Physics.YangMills.YangMillsDirectSourceOSReconstructedSpectrumH3Exact as H3
import DASHI.Physics.YangMills.YangMillsDirectSourceOSRationalContinuumH2Exact as H2Continuum
import DASHI.Physics.YangMills.YangMillsContinuumOPEStressWardGaussianKernelExact as Local
import DASHI.Physics.YangMills.YangMillsFreeGaussianMaxwellNoGapExact as Free
import DASHI.Physics.YangMills.YangMillsMaxwellLinearDispersionNoGapExact as Disp
import DASHI.Physics.YangMills.YangMillsGaussianWardTwoDerivativeMaxwellClassificationExact as Ward
import DASHI.Physics.YangMills.YangMillsGaussianWardGapNontrivialityExact as Nontrivial
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS

------------------------------------------------------------------------
-- The following compiler bundle was historically housed in Round77.  It is
-- reproduced here because H6 is its canonical same-system recipient.  The
-- bundle is a constructive consequence of the local Ward package and the
-- same-H positive gap; it is not a new physical theorem or a promotion.
-- Historical source: BalabanClayHighestAlphaRound77FiveAnalyticCutsetExact,
-- sameFamilyLocalAndGapData and round77InteractingWitnessFromLocalAndGap.
------------------------------------------------------------------------

record StandardGaussianMaxwellSameHGapBridge
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian Observable Point Scalar : Set}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (localPackage :
      Local.SameFamilyOPEStressWardGaussianKernel
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian Observable Point Scalar system)
    : Set₂ where
  field
    reconstruction : OS.OSReconstructionAuthority Observable Point Scalar system
    gapOrder : Free.GapOrder

    gaussianMaxwellPhysicalSector :
      (gaussian : Local.Gaussian localPackage system) →
      Ward.GenericMaxwellQuadraticKernelClassification
        (Local.coefficientAlgebra localPackage)
        (Local.gaussianLocalTwoDerivativeWardKernel localPackage gaussian) →
      Disp.GaplessGaugeInvariantPhysicalSector gapOrder

    PhysicalPositiveGap : OS.Hamiltonian reconstruction → Set
    physicalPositiveGap :
      PhysicalPositiveGap (OS.hamiltonian reconstruction)

    gapRestrictsToSamePhysicalSector :
      (gaussian : Local.Gaussian localPackage system) →
      (classification : Ward.GenericMaxwellQuadraticKernelClassification
        (Local.coefficientAlgebra localPackage)
        (Local.gaussianLocalTwoDerivativeWardKernel localPackage gaussian)) →
      PhysicalPositiveGap (OS.hamiltonian reconstruction) →
      Free.PositiveSpectralGap
        (Disp.gaugeInvariantPhysicalSectorGivesGaplessApproximation
          (gaussianMaxwellPhysicalSector gaussian classification))

    spectralGapContradictionIsAbsurd :
      (gaussian : Local.Gaussian localPackage system) →
      (classification : Ward.GenericMaxwellQuadraticKernelClassification
        (Local.coefficientAlgebra localPackage)
        (Local.gaussianLocalTwoDerivativeWardKernel localPackage gaussian)) →
      let sector = gaussianMaxwellPhysicalSector gaussian classification
          gapData = gapRestrictsToSamePhysicalSector
            gaussian classification physicalPositiveGap
      in
      Free.SpectralContradiction gapData → ⊥

open StandardGaussianMaxwellSameHGapBridge public

sameFamilyLocalAndGapData :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (localPackage :
      Local.SameFamilyOPEStressWardGaussianKernel
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian Observable Point Scalar system) →
    (bridge : StandardGaussianMaxwellSameHGapBridge localPackage) →
  Nontrivial.SameSystemGaussianWardGapData system
sameFamilyLocalAndGapData localPackage bridge = record
  { reconstruction = reconstruction bridge
  ; Gaussian = Local.Gaussian localPackage
  ; coefficientAlgebra =
      Local.coefficientAlgebra localPackage
  ; localWardKernelUnderGaussian =
      Local.gaussianLocalTwoDerivativeWardKernel localPackage
  ; gapOrder = gapOrder bridge
  ; gaussianMaxwellPhysicalSector =
      gaussianMaxwellPhysicalSector bridge
  ; PhysicalPositiveGap =
      PhysicalPositiveGap bridge
  ; physicalPositiveGap =
      physicalPositiveGap bridge
  ; gapRestrictsToSamePhysicalSector =
      gapRestrictsToSamePhysicalSector bridge
  ; spectralGapContradictionIsAbsurd =
      spectralGapContradictionIsAbsurd bridge
  }

round77InteractingWitnessFromLocalAndGap :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian Observable Point Scalar}
    {system : OS.ContinuumSchwingerSystem Observable Point Scalar}
    (localPackage :
      Local.SameFamilyOPEStressWardGaussianKernel
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian Observable Point Scalar system) →
    (bridge : StandardGaussianMaxwellSameHGapBridge localPackage) →
  OS.InteractingContinuumWitness Observable Point Scalar system
round77InteractingWitnessFromLocalAndGap localPackage bridge =
  Nontrivial.nonGaussianityGivesInteractingContinuumWitness
    (sameFamilyLocalAndGapData localPackage bridge)

round77NontrivialityDependencyCompilerLevel : ProofLevel
round77NontrivialityDependencyCompilerLevel = machineChecked

standardGaussianMaxwellSameHGapBridgeLevel : ProofLevel
standardGaussianMaxwellSameHGapBridgeLevel = standardImported

record LiteralDirectSourceSameSystemNontriviality
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (source : H5.LiteralCompactSimpleDirectSourceContinuation Y)
    : Set₂ where
  field
    ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian : Set

    localPackageFromLiteralC :
      Five.CutoffUniformPhysicalMassGap Y →
      Five.ContinuumLocalFieldOPEStressWard Y →
      ∀ G →
      let sameOS = H5.h3ForEveryLiteralGroup source G in
      Local.SameFamilyOPEStressWardGaussianKernel
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian
        (Top.Observable C)
        (Top.Position C)
        ℚ
        (H2Continuum.generatedSystem (H5.continuum source) G)

    sameHBridgeFromLiteralBC :
      (gap : Five.CutoffUniformPhysicalMassGap Y) →
      (local : Five.ContinuumLocalFieldOPEStressWard Y) →
      ∀ G →
      StandardGaussianMaxwellSameHGapBridge
        (localPackageFromLiteralC gap local G)

    interactingWitnessIsLiteralClayNontriviality :
      ∀ gap local G →
      let sameOS = H5.h3ForEveryLiteralGroup source G in
      OS.InteractingContinuumWitness
        (Top.Observable C)
        (Top.Position C)
        ℚ
        (H2Continuum.generatedSystem (H5.continuum source) G) →
      Top.IsNontrivialQuantumYangMills S G
        (Top.continuumMeasure Y G)
        (Top.schwinger Y G)

    interactingWitnessIsPreservedInLiteralLimit :
      ∀ gap local G →
      let sameOS = H5.h3ForEveryLiteralGroup source G in
      OS.InteractingContinuumWitness
        (Top.Observable C)
        (Top.Position C)
        ℚ
        (H2Continuum.generatedSystem (H5.continuum source) G) →
      Top.NontrivialityPreservedInLimit S G
        (Top.continuumMeasure Y G)

open LiteralDirectSourceSameSystemNontriviality public

round77Witness :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    {source : H5.LiteralCompactSimpleDirectSourceContinuation Y}
    (nontrivial :
      LiteralDirectSourceSameSystemNontriviality Y source)
    (gap : Five.CutoffUniformPhysicalMassGap Y)
    (local : Five.ContinuumLocalFieldOPEStressWard Y)
    G →
  let sameOS = H5.h3ForEveryLiteralGroup source G in
  OS.InteractingContinuumWitness
    (Top.Observable C)
    (Top.Position C)
    ℚ
    (H2Continuum.generatedSystem (H5.continuum source) G)
round77Witness nontrivial gap local G =
  round77InteractingWitnessFromLocalAndGap
    (localPackageFromLiteralC nontrivial gap local G)
    (sameHBridgeFromLiteralBC nontrivial gap local G)

asInteractingContinuumNontriviality :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S}
    {source : H5.LiteralCompactSimpleDirectSourceContinuation Y} →
  LiteralDirectSourceSameSystemNontriviality Y source →
  Five.CutoffUniformPhysicalMassGap Y →
  Five.ContinuumLocalFieldOPEStressWard Y →
  Five.InteractingContinuumNontriviality Y
asInteractingContinuumNontriviality nontrivial gap local = record
  { nontrivialQuantumYangMills =
      λ G →
        interactingWitnessIsLiteralClayNontriviality
          nontrivial gap local G
          (round77Witness nontrivial gap local G)
  ; nontrivialityPreservedInLimit =
      λ G →
        interactingWitnessIsPreservedInLiteralLimit
          nontrivial gap local G
          (round77Witness nontrivial gap local G)
  }

directH6GaussianWardGapCompilerLevel : ProofLevel
directH6GaussianWardGapCompilerLevel =
  round77NontrivialityDependencyCompilerLevel

-- H6 physical payment: a same-system semantic bridge saying the already
-- constructed literal C theorem supplies the Gaussian Ward kernel on the exact
-- H3 OS system and the already constructed B theorem supplies its SAME-H gap,
-- plus interpretation of the resulting interacting witness in literal Y.
directH6SameSystemPhysicalInstantiationLevel : ProofLevel
directH6SameSystemPhysicalInstantiationLevel = conditional
