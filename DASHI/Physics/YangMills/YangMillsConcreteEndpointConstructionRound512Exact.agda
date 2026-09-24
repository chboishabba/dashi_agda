{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsConcreteEndpointConstructionRound512Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND512: SOURCE-FIRST TERMINAL ENDPOINT CONSTRUCTION
--
-- Given R511's proof-bearing source bundle, choose the literal endpoint objects
-- FROM those sources:
--
--   finite family      := literal CMP119 finite family
--   continuum measure  := represented countably-additive measure
--   Schwinger family   := Schwinger from that represented measure
--   Hilbert/H/vacuum   := SAME OS reconstruction
--   mass gap           := SAME physical spectral certificate
--
-- Then the corresponding endpoint semantics are no longer independent fields.
-- They compile from refl / source equalities.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476
import DASHI.Physics.YangMills.YangMillsConcreteEndpointSemanticsRound511Exact as R511
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.BalabanOSReconstructionMassGapProduction as OSR
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record ConcreteEndpointConstructionInputs
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
     Algebra Event Projection : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    (base :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum))
    (bundle :
      R511.ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    : Set₁ where
  field
    spacetime : X

    localObservable :
      G → Position → Configuration → ℝ

    curvatureOperator :
      G → CurvaturePolynomial → LocalOperator

    opeCoefficient :
      G →
      LocalOperator → LocalOperator → LocalOperator →
      Position → OPECoefficient

    opeRemainder :
      G →
      LocalOperator → LocalOperator →
      Position → Nat → ℚ

    stressTensor :
      G → StressTensor

open ConcreteEndpointConstructionInputs public

concreteLiteralConstruction :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division
      base bundle} →
  ConcreteEndpointConstructionInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    Algebra Event Projection
    {sequenceLimit = sequenceLimit}
    {limitLaws = limitLaws}
    {quotient = quotient}
    {division = division}
    base bundle →
  Top.LiteralYangMillsConstruction
    (Physical.physicalLiteralCarriers
      G X Nat Configuration ℝ (Configuration → ℝ) Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      Hilbert Hamiltonian Vacuum)
    (R511.concreteEndpointSemantics base bundle)
concreteLiteralConstruction {bundle = bundle} inputs = record
  { Top.LiteralYangMillsConstruction.spacetime =
      spacetime inputs
  ; Top.LiteralYangMillsConstruction.finiteMeasure =
      λ group cutoff →
        Limit.finiteMeasure (R511.family bundle group) cutoff
  ; Top.LiteralYangMillsConstruction.continuumMeasure =
      λ group →
        R476.asPhysicalContinuum (R511.representedFor bundle group)
  ; Top.LiteralYangMillsConstruction.schwinger =
      λ group →
        R476.representedSchwinger
          (R511.cylinderEncoding bundle)
          (R511.representedFor bundle group)
  ; Top.LiteralYangMillsConstruction.localObservable =
      localObservable inputs
  ; Top.LiteralYangMillsConstruction.curvatureOperator =
      curvatureOperator inputs
  ; Top.LiteralYangMillsConstruction.opeCoefficient =
      opeCoefficient inputs
  ; Top.LiteralYangMillsConstruction.opeRemainder =
      opeRemainder inputs
  ; Top.LiteralYangMillsConstruction.stressTensor =
      stressTensor inputs
  ; Top.LiteralYangMillsConstruction.hilbertSpace =
      λ group →
        OSR.reconstructedHilbertSpace (R511.reconstruction bundle group)
  ; Top.LiteralYangMillsConstruction.hamiltonian =
      λ group →
        OSR.reconstructedHamiltonian (R511.reconstruction bundle group)
  ; Top.LiteralYangMillsConstruction.vacuum =
      λ group →
        OSR.reconstructedVacuum (R511.reconstruction bundle group)
  ; Top.LiteralYangMillsConstruction.massGap =
      λ group →
        OSGap.gap (R511.gapCertificate bundle group)
  }

concreteContinuumLimit :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division
      base bundle}
    (inputs :
      ConcreteEndpointConstructionInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        base bundle)
    group →
  Top.IsContinuumLimitOf
    (R511.concreteEndpointSemantics base bundle)
    group
    (Top.finiteMeasure (concreteLiteralConstruction inputs) group)
    (Top.continuumMeasure (concreteLiteralConstruction inputs) group)
concreteContinuumLimit inputs group =
  ( (λ cutoff → refl)
  , (λ observable → refl)
  )

concreteSchwingerBelongs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division
      base bundle}
    (inputs :
      ConcreteEndpointConstructionInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        base bundle)
    group →
  Top.SchwingerBelongsToMeasure
    (R511.concreteEndpointSemantics base bundle)
    (Top.continuumMeasure (concreteLiteralConstruction inputs) group)
    (Top.schwinger (concreteLiteralConstruction inputs) group)
concreteSchwingerBelongs inputs group observable left right = refl

concreteAcceptedOS :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division
      base bundle}
    (inputs :
      ConcreteEndpointConstructionInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        base bundle)
    group →
  Top.SatisfiesAcceptedWightmanOrOSAxioms
    (R511.concreteEndpointSemantics base bundle)
    group
    (Top.schwinger (concreteLiteralConstruction inputs) group)
concreteAcceptedOS {bundle = bundle} inputs group observable left right =
  sym (R511.osSystemIsRepresentedSchwinger
    bundle group observable left right)

concreteReconstructedHilbert :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division
      base bundle}
    (inputs :
      ConcreteEndpointConstructionInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        base bundle)
    group →
  Top.IsReconstructedHilbertSpace
    (R511.concreteEndpointSemantics base bundle)
    group
    (Top.schwinger (concreteLiteralConstruction inputs) group)
    (Top.hilbertSpace (concreteLiteralConstruction inputs) group)
concreteReconstructedHilbert inputs group =
  concreteAcceptedOS inputs group , refl

concretePositiveSelfAdjointHamiltonian :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division
      base bundle}
    (inputs :
      ConcreteEndpointConstructionInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        base bundle)
    group →
  Top.IsPositiveSelfAdjointHamiltonian
    (R511.concreteEndpointSemantics base bundle)
    (Top.hilbertSpace (concreteLiteralConstruction inputs) group)
    (Top.hamiltonian (concreteLiteralConstruction inputs) group)
concretePositiveSelfAdjointHamiltonian inputs group =
  group , (refl , refl)

concreteVacuumSectorPositiveEnergy :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division
      base bundle}
    (inputs :
      ConcreteEndpointConstructionInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        base bundle)
    group →
  Top.IsVacuumSectorAndPositiveEnergyComplement
    (R511.concreteEndpointSemantics base bundle)
    (Top.hilbertSpace (concreteLiteralConstruction inputs) group)
    (Top.hamiltonian (concreteLiteralConstruction inputs) group)
    (Top.vacuum (concreteLiteralConstruction inputs) group)
concreteVacuumSectorPositiveEnergy {bundle = bundle} inputs group =
  group ,
    ( refl
    , refl
    , refl
    , R511.clusteringHamiltonianIsReconstructed bundle group
    )

concreteStrictPositiveMassGap :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division
      base bundle}
    (inputs :
      ConcreteEndpointConstructionInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        base bundle)
    group →
  Top.IsStrictlyPositiveFiniteMassGap
    (R511.concreteEndpointSemantics base bundle)
    (Top.hamiltonian (concreteLiteralConstruction inputs) group)
    (Top.massGap (concreteLiteralConstruction inputs) group)
concreteStrictPositiveMassGap {bundle = bundle} inputs group =
  group ,
    ( sym (R511.gapHamiltonianIsReconstructed bundle group)
    , refl
    )

concretePhysicalScaleLowerBound :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division
      base bundle}
    (inputs :
      ConcreteEndpointConstructionInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        base bundle)
    group →
  Top.PhysicalScaleLowerBoundUniform
    (R511.concreteEndpointSemantics base bundle)
    group
    (Top.massGap (concreteLiteralConstruction inputs) group)
concretePhysicalScaleLowerBound {bundle = bundle} inputs group =
  sym (refl)

concreteNoSpectralPollution :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division
      base bundle}
    (inputs :
      ConcreteEndpointConstructionInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        base bundle)
    group →
  Top.NoSpectralPollutionBelowGap
    (R511.concreteEndpointSemantics base bundle)
    group
    (Top.hamiltonian (concreteLiteralConstruction inputs) group)
    (Top.massGap (concreteLiteralConstruction inputs) group)
concreteNoSpectralPollution {bundle = bundle} inputs group =
  ( sym (R511.clusteringHamiltonianIsReconstructed bundle group)
  , refl
  )

concreteGapAndClusteringDerived :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division
      base bundle}
    (inputs :
      ConcreteEndpointConstructionInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        base bundle)
    group →
  Top.GapAndClusteringAreDerivedNotAssumed
    (R511.concreteEndpointSemantics base bundle)
    group
concreteGapAndClusteringDerived {bundle = bundle} inputs group =
  R511.clusteringHamiltonianIsReconstructed bundle group

concreteNontrivialYangMills :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division
      base bundle}
    (inputs :
      ConcreteEndpointConstructionInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        base bundle)
    group →
  Top.IsNontrivialQuantumYangMills
    (R511.concreteEndpointSemantics base bundle)
    group
    (Top.continuumMeasure (concreteLiteralConstruction inputs) group)
    (Top.schwinger (concreteLiteralConstruction inputs) group)
concreteNontrivialYangMills inputs group =
  ( (λ observable → refl)
  , concreteAcceptedOS inputs group
  )

concreteNontrivialityPreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division
      base bundle}
    (inputs :
      ConcreteEndpointConstructionInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        base bundle)
    group →
  Top.NontrivialityPreservedInLimit
    (R511.concreteEndpointSemantics base bundle)
    group
    (Top.continuumMeasure (concreteLiteralConstruction inputs) group)
concreteNontrivialityPreserved inputs group observable = refl

------------------------------------------------------------------------
-- Exact classification.
------------------------------------------------------------------------

round512ConcreteEndpointConstructionCompilerLevel : ProofLevel
round512ConcreteEndpointConstructionCompilerLevel = machineChecked

round512ContinuumAndSchwingerSemanticsCompilerLevel : ProofLevel
round512ContinuumAndSchwingerSemanticsCompilerLevel = machineChecked

round512OSReconstructionSemanticsCompilerLevel : ProofLevel
round512OSReconstructionSemanticsCompilerLevel = machineChecked

round512GapSemanticsCompilerLevel : ProofLevel
round512GapSemanticsCompilerLevel = machineChecked

round512NontrivialitySemanticsCompilerLevel : ProofLevel
round512NontrivialitySemanticsCompilerLevel = machineChecked
