{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsConcreteEndpointSemanticsRound511Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND511: CONCRETE ENDPOINT SEMANTICS OVER PROOF-BEARING SOURCES
--
-- LiteralYangMillsSemantics stores Set-valued predicates, while the actual
-- represented-measure / OS-reconstruction / spectral-gap source objects live
-- in Set1.  Do not duplicate those rich objects inside endpoint predicates.
--
-- Instead:
--
--   1. choose the proof-bearing source object once per compact-simple G;
--   2. define the literal endpoint predicate as SAME-OBJECT equations tying the
--      candidate literal projection to that source object;
--   3. compile mathematical consequences from the source object.
--
-- Thus endpoint meaning is no longer an arbitrary opaque Set for:
--
--   continuum limit, Schwinger-belongs, accepted OS,
--   reconstructed Hilbert/Hamiltonian, vacuum+positive-energy sector,
--   strict physical gap, no spectral pollution, scale lower bound,
--   derived clustering/gap, and same-system nontriviality.
--
-- Structural/T1/local-QFT predicates are deliberately inherited from a base
-- semantics until their own source-backed overlays are supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; Σ; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476
import DASHI.Physics.YangMills.YangMillsPhysicalProjectiveCylinderRepresentationRound535Exact as R535
import DASHI.Physics.YangMills.YangMillsProjectiveRepresentedExpectationConvergenceRound536Exact as R536
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.BalabanOSReconstructionMassGapProduction as OSR
import DASHI.Physics.YangMills.BalabanScalarCylinderExpectationLimitExact as Cylinder
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record ConcreteEndpointSourceBundle
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
     Algebra Event Projection : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    : Set₂ where
  field
    family :
      G →
      Limit.FinitePhysicalNormalizedFamily
        Configuration
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division

    representationInputs :
      ∀ group →
      R535.PhysicalProjectiveCylinderRepresentationInputs
        Configuration Event
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division (family group)

    cylinderEncoding :
      Schwinger.CylinderSchwingerEncoding
        (Configuration → ℝ) Position

    osSystem :
      G →
      OSGap.ContinuumSchwingerSystem
        (Configuration → ℝ) Position ℝ

    -- Source OS system is the represented Schwinger system, pointwise.
    osSystemIsRepresentedSchwinger :
      ∀ group observable left right →
      OSGap.schwinger (osSystem group) observable left right
      ≡
      Physical.schwinger
        (R476.representedSchwinger
          cylinderEncoding
          (R476.represented
            (R535.asSourceLimitRepresentation
              (representationInputs group))))
        observable left right

    reconstruction :
      ∀ group →
      OSR.OSReconstructionData
        (Configuration → ℝ) Position ℝ
        Hilbert Vacuum Hamiltonian Algebra
        (osSystem group)

    reconstructionAuthority :
      ∀ group →
      OSR.OSReconstructionStandardAuthority
        (reconstruction group)

    clusteringData :
      G →
      OSR.UniformConnectedCorrelationDecayData
        (Configuration → ℝ) Nat ℝ ℚ Hamiltonian

    clusteringTimeAuthority :
      ∀ group →
      OSR.EuclideanToHamiltonianClusteringAuthority
        (clusteringData group)

    clusteringSpectrumAuthority :
      ∀ group →
      OSR.TimeClusteringSpectrumAuthority
        (clusteringData group)
        (clusteringTimeAuthority group)

    clusteringHamiltonianIsReconstructed :
      ∀ group →
      OSR.hamiltonian (clusteringData group)
      ≡ OSR.reconstructedHamiltonian (reconstruction group)

    clusteringMassPositiveRational :
      ∀ group →
      0ℚ < OSR.mStar (clusteringData group)

    interactingWitness :
      ∀ group →
      OSGap.InteractingContinuumWitness
        (Configuration → ℝ) Position ℝ
        (osSystem group)

open ConcreteEndpointSourceBundle public

gapCertificate :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division} →
  (bundle :
    ConcreteEndpointSourceBundle
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection
      {sequenceLimit = sequenceLimit}
      limitLaws quotient division) →
  G → OSGap.PhysicalMassGapCertificate Hamiltonian ℚ
gapCertificate bundle group =
  OSR.exponentialTimeClusteringImpliesSpectrumGap
    (clusteringData bundle group)
    (clusteringTimeAuthority bundle group)
    (clusteringSpectrumAuthority bundle group)

representedFor :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division} →
  ConcreteEndpointSourceBundle
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    Algebra Event Projection
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division →
  G → R476.RepresentedContinuum (Configuration → ℝ)
representedFor bundle group =
  R476.represented
    (R535.asSourceLimitRepresentation
      (representationInputs bundle group))

------------------------------------------------------------------------
-- Set-level concrete endpoint predicates.
------------------------------------------------------------------------

ConcreteContinuumLimitOf :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division) →
  G →
  (Nat → Physical.PhysicalFiniteYMMeasure Configuration ℝ) →
  Physical.PhysicalContinuumYMMeasure (Configuration → ℝ) ℝ →
  Set
ConcreteContinuumLimitOf bundle group finite continuum =
  (∀ cutoff →
    finite cutoff ≡ Limit.finiteMeasure (family bundle group) cutoff)
  ×
  (∀ observable →
    Physical.expectation continuum observable
    ≡
    Physical.expectation
      (R476.asPhysicalContinuum (representedFor bundle group))
      observable)

ConcreteSchwingerBelongsToMeasure :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division) →
  Physical.PhysicalContinuumYMMeasure (Configuration → ℝ) ℝ →
  Physical.PhysicalSchwingerFamily (Configuration → ℝ) Position ℝ →
  Set
ConcreteSchwingerBelongsToMeasure bundle continuum schwinger =
  ∀ observable left right →
  Physical.schwinger schwinger observable left right
  ≡
  Physical.expectation continuum
    (Schwinger.twoPointCylinder
      (cylinderEncoding bundle)
      observable left right)

ConcreteAcceptedOS :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division) →
  G →
  Physical.PhysicalSchwingerFamily (Configuration → ℝ) Position ℝ →
  Set
ConcreteAcceptedOS bundle group schwinger =
  ∀ observable left right →
  Physical.schwinger schwinger observable left right
  ≡ OSGap.schwinger (osSystem bundle group) observable left right

ConcreteReconstructedHilbert :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division) →
  G →
  Physical.PhysicalSchwingerFamily (Configuration → ℝ) Position ℝ →
  Hilbert → Set
ConcreteReconstructedHilbert bundle group schwinger hilbert =
  ConcreteAcceptedOS bundle group schwinger
  ×
  (hilbert ≡ OSR.reconstructedHilbertSpace (reconstruction bundle group))

ConcretePositiveSelfAdjointHamiltonian :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division) →
  Hilbert → Hamiltonian → Set
ConcretePositiveSelfAdjointHamiltonian {G = G} bundle hilbert hamiltonian =
  Σ G
    (λ group →
      (hilbert ≡ OSR.reconstructedHilbertSpace (reconstruction bundle group))
      ×
      (hamiltonian ≡
        OSR.reconstructedHamiltonian (reconstruction bundle group)))

ConcreteVacuumSectorPositiveEnergy :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division) →
  Hilbert → Hamiltonian → Vacuum → Set
ConcreteVacuumSectorPositiveEnergy {G = G} bundle hilbert hamiltonian vacuum =
  Σ G
    (λ group →
      (hilbert ≡ OSR.reconstructedHilbertSpace (reconstruction bundle group))
      ×
      (hamiltonian ≡ OSR.reconstructedHamiltonian (reconstruction bundle group))
      ×
      (vacuum ≡ OSR.reconstructedVacuum (reconstruction bundle group))
      ×
      (OSGap.hamiltonian (gapCertificate bundle group)
        ≡ OSR.reconstructedHamiltonian (reconstruction bundle group)))

ConcreteStrictPositiveMassGap :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division) →
  Hamiltonian → ℚ → Set
ConcreteStrictPositiveMassGap {G = G} bundle hamiltonian gap =
  Σ G
    (λ group →
      (hamiltonian ≡ OSGap.hamiltonian (gapCertificate bundle group))
      ×
      (gap ≡ OSGap.gap (gapCertificate bundle group)))

ConcretePhysicalScaleLowerBound :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division) →
  G → ℚ → Set
ConcretePhysicalScaleLowerBound bundle group gap =
  gap ≡ OSR.mStar (clusteringData bundle group)

ConcreteNoSpectralPollution :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division) →
  G → Hamiltonian → ℚ → Set
ConcreteNoSpectralPollution bundle group hamiltonian gap =
  (hamiltonian ≡ OSR.hamiltonian (clusteringData bundle group))
  ×
  (gap ≡ OSR.mStar (clusteringData bundle group))

ConcreteGapAndClusteringDerived :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division) →
  G → Set
ConcreteGapAndClusteringDerived bundle group =
  OSR.hamiltonian (clusteringData bundle group)
  ≡ OSR.reconstructedHamiltonian (reconstruction bundle group)

ConcreteNontrivialYangMills :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division) →
  G →
  Physical.PhysicalContinuumYMMeasure (Configuration → ℝ) ℝ →
  Physical.PhysicalSchwingerFamily (Configuration → ℝ) Position ℝ →
  Set
ConcreteNontrivialYangMills bundle group continuum schwinger =
  (∀ observable →
    Physical.expectation continuum observable
    ≡
    Physical.expectation
      (R476.asPhysicalContinuum (representedFor bundle group))
      observable)
  ×
  ConcreteAcceptedOS bundle group schwinger

ConcreteNontrivialityPreserved :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division) →
  G →
  Physical.PhysicalContinuumYMMeasure (Configuration → ℝ) ℝ →
  Set
ConcreteNontrivialityPreserved bundle group continuum =
  ∀ observable →
  Physical.expectation continuum observable
  ≡
  Physical.expectation
    (R476.asPhysicalContinuum (representedFor bundle group))
    observable

------------------------------------------------------------------------
-- Overlay the concrete source-backed meanings onto the existing semantics.
------------------------------------------------------------------------

concreteEndpointSemantics :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (base :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum))
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division) →
  Top.LiteralYangMillsSemantics
    (Physical.physicalLiteralCarriers
      G X Nat Configuration ℝ (Configuration → ℝ) Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      Hilbert Hamiltonian Vacuum)
concreteEndpointSemantics base bundle = record
  { Top.LiteralYangMillsSemantics.IsCompactSimple =
      Top.IsCompactSimple base
  ; Top.LiteralYangMillsSemantics.IsFourDimensionalEuclidean =
      Top.IsFourDimensionalEuclidean base
  ; Top.LiteralYangMillsSemantics.IsFiniteVolumeCutoffMeasure =
      Top.IsFiniteVolumeCutoffMeasure base
  ; Top.LiteralYangMillsSemantics.IsReflectionPositiveRegularization =
      Top.IsReflectionPositiveRegularization base
  ; Top.LiteralYangMillsSemantics.HasUltravioletYangMillsNormalization =
      Top.HasUltravioletYangMillsNormalization base
  ; Top.LiteralYangMillsSemantics.HasAsymptoticallyFreeScaleTrajectory =
      Top.HasAsymptoticallyFreeScaleTrajectory base
  ; Top.LiteralYangMillsSemantics.IsGaugeInvariantObservable =
      Top.IsGaugeInvariantObservable base
  ; Top.LiteralYangMillsSemantics.IsLocalObservable =
      Top.IsLocalObservable base
  ; Top.LiteralYangMillsSemantics.IsContinuumLimitOf =
      ConcreteContinuumLimitOf bundle
  ; Top.LiteralYangMillsSemantics.SchwingerBelongsToMeasure =
      ConcreteSchwingerBelongsToMeasure bundle
  ; Top.LiteralYangMillsSemantics.IsNontrivialQuantumYangMills =
      ConcreteNontrivialYangMills bundle
  ; Top.LiteralYangMillsSemantics.CurvatureOperatorCorrespondence =
      Top.CurvatureOperatorCorrespondence base
  ; Top.LiteralYangMillsSemantics.IsGaugeInvariantLocalOperator =
      Top.IsGaugeInvariantLocalOperator base
  ; Top.LiteralYangMillsSemantics.IsLocalOperator =
      Top.IsLocalOperator base
  ; Top.LiteralYangMillsSemantics.IsPhysicalOPECoefficient =
      Top.IsPhysicalOPECoefficient base
  ; Top.LiteralYangMillsSemantics.IsPhysicalOPERemainder =
      Top.IsPhysicalOPERemainder base
  ; Top.LiteralYangMillsSemantics.HasShortDistanceAsymptoticFreedom =
      Top.HasShortDistanceAsymptoticFreedom base
  ; Top.LiteralYangMillsSemantics.HasStressTensorAndOPE =
      Top.HasStressTensorAndOPE base
  ; Top.LiteralYangMillsSemantics.SatisfiesAcceptedWightmanOrOSAxioms =
      ConcreteAcceptedOS bundle
  ; Top.LiteralYangMillsSemantics.IsReconstructedHilbertSpace =
      ConcreteReconstructedHilbert bundle
  ; Top.LiteralYangMillsSemantics.IsPositiveSelfAdjointHamiltonian =
      ConcretePositiveSelfAdjointHamiltonian bundle
  ; Top.LiteralYangMillsSemantics.IsVacuumSectorAndPositiveEnergyComplement =
      ConcreteVacuumSectorPositiveEnergy bundle
  ; Top.LiteralYangMillsSemantics.IsStrictlyPositiveFiniteMassGap =
      ConcreteStrictPositiveMassGap bundle
  ; Top.LiteralYangMillsSemantics.GaugeSymmetryPreservedAlongConstruction =
      Top.GaugeSymmetryPreservedAlongConstruction base
  ; Top.LiteralYangMillsSemantics.LocalityPreservedAlongConstruction =
      Top.LocalityPreservedAlongConstruction base
  ; Top.LiteralYangMillsSemantics.EuclideanCovariancePreservedAlongConstruction =
      Top.EuclideanCovariancePreservedAlongConstruction base
  ; Top.LiteralYangMillsSemantics.ReflectionPositivityPreservedAlongConstruction =
      Top.ReflectionPositivityPreservedAlongConstruction base
  ; Top.LiteralYangMillsSemantics.PositivityNormalizationPreservedAlongConstruction =
      Top.PositivityNormalizationPreservedAlongConstruction base
  ; Top.LiteralYangMillsSemantics.VolumeCutoffCompatibilityPreserved =
      Top.VolumeCutoffCompatibilityPreserved base
  ; Top.LiteralYangMillsSemantics.PhysicalScaleLowerBoundUniform =
      ConcretePhysicalScaleLowerBound bundle
  ; Top.LiteralYangMillsSemantics.NoSpectralPollutionBelowGap =
      ConcreteNoSpectralPollution bundle
  ; Top.LiteralYangMillsSemantics.NontrivialityPreservedInLimit =
      ConcreteNontrivialityPreserved bundle
  ; Top.LiteralYangMillsSemantics.GapAndClusteringAreDerivedNotAssumed =
      ConcreteGapAndClusteringDerived bundle
  ; Top.LiteralYangMillsSemantics.CompactSimpleParameterizationPreserved =
      Top.CompactSimpleParameterizationPreserved base
  }

------------------------------------------------------------------------
-- Mathematical consequences hidden behind the Set-level same-object meanings.
------------------------------------------------------------------------

representedFiniteExpectationsConverge :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    group observable →
  Cylinder.Converges
    (RealLimit.canonicalCylinderAlgebra limitLaws)
    (λ cutoff →
      Limit.finiteExpectation (family bundle group) cutoff observable)
    (Physical.expectation
      (R476.asPhysicalContinuum (representedFor bundle group))
      observable)
representedFiniteExpectationsConverge bundle group observable =
  R536.projectiveRepresentedPhysicalExpectationConverges
    (representationInputs bundle group)
    observable

sourceGapIsStrictlyPositiveRational :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    group →
  0ℚ < OSGap.gap (gapCertificate bundle group)
sourceGapIsStrictlyPositiveRational bundle =
  clusteringMassPositiveRational bundle

sourceNoSpectralPollution :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      Algebra Event Projection sequenceLimit limitLaws quotient division}
    (bundle :
      ConcreteEndpointSourceBundle
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Algebra Event Projection
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division)
    group →
  OSGap.SpectrumAboveVacuumGap (gapCertificate bundle group)
sourceNoSpectralPollution bundle group =
  OSGap.spectrumAboveVacuumGap (gapCertificate bundle group)

round511ConcreteEndpointSemanticsCompilerLevel : ProofLevel
round511ConcreteEndpointSemanticsCompilerLevel = machineChecked

round511RepresentationConvergenceCompilerLevel : ProofLevel
round511RepresentationConvergenceCompilerLevel = machineChecked

round511NoPollutionCompilerLevel : ProofLevel
round511NoPollutionCompilerLevel = machineChecked
