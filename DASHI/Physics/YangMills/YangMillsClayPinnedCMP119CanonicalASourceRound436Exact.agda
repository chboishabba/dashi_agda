{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119CanonicalASourceRound436Exact where

------------------------------------------------------------------------
-- A / ROUND436: ONE FINITE-MEASURE SOURCE -> COMPLETE LITERAL A SOURCE
--
-- R431 reduced finite Euclidean/bosonic invariance to:
--   pullback action + Wilson/Gibbs density invariance + product-Haar invariance.
-- This owner applies that theorem once per selected action family and feeds the
-- resulting finite symmetries, Wilson-square OS2 and canonical OS0/OS5 data
-- directly into ConcreteAFromSources.  Adding R424 projective data then gives
-- the one-family A completion.
--
-- No finite normalized symmetry theorem is assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsContinuumSchwingerFromMeasureExact as Schwinger
import DASHI.Physics.YangMills.YangMillsCylinderLimitOSReflectionPositiveExact as OS2
import DASHI.Physics.YangMills.YangMillsFiniteHaarActionNumeratorInvariantRound431Exact as Haar
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119FiniteEuclideanSourceExact as Euclidean
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119BosonicOS3SourceExact as Bosonic
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119StandaloneWilsonSquareExact as Wilson
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OS05CanonicalLimitExact as OS05
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteAFromSourcesExact as SourceA
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LiteralACompletionRound424Exact as R424
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119UniformProjectiveCompactnessExact as Projective
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CanonicalCMP119ASource
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
     EuclideanAction Permutation : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ
          (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum))
    : Set₂ where
  field
    family : ∀ group →
      Limit.FinitePhysicalNormalizedFamily
        Configuration limitLaws quotient division

    cylinderEncoding :
      Schwinger.CylinderSchwingerEncoding
        (Configuration → ℝ) Position

    observableAlgebra :
      OS2.CylinderOSAlgebra (Configuration → ℝ)

    euclideanActConfiguration :
      EuclideanAction → Configuration → Configuration
    euclideanActObservable :
      EuclideanAction →
      (Configuration → ℝ) → Configuration → ℝ
    euclideanPullback :
      ∀ action observable configuration →
      euclideanActObservable action observable configuration
      ≡ observable (euclideanActConfiguration action configuration)

    euclideanHaarAction :
      ∀ group cutoff →
      Haar.FiniteHaarMeasurePreservingAction
        {Configuration = Configuration} {Action = EuclideanAction}
        (Limit.finiteMeasure (family group) cutoff)
        (Limit.integrationLaws (family group) cutoff)

    euclideanLocalActionIsGlobal :
      ∀ group cutoff action observable configuration →
      Haar.actObservable (euclideanHaarAction group cutoff)
        action observable configuration
      ≡ euclideanActObservable action observable configuration

    permuteObservable :
      Permutation → (Configuration → ℝ) → Configuration → ℝ

    bosonicHaarAction :
      ∀ group cutoff →
      Haar.FiniteHaarMeasurePreservingAction
        {Configuration = Configuration} {Action = Permutation}
        (Limit.finiteMeasure (family group) cutoff)
        (Limit.integrationLaws (family group) cutoff)

    bosonicLocalActionIsGlobal :
      ∀ group cutoff permutation observable configuration →
      Haar.actObservable (bosonicHaarAction group cutoff)
        permutation observable configuration
      ≡ permuteObservable permutation observable configuration

    GaugeInvariantBosonic : (Configuration → ℝ) → Set
    selectedObservablesAreGaugeInvariantBosonic :
      ∀ observable → GaugeInvariantBosonic observable

    wilson :
      ∀ group →
      Wilson.StandaloneCMP119WilsonSquare
        Configuration (family group) observableAlgebra

    os05 :
      ∀ group →
      OS05.CanonicalCMP119OS05LimitData
        Configuration (family group)

    OS4Clustering : G → Set
    os4 : ∀ group → OS4Clustering group

open CanonicalCMP119ASource public

euclideanSource :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    (source :
      CanonicalCMP119ASource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  Euclidean.CMP119WholeLatticeEuclideanCovariance
    Configuration EuclideanAction (family source group)
euclideanSource source group =
  Euclidean.euclideanFromNumeratorChangeOfVariables
    (euclideanActConfiguration source)
    (euclideanActObservable source)
    (euclideanPullback source)
    (Haar.familyNumeratorActionInvariant
      (family source group)
      (euclideanActObservable source)
      (euclideanHaarAction source group)
      (euclideanLocalActionIsGlobal source group))

bosonicSource :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S}
    (source :
      CanonicalCMP119ASource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  Bosonic.LiteralCMP119BosonicPermutationSymmetry
    Configuration Permutation (family source group)
bosonicSource source group =
  Bosonic.bosonicFromNumeratorChangeOfVariables
    (permuteObservable source)
    (GaugeInvariantBosonic source)
    (selectedObservablesAreGaugeInvariantBosonic source)
    (Haar.familyNumeratorActionInvariant
      (family source group)
      (permuteObservable source)
      (bosonicHaarAction source group)
      (bosonicLocalActionIsGlobal source group))

asConcreteAFromSources :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation sequenceLimit limitLaws quotient division S} →
  CanonicalCMP119ASource
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    EuclideanAction Permutation
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  SourceA.ConcreteAFromSources
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    EuclideanAction Permutation
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
asConcreteAFromSources source = record
  { SourceA.ConcreteAFromSources.family = family source
  ; SourceA.ConcreteAFromSources.cylinderEncoding = cylinderEncoding source
  ; SourceA.ConcreteAFromSources.observableAlgebra = observableAlgebra source
  ; SourceA.ConcreteAFromSources.euclidean = euclideanSource source
  ; SourceA.ConcreteAFromSources.bosonic = bosonicSource source
  ; SourceA.ConcreteAFromSources.wilson = wilson source
  ; SourceA.ConcreteAFromSources.os05 = os05 source
  ; SourceA.ConcreteAFromSources.OS4Clustering = OS4Clustering source
  ; SourceA.ConcreteAFromSources.os4 = os4 source
  }

record CanonicalCMP119ACompletion
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
     EuclideanAction Permutation Epsilon Witness : Set)
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    (limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit)
    (quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit))
    (division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient)
    (S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ
          (Configuration → ℝ) Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum))
    : Set₂ where
  field
    source :
      CanonicalCMP119ASource
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        EuclideanAction Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S

    projective :
      ∀ group →
      Projective.CMP119UniformProjectiveInputs
        (SourceA.asPinnedOSAxiomInputs (asConcreteAFromSources source))
        group Epsilon Witness

open CanonicalCMP119ACompletion public

asRound424Completion :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
      EuclideanAction Permutation Epsilon Witness
      sequenceLimit limitLaws quotient division S} →
  CanonicalCMP119ACompletion
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    EuclideanAction Permutation Epsilon Witness
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  R424.LiteralCMP119ACompletion
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    EuclideanAction Permutation Epsilon Witness
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
asRound424Completion completion = record
  { R424.LiteralCMP119ACompletion.source =
      asConcreteAFromSources (source completion)
  ; R424.LiteralCMP119ACompletion.projective =
      projective completion
  }

round436FiniteSymmetryCompilerLevel : ProofLevel
round436FiniteSymmetryCompilerLevel = machineChecked

round436LiteralAAssemblyCompilerLevel : ProofLevel
round436LiteralAAssemblyCompilerLevel = machineChecked

-- Remaining Goal-1 A mathematics on this route:
-- * actual finite Haar/density action invariance (A1);
-- * Wilson/Peter-Weyl square factorization (A2);
-- * uniform projective compact containment + cylinder agreement (A3 fallback);
-- * finite OS0 regularity and OS5 growth bounds (A4/A5).
-- R430 may replace the projective semantic interpretation once R129 is present.
literalRound436CanonicalASourceLevel : ProofLevel
literalRound436CanonicalASourceLevel = conditional
