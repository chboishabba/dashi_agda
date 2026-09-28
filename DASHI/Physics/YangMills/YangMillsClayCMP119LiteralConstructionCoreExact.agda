{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119LiteralConstructionCoreExact where

------------------------------------------------------------------------
-- CONSTRUCT THE LITERAL Y DIRECTLY FROM THE ACTUAL CMP119 H2 OBJECTS.
--
-- No post-hoc finite/continuum/Schwinger/Hamiltonian weld remains:
--
--   Y.finiteMeasure    := exact normalized CMP119 finite family
--   Y.continuumMeasure := exact CMP119 limit measure
--   Y.schwinger        := exact Schwinger family of that measure
--   Y.hilbertSpace     := exact OS reconstruction
--   Y.hamiltonian      := exact OS reconstruction
--
-- Only local-field, vacuum and gap coordinates are supplied separately; those
-- are precisely what C/H3/H6 subsequently identify/prove.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2Exact as H2
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record CMP119LiteralConstructionFields
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
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
          Hilbert Hamiltonian Vector))
    (h2 :
      H2.CMP119DirectPhysicalH2
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    : Set₁ where
  field
    spacetime : X

    localObservable : G → Position → Configuration → ℝ

    curvatureOperator :
      G → CurvaturePolynomial → LocalOperator

    opeCoefficient :
      G → LocalOperator → LocalOperator → LocalOperator →
      Position → OPECoefficient

    opeRemainder :
      G → LocalOperator → LocalOperator → Position → Nat → ℚ

    stressTensor : G → StressTensor

    massGap : G → ℚ

open CMP119LiteralConstructionFields public

literalConstruction :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      sequenceLimit limitLaws quotient division S h2} →
  CMP119LiteralConstructionFields
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
    EuclideanAction Permutation Epsilon Witness
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S h2 →
  Top.LiteralYangMillsConstruction
    (Physical.physicalLiteralCarriers
      G X Nat Configuration ℝ
      (Configuration → ℝ) Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      Hilbert Hamiltonian Vector)
    S
literalConstruction {h2 = h2} fields = record
  { Top.LiteralYangMillsConstruction.spacetime =
      spacetime fields
  ; Top.LiteralYangMillsConstruction.finiteMeasure =
      λ group cutoff →
        Limit.finiteMeasure
          (OSSystem.family (H2.osInputs h2) group)
          cutoff
  ; Top.LiteralYangMillsConstruction.continuumMeasure =
      λ group →
        OSSystem.constructedMeasure
          (H2.osInputs h2) group
  ; Top.LiteralYangMillsConstruction.schwinger =
      λ group →
        OSSystem.constructedSchwinger
          (H2.osInputs h2) group
  ; Top.LiteralYangMillsConstruction.localObservable =
      localObservable fields
  ; Top.LiteralYangMillsConstruction.curvatureOperator =
      curvatureOperator fields
  ; Top.LiteralYangMillsConstruction.opeCoefficient =
      opeCoefficient fields
  ; Top.LiteralYangMillsConstruction.opeRemainder =
      opeRemainder fields
  ; Top.LiteralYangMillsConstruction.stressTensor =
      stressTensor fields
  ; Top.LiteralYangMillsConstruction.hilbertSpace =
      λ group →
        OSR.reconstructedHilbert
          (H2.reconstruction h2) group
  ; Top.LiteralYangMillsConstruction.hamiltonian =
      λ group →
        OSR.reconstructedHamiltonian
          (H2.reconstruction h2) group
  ; Top.LiteralYangMillsConstruction.vacuum =
      λ group →
        OSR.reconstructedVacuum
          (H2.reconstruction h2) group
  ; Top.LiteralYangMillsConstruction.massGap =
      massGap fields
  }

literalFiniteMeasureIsExactCMP119 :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      sequenceLimit limitLaws quotient division S h2}
    (fields :
      CMP119LiteralConstructionFields
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2)
    group cutoff →
  Top.finiteMeasure (literalConstruction fields) group cutoff
  ≡
  Limit.finiteMeasure
    (OSSystem.family (H2.osInputs h2) group)
    cutoff
literalFiniteMeasureIsExactCMP119 fields group cutoff =
  refl

literalContinuumMeasureIsExactCMP119 :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      sequenceLimit limitLaws quotient division S h2}
    (fields :
      CMP119LiteralConstructionFields
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2)
    group →
  Top.continuumMeasure (literalConstruction fields) group
  ≡
  OSSystem.constructedMeasure (H2.osInputs h2) group
literalContinuumMeasureIsExactCMP119 fields group =
  refl

literalSchwingerIsExactCMP119 :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      sequenceLimit limitLaws quotient division S h2}
    (fields :
      CMP119LiteralConstructionFields
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2)
    group →
  Top.schwinger (literalConstruction fields) group
  ≡
  OSSystem.constructedSchwinger (H2.osInputs h2) group
literalSchwingerIsExactCMP119 fields group =
  refl

literalHamiltonianIsExactCMP119OS :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      sequenceLimit limitLaws quotient division S h2}
    (fields :
      CMP119LiteralConstructionFields
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2)
    group →
  Top.hamiltonian (literalConstruction fields) group
  ≡
  OSR.reconstructedHamiltonian (H2.reconstruction h2) group
literalHamiltonianIsExactCMP119OS fields group =
  refl


literalVacuumIsExactCMP119OS :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      sequenceLimit limitLaws quotient division S h2}
    (fields :
      CMP119LiteralConstructionFields
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2)
    group →
  Top.vacuum (literalConstruction fields) group
  ≡
  OSR.reconstructedVacuum (H2.reconstruction h2) group
literalVacuumIsExactCMP119OS fields group = refl

cmp119LiteralConstructionCoreLevel : ProofLevel
cmp119LiteralConstructionCoreLevel = machineChecked
