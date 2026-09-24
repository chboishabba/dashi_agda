{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119LiteralACompletionRound424Exact where

------------------------------------------------------------------------
-- A / ROUND424: ONE LITERAL SOURCE-FED OS + PROJECTIVE COMPLETION OBJECT
--
-- Keep every A theorem on exactly one finite normalized CMP119 family.
-- ConcreteAFromSources already compiles finite Euclidean/bosonic symmetry,
-- Wilson-square OS2, and canonical OS0/OS5 closure to PinnedCMP119OSAxiomInputs.
-- UniformProjectiveCompactness already compiles one uniform tightness theorem,
-- Prokhorov extraction, cylinder determination, and cluster agreement to full
-- sequence convergence.  This owner makes those two routes definitionally use
-- the same family and target.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteAFromSourcesExact as SourceA
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119UniformProjectiveCompactnessExact as Projective
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119SelectedProjectiveCompactnessExact as Selected
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Convergence
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OS
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record LiteralCMP119ACompletion
    (G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
     Epsilon Witness : Set)
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
      SourceA.ConcreteAFromSources
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Action Permutation
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S

    projective :
      ∀ group →
      Projective.CMP119UniformProjectiveInputs
        (SourceA.asPinnedOSAxiomInputs source)
        group Epsilon Witness

open LiteralCMP119ACompletion public

osInputs :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
      Epsilon Witness sequenceLimit limitLaws quotient division S} →
  LiteralCMP119ACompletion
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    Action Permutation Epsilon Witness
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S →
  OS.PinnedCMP119OSAxiomInputs
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    {sequenceLimit = sequenceLimit}
    limitLaws quotient division S
osInputs completion =
  SourceA.asPinnedOSAxiomInputs (source completion)

fullLiteralCMP119ExpectationSequenceConverges :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum Action Permutation
      Epsilon Witness sequenceLimit limitLaws quotient division S}
    (completion :
      LiteralCMP119ACompletion
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
        Action Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    group →
  Convergence.Converges
    (Projective.convergence (projective completion group))
    (Selected.cmp119ExpectationSequence (osInputs completion) group)
    (Selected.cmp119ExpectationTarget (osInputs completion) group)
fullLiteralCMP119ExpectationSequenceConverges completion group =
  Projective.fullCMP119ExpectationSequenceConvergesFromUniformTightness
    (projective completion group)

round424SameFamilyOSProjectiveCompilerLevel : ProofLevel
round424SameFamilyOSProjectiveCompilerLevel = machineChecked

-- No extra A theorem is introduced by this owner.  The physical leaves are
-- exactly those inside ConcreteAFromSources (finite source identifications,
-- OS0/OS5) and CMP119UniformProjectiveInputs (uniform compact containment and
-- extracted-cluster cylinder agreement).
literalRound424ACompletionSourceLevel : ProofLevel
literalRound424ACompletionSourceLevel = conditional
