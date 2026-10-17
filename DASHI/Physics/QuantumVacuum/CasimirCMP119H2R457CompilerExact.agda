module DASHI.Physics.QuantumVacuum.CasimirCMP119H2R457CompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.QuantumVacuum.CasimirMinimalR457SourceNativeCompilerExact as Minimal
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayCMP119DirectPhysicalH2Exact as H2
import DASHI.Physics.YangMills.YangMillsClayCMP119LiteralConstructionCoreExact as Core

------------------------------------------------------------------------
-- CMP119 H2 -> LITERAL Y -> MINIMAL CASIMIR/R457 CONTINUUM ATTACHMENT
--
-- H2 already fixes the finite CMP119 family, continuum measure, Schwinger
-- family and OS reconstruction.  Core.literalConstruction uses exactly those
-- objects.  Hence Casimir does not need an independent literal-construction
-- choice or a full PinnedYangMillsConstruction/mass-gap proof package.
------------------------------------------------------------------------

cmp119LiteralConstructionFromH2Fields :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      sequenceLimit limitLaws quotient division S h2} →
  Core.CMP119LiteralConstructionFields
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
cmp119LiteralConstructionFromH2Fields = Core.literalConstruction

h2AndFieldsBuildMinimalContinuum :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      EuclideanAction Permutation Epsilon Witness
      sequenceLimit limitLaws quotient division S}
    (h2 :
      H2.CMP119DirectPhysicalH2
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S)
    (fields :
      Core.CMP119LiteralConstructionFields
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        EuclideanAction Permutation Epsilon Witness
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division S h2)
    (group : G) →
  Minimal.MinimalContinuumSchwingerAttachment
    S (Core.literalConstruction fields) group
h2AndFieldsBuildMinimalContinuum h2 fields group = record
  { Minimal.MinimalContinuumSchwingerAttachment.literalFiniteMeasuresConverge =
      H2.continuumLimit h2 group
  ; Minimal.MinimalContinuumSchwingerAttachment.literalSchwingerBelongsToContinuumMeasure =
      H2.schwingerBelongsToContinuumMeasure h2 group
  }

record CasimirCMP119H2R457Boundary : Set where
  constructor casimir-cmp119-h2-r457-boundary
  field
    cmp119H2LiteralConstructionCompilerOwned : Bool
    cmp119H2ContinuumAttachmentCompilerOwned : Bool
    pinnedYangMillsConstructionRequiredForCasimirR457 : Bool
    independentLiteralConstructionPaymentRequiredAfterH2Fields : Bool
    cmp119H2PhysicalInstantiationStillRequired : Bool
    r581PreferredFiniteOSMomentSourceStillRequiredInsideH2 : Bool

open CasimirCMP119H2R457Boundary public

canonicalCMP119H2R457Boundary : CasimirCMP119H2R457Boundary
canonicalCMP119H2R457Boundary =
  casimir-cmp119-h2-r457-boundary
    true true false false true true

casimirCMP119H2R457Reading : String
casimirCMP119H2R457Reading =
  "The Casimir/R457 construction-side dependency is not a full PinnedYangMillsConstruction. CMP119 H2 plus CMP119LiteralConstructionFields definitionally builds the literal Y; the same H2 object supplies the finite-to-continuum and Schwinger-membership witnesses needed by the minimal R457 compiler. The first upstream physical/source dependency is therefore H2 instantiation, whose preferred finite-OS source begins at Round581 published Euclidean/bosonic/Wilson-RP applicability, exact-family moments, OS0/OS5 closure and selected OS4 clustering. No positive Clay mass-gap theorem is required for this Casimir stress handoff."
