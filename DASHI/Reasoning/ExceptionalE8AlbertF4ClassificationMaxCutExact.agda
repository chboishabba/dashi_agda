module DASHI.Reasoning.ExceptionalE8AlbertF4ClassificationMaxCutExact where

------------------------------------------------------------------------
-- TERMINAL CURRENT EXCEPTIONAL CLASSIFICATION MAX-CUT
--
-- At this point the remaining E6/F4 step is a known classification theorem,
-- not a missing carrier/product/action discovery.
--
-- Internally paid/source-written:
--   * exact rational alternative composition algebra O_Q;
--   * actual H_3(O_Q) 27-dimensional Jordan carrier, unit, cubic norm/product;
--   * commutativity/unit/Jordan identity;
--   * arbitrary inner derivation law;
--   * explicit S3, signed-basis octonion and selected Moufang-triality Albert
--     automorphisms plus arbitrary-word closure;
--   * every compiled Jordan automorphism fixes the actual Jordan unit;
--   * exact derivation diagnostics: dim 52, perfect, center 0, positive trace
--     form, regular centralizer rank 4;
--   * complexified diagnostic: 48 roots = 24 short + 24 long, ratio 2, standard
--     F4 Cartan;
--   * companion Lean independent F4 root/Coxeter datum.
--
-- Classically sourced:
--   * Der(Albert) is central simple Lie algebra of type F4 in char 0;
--   * Aut(Albert) is an algebraic group of type F4;
--   * the cubic determinant symmetry group is of type E6.
--
-- Thus the only formal exceptional-classification seam is importing/proving
-- the scalar-extension/root-space/classification theorem on THIS rational form
-- and constructing the same-carrier E6/F4 group recognition.  Cardinalities,
-- finite minuscule points and dimensions are no longer doing that work.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Mathematics.Algebra.CompositionAlgebraCoreExact as Composition
import DASHI.Mathematics.Algebra.RationalAlbertClassicalE6F4SourceReceiptExact as Source
import DASHI.Mathematics.Algebra.RationalAlbertAutomorphismFixesUnitExact as UnitFix
import DASHI.Mathematics.Algebra.RationalAlbertLinearExceptionalGroupsExact as Linear
import DASHI.Mathematics.Algebra.RationalAlbertF4RootDecompositionDiagnosticExact as RootDiag
import DASHI.Reasoning.ExceptionalE8AlbertF4RootMaxCutExact as Previous

record ExceptionalClassificationBoundary : Set where
  constructor exceptional-classification-boundary
  field
    exactRationalOctonionCompositionCorePaid : Bool
    actualRationalAlbertJordanAlgebraPaid : Bool
    arbitraryInnerDerivationLawPaid : Bool
    actualJordanAutomorphismsFixUnitPaid : Bool
    derivationDimension52PerfectCenterlessDiagnosticPaid : Bool
    compactRank4DiagnosticPaid : Bool
    F4RootDecompositionDiagnosticPaid : Bool
    companionLeanIndependentF4RootDatumPaid : Bool

    classicalDerivationTypeF4SourcePaid : Bool
    classicalAutAlbertTypeF4SourcePaid : Bool
    classicalCubicSymmetryTypeE6SourcePaid : Bool
    linearSameCarrierE6F4TargetTyped : Bool

    formalScalarExtensionRootSpacesPaid : Bool
    formalDerAlbertTypeF4InstantiationPaid : Bool
    formalAutAlbertEqualsF4Paid : Bool
    formalCubicGroupEqualsE6Paid : Bool
    formalF4EqualsE6UnitStabilizerPaid : Bool

    monsterNormalizerPhysicalRealizationPaid : Bool
    originalT5NaturalRestrictionBlocked : Bool
    originalT5IndependentRecognitionPaid : Bool
    empiricalLilaInstantiationPaid : Bool
    note : String
open ExceptionalClassificationBoundary public

canonicalExceptionalClassificationBoundary : ExceptionalClassificationBoundary
canonicalExceptionalClassificationBoundary =
  exceptional-classification-boundary
    true true true true
    true true true true
    true true true true
    false false false false false
    false true false false
    "The exceptional finite/root/Jordan discovery programme is exhausted through an actual rational Albert algebra and an intrinsic structured E8 root datum. Classical sources identify Der(J) and Aut(J) as type F4 and the cubic determinant group as type E6; the remaining formal task is classification/scalar-extension instantiation on this rational form. The Monster normalizer remains source-action dependent; the natural inherited action on the original punctured T5 is already blocked, so any future T5 recognition must introduce genuinely new structure; LILA remains empirical."
