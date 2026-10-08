module DASHI.Mathematics.Algebra.RationalAlbertF4RootDecompositionDiagnosticExact where

------------------------------------------------------------------------
-- ROOT-DECOMPOSITION DIAGNOSTIC ON THE SAME ALBERT DERIVATION ALGEBRA
--
-- Companion exact/numerical scripts operate on the literal 27x27 matrices
-- generated from the repository's RationalAlbert Jordan product.  A 52-element
-- independent basis of inner derivations is selected exactly.  For the
-- deterministic regular element H = sum((i+1) D_i):
--
--   * centralizer(H) has dimension 4;
--   * after numerical complexification of ad(H), there are exactly 48 nonzero
--     one-dimensional root spaces;
--   * the trace/Killing metric splits them into 24 short and 24 long roots;
--   * squared lengths are 1/18 and 1/9 in the chosen normalization (ratio 2);
--   * four root spaces have the standard F4 Cartan matrix
--
--       [ 2 -1  0  0 ]
--       [-1  2 -1  0 ]
--       [ 0 -2  2 -1 ]
--       [ 0  0 -1  2 ].
--
-- The basis/rank/trace computations are exact rational where stated; the
-- eigenspace/root extraction is a deterministic floating diagnostic.  This
-- sharply identifies the intended type but does not replace a formal
-- complexification/root-space theorem in Agda.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

record RootDecompositionDiagnostic : Set where
  constructor root-decomposition-diagnostic
  field
    derivationDimension : Nat
    regularCentralizerDimension : Nat
    zeroAdjointEigenvalueMultiplicity : Nat
    nonzeroRootSpaceCount : Nat
    shortRootCount : Nat
    longRootCount : Nat
    rootLengthRatioTwo : Bool
    standardF4CartanFound : Bool
    deterministicProbePassed : Bool
open RootDecompositionDiagnostic public

canonicalDiagnostic : RootDecompositionDiagnostic
canonicalDiagnostic =
  root-decomposition-diagnostic 52 4 4 48 24 24 true true true

record RootDecompositionBoundary : Set where
  constructor root-decomposition-boundary
  field
    sameAlbertDerivationMatricesUsed : Bool
    exactDimension52InputPaid : Bool
    exactRegularCentralizerRank4Checked : Bool
    complexifiedRootCount48Checked : Bool
    longShortTwentyFourTwentyFourChecked : Bool
    lengthRatioTwoChecked : Bool
    standardF4CartanChecked : Bool
    agdaFormalComplexificationPaid : Bool
    agdaFormalRootSpaceDecompositionPaid : Bool
    sameLieAlgebraF4RecognitionPaid : Bool
open RootDecompositionBoundary public

canonicalBoundary : RootDecompositionBoundary
canonicalBoundary =
  root-decomposition-boundary
    true true true true true true true
    false false false
