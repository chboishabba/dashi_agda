module DASHI.Mathematics.Algebra.RationalAlbertF4RootDecompositionDiagnosticExact where

------------------------------------------------------------------------
-- ROOT-DECOMPOSITION DIAGNOSTIC ON THE SAME ALBERT DERIVATION ALGEBRA
--
-- Historical/compatibility owner.  The original deterministic probe used a
-- numerical complexification of ad(H) after exact rational basis/rank work and
-- found the expected F4 profile:
--
--   centralizer dimension 4;
--   48 nonzero one-dimensional root spaces;
--   24 short + 24 long roots with squared-length ratio 2;
--   a standard F4 Cartan simple system.
--
-- That floating root extraction has now been superseded by the exact symbolic
-- Q(i) projector producer recorded in
-- `RationalAlbertF4ExactWeightDecompositionReceiptExact`.  The exact producer
-- proves zero-weight rank 4 and 24+8+8+8 one-dimensional nonzero weight spaces
-- without floating point.  This module is retained so downstream historical
-- imports remain valid while exposing the stronger status explicitly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Algebra.RationalAlbertF4ExactWeightDecompositionReceiptExact as Exact

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
    floatingRootExtractionSuperseded : Bool
    exactQIWeightDecompositionProducerPaid : Bool
    exactTrialityTwentyFourEightEightEightPaid : Bool
    agdaFormalComplexificationPaid : Bool
    agdaFormalRootSpaceDecompositionPaid : Bool
    sameLieAlgebraF4RecognitionPaid : Bool
open RootDecompositionBoundary public

canonicalBoundary : RootDecompositionBoundary
canonicalBoundary =
  root-decomposition-boundary
    true true true true true true true
    true
    Exact.canonicalBoundary.exactQIRootSpaceDecompositionPaidByProducer
    Exact.canonicalBoundary.exactTrialityRootPartitionPaidByProducer
    false false false
