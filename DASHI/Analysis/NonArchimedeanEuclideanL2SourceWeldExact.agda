module DASHI.Analysis.NonArchimedeanEuclideanL2SourceWeldExact where

------------------------------------------------------------------------
-- SOURCE L2 / FINITE EUCLIDEAN SAME-OBJECT WELD
--
-- External source head audited:
--   f94b956e6e970c40c8bb9f9c39e9052ad7a5f884
--
-- L2Mixing.lean does not introduce a separate function-space completion:
--
--   L2Space n := EuclideanSpace ℂ (ZMod (2^n)).
--
-- P_n is built from P_n_matrix by Matrix.toLin in the standard Euclidean
-- `basisFun` basis.  Therefore source L2 squared energy is already the finite
-- coordinate energy consumed by unitary matrix/orthogonal detail decompositions.
--
-- This closes the old same-object concern between "source L2 norm" and
-- "finite Fourier coordinate norm" at the carrier level. Parseval itself is
-- supplied by the normalized DFT unitarity receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record EuclideanL2SourceWeld : Set where
  constructor euclideanL2SourceWeld
  field
    sourceCommit : String
    l2SpaceDefinitionIsEuclideanSpace : Bool
    exactIndexCarrierIsZModTwoPower : Bool
    transitionOperatorBuiltFromConcreteMatrix : Bool
    matrixToLinUsesStandardEuclideanBasis : Bool
    extraMeasureCompletionWeldRequired : Bool
    extraFunctionCoordinateBijectionRequired : Bool
    finiteCoordinateEnergySameObject : Bool

canonicalEuclideanL2SourceWeld : EuclideanL2SourceWeld
canonicalEuclideanL2SourceWeld =
  euclideanL2SourceWeld
    "f94b956e6e970c40c8bb9f9c39e9052ad7a5f884"
    true true true true false false true

finiteCoordinateCarrierIsLiteralSourceL2 :
  EuclideanL2SourceWeld.finiteCoordinateEnergySameObject
    canonicalEuclideanL2SourceWeld
  ≡ true
finiteCoordinateCarrierIsLiteralSourceL2 = refl

noCompletionWeldNeeded :
  EuclideanL2SourceWeld.extraMeasureCompletionWeldRequired
    canonicalEuclideanL2SourceWeld
  ≡ false
noCompletionWeldNeeded = refl
