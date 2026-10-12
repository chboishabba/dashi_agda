module DASHI.Mathematics.Algebra.Ternary27FirstTitsDerivationF4SignalExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Mathematics.Algebra.Ternary27FirstTitsAlbertExact as Tits
import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as Compact

------------------------------------------------------------------------
-- CORRECTED FIRST-TITS DERIVATION / F4 SIGNAL
--
-- The authoritative local executable for this tranche is
--
--   scripts/exceptional_f4_derivation_maxcut_probe.py
--
-- It uses the standard first-Tits normalization in which x cross y is one
-- half of the bilinearized adjoint and appears directly (not with another
-- outer factor one-half) in the second and third M3 sectors.
--
-- On J(M3(F3),1), the complete linear derivation equations have 729 unknown
-- matrix entries and rank 677, hence a 52-dimensional derivation space.
-- Every derivation is already in the span of inner derivations [L_x,L_y].
-- The resulting 52-dimensional Lie algebra is perfect and centreless in the
-- finite computation, and its common fixed subspace on the 27-dimensional
-- carrier has dimension one.
--
-- This is a strong F4 recognition signal on the actual product/action carrier,
-- but it is deliberately not promoted to an identification with the Chevalley
-- Lie algebra/group of type F4 until a root/action recognition receipt exists.
------------------------------------------------------------------------

record FirstTitsDerivationF4LocalReceipt : Set where
  constructor first-tits-derivation-f4-local-receipt
  field
    standardFirstTitsNormalisationUsed : Bool
    all729BasisJordanChecksPass : Bool
    randomFullJordanChecksPass : Bool
    derivationUnknownCount : Nat
    derivationConstraintRank : Nat
    derivationDimension : Nat
    innerDerivationSpanDimension : Nat
    derivedBracketSpanDimension : Nat
    derivationCentreDimension : Nat
    commonFixedSubspaceDimension : Nat
    dimension52MatchesClassicalF4LieDimension : Bool
    actualF4RootRecognitionPaid : Bool
    actualF4GroupRecognitionPaid : Bool
    characteristicThreeSmoothGroupRecognitionPaid : Bool
    boundary : String
open FirstTitsDerivationF4LocalReceipt public

canonicalFirstTitsDerivationF4LocalReceipt : FirstTitsDerivationF4LocalReceipt
canonicalFirstTitsDerivationF4LocalReceipt =
  first-tits-derivation-f4-local-receipt
    true true true
    729 677 52 52 52 0 1
    true
    false false false
    "The corrected J(M3(F3),1) product has a 52-dimensional, inner-generated, perfect, centreless derivation Lie algebra with one common fixed direction. This is same-product/action evidence, not yet a theorem identifying the characteristic-three derivation algebra or automorphism group with F4."

------------------------------------------------------------------------
-- RATIONAL-FORM OBSTRUCTION TO THE OLD SAME-OBJECT TARGET
--
-- The rational first-Tits M3^3 trace bilinear form has signature (15,12).
-- The repository's existing rational H3(O_Q) uses the positive Cayley-Dickson
-- octonion norm.  Directly from its Jordan-product diagonal coordinates,
--
--   tr(X o X) = a^2+b^2+c^2 + 2(n(x)+n(y)+n(z)),
--
-- hence its real/rational trace-square form is positive definite.
-- A literal first-Tits witness is the first-sector skew matrix E01-E10, whose
-- trace-square equals -2.  Therefore the formerly proposed trace-preserving
-- same-object intertwiner to this *particular positive form* is impossible.
-- The correct target is a split Albert / split-octonion realization, while the
-- existing positive rational Albert remains a separate real-form lane.
------------------------------------------------------------------------

record FirstTitsCompactAlbertNoGoReceipt : Set where
  constructor first-tits-compact-albert-no-go-receipt
  field
    firstTitsPositiveSignatureCount : Nat
    firstTitsNegativeSignatureCount : Nat
    firstTitsTraceGramDeterminantOne : Bool
    explicitNegativeWitnessPresent : Bool
    explicitNegativeWitnessTraceSquare : String
    existingOctonionNormPositiveSumOfSquares : Bool
    compactAlbertPositiveSignatureCount : Nat
    tracePreservingSameObjectIntertwinerPossible : Bool
    splitAlbertTargetRequiredForThisRoute : Bool
    boundary : String
open FirstTitsCompactAlbertNoGoReceipt public

canonicalFirstTitsCompactAlbertNoGoReceipt : FirstTitsCompactAlbertNoGoReceipt
canonicalFirstTitsCompactAlbertNoGoReceipt =
  first-tits-compact-albert-no-go-receipt
    15 12 true true "-2" true 27 false true
    "The ternary first-Tits carrier and the current positive-norm rational H3(O_Q) carrier are different forms. Signature obstruction retires the direct trace-preserving intertwiner; it does not refute either Albert construction or a future split-Albert equivalence."

------------------------------------------------------------------------
-- Fail-closed promotion boundaries.
------------------------------------------------------------------------

data DerivationDimension52CreatesF4 : Set where
data PerfectCentrelessCreatesF4 : Set where
data DifferentRationalFormsMeansNoAlbertRelation : Set where

derivation52DoesNotCreateF4 : DerivationDimension52CreatesF4 → {A : Set} → A
derivation52DoesNotCreateF4 ()

perfectCentrelessDoesNotCreateF4 : PerfectCentrelessCreatesF4 → {A : Set} → A
perfectCentrelessDoesNotCreateF4 ()

differentFormsDoNotEraseAlbertRelation : DifferentRationalFormsMeansNoAlbertRelation → {A : Set} → A
differentFormsDoNotEraseAlbertRelation ()
