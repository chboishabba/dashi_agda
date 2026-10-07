module DASHI.Mathematics.Algebra.RationalAlbertTrialityDerivationDecompositionExact where

------------------------------------------------------------------------
-- TRIALITY DECOMPOSITION OF THE RATIONAL ALBERT DERIVATION ALGEBRA
--
-- Exact-rational companion computation:
--   scripts/check_rational_albert_triality_derivation_decomposition.py
--
-- solves the octonion triality Lie algebra
--
--   A(xy) = B(x)y + x C(y),      A,B,C in so(8),
--
-- on the literal rational-octonion basis.  The 84-variable linear system has
-- rank 56 and nullity 28; each A/B/C projection has full rank 28.
--
-- Under the repository Albert coordinate convention the induced block action
-- on the three octonion coordinates is
--
--   x-block : conjugation o A o conjugation,
--   y-block : B,
--   z-block : C.
--
-- The runtime check verifies all 28 basis triples act as Albert derivations.
-- Three explicit Peirce/inner-derivation families contribute 8+8+8 further
-- independent directions, and the combined exact rational span has rank 52.
--
-- Thus the source-native computational decomposition is
--
--   Der(H_3(O_Q)) = tri(O_Q) + O_Q + O_Q + O_Q
--                  28       + 8   + 8   + 8 = 52.
--
-- This is the standard exceptional decomposition expected for f4, but the file
-- retains the attribution firewall: the Lie type/classification theorem itself
-- is not inferred from dimensions alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact as J
import DASHI.Mathematics.Algebra.RationalAlbertDerivationDimensionExact as Der

------------------------------------------------------------------------
-- Abstract source-facing triality law.
------------------------------------------------------------------------

record OctonionTrialityTriple : Set₁ where
  field
    first second third : O.RationalOctonion → O.RationalOctonion
    trialityLeibniz : (x y : O.RationalOctonion) →
      first (O._*o_ x y)
      ≡ O._+o_
          (O._*o_ (second x) y)
          (O._*o_ x (third y))
open OctonionTrialityTriple public

conjugateTwist :
  (O.RationalOctonion → O.RationalOctonion) →
  O.RationalOctonion → O.RationalOctonion
conjugateTwist f x = O.octonionConjugate (f (O.octonionConjugate x))

trialityAlbertAction : OctonionTrialityTriple → A.RationalAlbert → A.RationalAlbert
trialityAlbertAction t (A.albert a b c x y z) =
  A.albert a b c
    (conjugateTwist (first t) x)
    (second t y)
    (third t z)

------------------------------------------------------------------------
-- Explicit Peirce-family ingredients on the actual Albert product.
------------------------------------------------------------------------

diagonalA diagonalB diagonalC : A.RationalAlbert
diagonalA = A.albert 1ℚ 0ℚ 0ℚ O.zeroO O.zeroO O.zeroO
diagonalB = A.albert 0ℚ 1ℚ 0ℚ O.zeroO O.zeroO O.zeroO
diagonalC = A.albert 0ℚ 0ℚ 1ℚ O.zeroO O.zeroO O.zeroO
  where
    open import Data.Rational.Base using (0ℚ; 1ℚ)

embedX embedY embedZ : O.RationalOctonion → A.RationalAlbert
embedX x = A.albert 0ℚ 0ℚ 0ℚ x O.zeroO O.zeroO
embedY y = A.albert 0ℚ 0ℚ 0ℚ O.zeroO y O.zeroO
embedZ z = A.albert 0ℚ 0ℚ 0ℚ O.zeroO O.zeroO z
  where
    open import Data.Rational.Base using (0ℚ)

peirceX peirceY peirceZ : O.RationalOctonion → A.RationalAlbert → A.RationalAlbert
peirceX x = Der.innerDerivation diagonalB (embedX x)
peirceY y = Der.innerDerivation diagonalC (embedY y)
peirceZ z = Der.innerDerivation diagonalA (embedZ z)

trialityEquationUnknownCount : Nat
trialityEquationUnknownCount = 84

trialityEquationExactRankRuntime : Nat
trialityEquationExactRankRuntime = 56

trialityDimensionRuntime : Nat
trialityDimensionRuntime = 28

peirceXDimensionRuntime peirceYDimensionRuntime peirceZDimensionRuntime : Nat
peirceXDimensionRuntime = 8
peirceYDimensionRuntime = 8
peirceZDimensionRuntime = 8

combinedDerivationDimensionRuntime : Nat
combinedDerivationDimensionRuntime = 52

record TrialityDerivationBoundary : Set where
  constructor triality-derivation-boundary
  field
    trialityLawTyped : Bool
    trialityEquationRank56RuntimeChecked : Bool
    trialityDimension28RuntimeChecked : Bool
    allThreeTrialityProjectionsRank28RuntimeChecked : Bool
    trialityLiftToAlbertDerivationsRuntimeChecked : Bool
    trialityAlbertSpanRank28RuntimeChecked : Bool
    threePeirceFamiliesTyped : Bool
    threePeirceRanksEightRuntimeChecked : Bool
    peirceCombinedRank24RuntimeChecked : Bool
    trialityPlusPeirceRank52RuntimeChecked : Bool
    derivationSpaceExhaustedByDecompositionRuntimeChecked : Bool
    agdaKernelTrialityRankCertificatePaid : Bool
    agdaKernelTrialityLiftDerivationLawPaid : Bool
    f4LieTypeRecognitionPaid : Bool
open TrialityDerivationBoundary public

currentTrialityDerivationBoundary : TrialityDerivationBoundary
currentTrialityDerivationBoundary =
  triality-derivation-boundary
    true true true true true true
    true true true true true
    false false false
