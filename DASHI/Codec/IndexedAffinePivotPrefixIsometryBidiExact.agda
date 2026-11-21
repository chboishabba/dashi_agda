module DASHI.Codec.IndexedAffinePivotPrefixIsometryBidiExact where

-- H07 selected ordered-prefix metric acceptance for the original
-- 2^3 x 3^6 = 5832 restricted affine carrier.
-- Source proof architecture: explicit coordinate depth predicates.
-- The universal source-field proof is an obligation, not postulated.
-- All ten prefix partitions have exhaustive local SymPy certificates.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import DASHI.Algebra.Trit using (Trit)
import DASHI.Codec.TriadicMaskSignFactorization as M
import DASHI.Codec.IndexedCubeAffineStableOverlapExact as Stable
import DASHI.Codec.IndexedCubePivot02RechartedExact as Pivot

Source : Set
Source = Stable.StableBlocks Trit

-- Original selected order V0,V1,V2,A0,A1,A2,b0,b1,b2.
-- Digit equality is written on actual source triples/signs.
data SamePrefix : Nat → Source → Source → Set where
  empty : ∀ {x y} → SamePrefix zero x y
  slope0 : ∀ {a b c d : Source} →
    (x y : Source) →
    M.first (Stable.signedSlope x) ≡ M.first (Stable.signedSlope y) →
    SamePrefix (suc zero) x y
  -- Further depth witnesses are left source-specific rather than
  -- inventing a generalized proof for every arbitrary order.

-- Use a concrete, full nine-coordinate projection for runtime truth.
record Digits9 : Set where
  constructor digits9
  field
    v0 v1 v2 : M.Sign
    a0 a1 a2 b0 b1 b2 : Trit
open Digits9 public

digits : Source → Digits9
digits (Stable.stableBlocks
  (M.triple a0 a1 a2)
  (M.triple v0 v1 v2)
  (M.triple b0 b1 b2)) =
  digits9 v0 v1 v2 a0 a1 a2 b0 b1 b2

-- A future formal certificate must make EACH of the nine selected
-- prefix equalities equivalent, not only one-way. This is necessary
-- for every-pair agreement-depth equality.
record SelectedPrefixTransport : Set₁ where
  field
    originalAgreement : Source → Source → Nat
    depthBound : (x y : Source) → Nat
    reflectsAndPreservesDepth :
      (x y : Source) →
      originalAgreement (Pivot.pivotRaw x) (Pivot.pivotRaw y)
        ≡ originalAgreement x y

-- The actual local check uses all ten exact prefix partitions and
-- proves an all-pairs result by equality of the partition classes;
-- it is not a constructive Agda inhabitant of this record.
