module DASHI.Codec.IndexedAffinePivotPrefixIsometryBidiExact where

-- H07: the actual nine selected digits, and prefix equality at
-- EVERY depth. This replaces the previous 0/1-only witness interface.
-- Source-written: the source-specific F3 algebra proof remains OPEN;
-- SymPy symbolically confirms triangular units + involution and checks
-- the complete 5832-carrier partition certificate. No Agda run.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import DASHI.Algebra.Trit using (Trit)
import DASHI.Codec.TriadicMaskSignFactorization as M
import DASHI.Codec.IndexedCubeAffineStableOverlapExact as Stable
import DASHI.Codec.IndexedCubePivot02RechartedExact as Pivot

Source : Set
Source = Stable.StableBlocks Trit

-- Preserve the selected coefficient order V0,V1,V2,A0,A1,A2,b0,b1,b2.
-- Sign values use the EXISTING original nonzero trit map, and thus
-- occupy the first three digits but cannot introduce a zero slope.
selectedDigits : Source → List Trit
selectedDigits (Stable.stableBlocks
  (M.triple a0 a1 a2)
  (M.triple v0 v1 v2)
  (M.triple b0 b1 b2)) =
  Stable.rawSlope v0 ∷ Stable.rawSlope v1 ∷ Stable.rawSlope v2 ∷
  a0 ∷ a1 ∷ a2 ∷ b0 ∷ b1 ∷ b2 ∷ []

prefix : Nat → List Trit → List Trit
prefix zero _ = []
prefix (suc k) [] = []
prefix (suc k) (d ∷ ds) = d ∷ prefix k ds

-- The original selected prefix partition, including the full 9-digit
-- equality case, not a declaration of a metric on some other carrier.
PrefixEqual : Nat → Source → Source → Set
PrefixEqual k x y =
  prefix k (selectedDigits x) ≡ prefix k (selectedDigits y)

prefixZero : (x y : Source) → PrefixEqual zero x y
prefixZero x y = refl

prefixSelf : (k : Nat) (x : Source) → PrefixEqual k x x
prefixSelf k x = refl

-- In source Agda, proving all nine triangular leading units suffices
-- to inhabit this record. The exact local SymPy all-depth check is not
-- silently promoted to an inhabitant.
record SelectedPrefixIsometry : Set₁ where
  field
    forward :
      (k : Nat) (x y : Source) →
      PrefixEqual k x y →
      PrefixEqual k (Pivot.pivotRaw x) (Pivot.pivotRaw y)

    backward :
      (k : Nat) (x y : Source) →
      PrefixEqual k (Pivot.pivotRaw x) (Pivot.pivotRaw y) →
      PrefixEqual k x y

-- Separately, retain the original index-depth consumer interface.
record SelectedPrefixTransport : Set₁ where
  field
    originalAgreement : Source → Source → Nat
    depthBound : (x y : Source) → Nat
    reflectsAndPreservesDepth :
      (x y : Source) →
      originalAgreement (Pivot.pivotRaw x) (Pivot.pivotRaw y)
        ≡ originalAgreement x y
