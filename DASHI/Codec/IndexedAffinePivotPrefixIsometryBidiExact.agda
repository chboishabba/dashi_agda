module DASHI.Codec.IndexedAffinePivotPrefixIsometryBidiExact where

-- H07: the actual nine selected digits, and prefix equality at
-- EVERY depth. This replaces the previous 0/1-only witness interface.
-- Source-written: the source-specific F3 algebra proof remains OPEN;
-- SymPy symbolically confirms triangular units + involution and checks
-- the complete 5832-carrier partition certificate. No Agda run.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
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


-- The actual lower-triangular pivot depends only on earlier selected
-- digits. Extract exactly those equalities; no enumeration of pairs.
headEqual : ∀ {a b : Trit} {as bs : List Trit} →
  (a ∷ as) ≡ (b ∷ bs) → a ≡ b
headEqual refl = refl

tailEqual : ∀ {a b : Trit} {as bs : List Trit} →
  (a ∷ as) ≡ (b ∷ bs) → as ≡ bs
tailEqual refl = refl

slopeInjective : {s t : M.Sign} →
  Stable.rawSlope s ≡ Stable.rawSlope t → s ≡ t
slopeInjective {M.negative} {M.negative} _ = refl
slopeInjective {M.positive} {M.positive} _ = refl
slopeInjective {M.negative} {M.positive} ()
slopeInjective {M.positive} {M.negative} ()

prefixForward : (k : Nat) (x y : Source) →
  PrefixEqual k x y →
  PrefixEqual k (Pivot.pivotRaw x) (Pivot.pivotRaw y)
prefixForward zero x y eq = refl
prefixForward (suc (zero))
  (Stable.stableBlocks (M.triple a b c) (M.triple s t u) (M.triple d e f))
  (Stable.stableBlocks (M.triple a′ b′ c′) (M.triple s′ t′ u′) (M.triple d′ e′ f′)) eq
  rewrite slopeInjective (headEqual (eq)) = refl

prefixForward (suc (suc (zero)))
  (Stable.stableBlocks (M.triple a b c) (M.triple s t u) (M.triple d e f))
  (Stable.stableBlocks (M.triple a′ b′ c′) (M.triple s′ t′ u′) (M.triple d′ e′ f′)) eq
  rewrite slopeInjective (headEqual (eq))
        | slopeInjective (headEqual (tailEqual (eq))) = refl

prefixForward (suc (suc (suc (zero))))
  (Stable.stableBlocks (M.triple a b c) (M.triple s t u) (M.triple d e f))
  (Stable.stableBlocks (M.triple a′ b′ c′) (M.triple s′ t′ u′) (M.triple d′ e′ f′)) eq
  rewrite slopeInjective (headEqual (eq))
        | slopeInjective (headEqual (tailEqual (eq)))
        | slopeInjective (headEqual (tailEqual (tailEqual (eq)))) = refl

prefixForward (suc (suc (suc (suc (zero)))))
  (Stable.stableBlocks (M.triple a b c) (M.triple s t u) (M.triple d e f))
  (Stable.stableBlocks (M.triple a′ b′ c′) (M.triple s′ t′ u′) (M.triple d′ e′ f′)) eq
  rewrite slopeInjective (headEqual (eq))
        | slopeInjective (headEqual (tailEqual (eq)))
        | slopeInjective (headEqual (tailEqual (tailEqual (eq))))
        | headEqual (tailEqual (tailEqual (tailEqual (eq)))) = refl

prefixForward (suc (suc (suc (suc (suc (zero))))))
  (Stable.stableBlocks (M.triple a b c) (M.triple s t u) (M.triple d e f))
  (Stable.stableBlocks (M.triple a′ b′ c′) (M.triple s′ t′ u′) (M.triple d′ e′ f′)) eq
  rewrite slopeInjective (headEqual (eq))
        | slopeInjective (headEqual (tailEqual (eq)))
        | slopeInjective (headEqual (tailEqual (tailEqual (eq))))
        | headEqual (tailEqual (tailEqual (tailEqual (eq))))
        | headEqual (tailEqual (tailEqual (tailEqual (tailEqual (eq))))) = refl

prefixForward (suc (suc (suc (suc (suc (suc (zero)))))))
  (Stable.stableBlocks (M.triple a b c) (M.triple s t u) (M.triple d e f))
  (Stable.stableBlocks (M.triple a′ b′ c′) (M.triple s′ t′ u′) (M.triple d′ e′ f′)) eq
  rewrite slopeInjective (headEqual (eq))
        | slopeInjective (headEqual (tailEqual (eq)))
        | slopeInjective (headEqual (tailEqual (tailEqual (eq))))
        | headEqual (tailEqual (tailEqual (tailEqual (eq))))
        | headEqual (tailEqual (tailEqual (tailEqual (tailEqual (eq)))))
        | headEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (eq)))))) = refl

prefixForward (suc (suc (suc (suc (suc (suc (suc (zero))))))))
  (Stable.stableBlocks (M.triple a b c) (M.triple s t u) (M.triple d e f))
  (Stable.stableBlocks (M.triple a′ b′ c′) (M.triple s′ t′ u′) (M.triple d′ e′ f′)) eq
  rewrite slopeInjective (headEqual (eq))
        | slopeInjective (headEqual (tailEqual (eq)))
        | slopeInjective (headEqual (tailEqual (tailEqual (eq))))
        | headEqual (tailEqual (tailEqual (tailEqual (eq))))
        | headEqual (tailEqual (tailEqual (tailEqual (tailEqual (eq)))))
        | headEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (eq))))))
        | headEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (eq))))))) = refl

prefixForward (suc (suc (suc (suc (suc (suc (suc (suc (zero)))))))))
  (Stable.stableBlocks (M.triple a b c) (M.triple s t u) (M.triple d e f))
  (Stable.stableBlocks (M.triple a′ b′ c′) (M.triple s′ t′ u′) (M.triple d′ e′ f′)) eq
  rewrite slopeInjective (headEqual (eq))
        | slopeInjective (headEqual (tailEqual (eq)))
        | slopeInjective (headEqual (tailEqual (tailEqual (eq))))
        | headEqual (tailEqual (tailEqual (tailEqual (eq))))
        | headEqual (tailEqual (tailEqual (tailEqual (tailEqual (eq)))))
        | headEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (eq))))))
        | headEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (eq)))))))
        | headEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (eq)))))))) = refl

prefixForward (suc (suc (suc (suc (suc (suc (suc (suc (suc (k))))))))))
  (Stable.stableBlocks (M.triple a b c) (M.triple s t u) (M.triple d e f))
  (Stable.stableBlocks (M.triple a′ b′ c′) (M.triple s′ t′ u′) (M.triple d′ e′ f′)) eq
  rewrite slopeInjective (headEqual (eq))
        | slopeInjective (headEqual (tailEqual (eq)))
        | slopeInjective (headEqual (tailEqual (tailEqual (eq))))
        | headEqual (tailEqual (tailEqual (tailEqual (eq))))
        | headEqual (tailEqual (tailEqual (tailEqual (tailEqual (eq)))))
        | headEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (eq))))))
        | headEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (eq)))))))
        | headEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (eq))))))))
        | headEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (tailEqual (eq))))))))) = refl

prefixBackward : (k : Nat) (x y : Source) →
  PrefixEqual k (Pivot.pivotRaw x) (Pivot.pivotRaw y) →
  PrefixEqual k x y
prefixBackward k x y eq =
  trans (sym (cong (λ z → prefix k (selectedDigits z))
                    (Pivot.onRaw Pivot.selectedPivotInvolution x)))
    (trans (prefixForward k (Pivot.pivotRaw x) (Pivot.pivotRaw y) eq)
           (cong (λ z → prefix k (selectedDigits z))
                 (Pivot.onRaw Pivot.selectedPivotInvolution y)))

selectedPrefixIsometry : SelectedPrefixIsometry
selectedPrefixIsometry = record
  { forward = prefixForward ; backward = prefixBackward }

-- The original recharted cube already consumes selectedPivotInvolution.
-- All prefix depths (including k >= 9) are covered by the clauses above.
-- Source-written; no kernel acceptance asserted.
