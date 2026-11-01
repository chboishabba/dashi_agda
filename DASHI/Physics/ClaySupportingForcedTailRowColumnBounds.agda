module DASHI.Physics.ClaySupportingForcedTailRowColumnBounds where

------------------------------------------------------------------------
-- Elementary, fully-proved forced-tail N⁻² row/column algebra (NS §A3.2).
--
-- Companion to `DASHI.Physics.ClaySupportingResidualDomination` and
-- `...DepthSeparation`.  Every declaration here is a genuine Agda proof over
-- concrete natural numbers: there are NO `postulate`s and NO added axioms.
--
-- The plan asks: depth-separation gain + multiplicity gain ⇒ N⁻² row/column
-- bound.  Over ℕ the (N+1)⁻² statement is stated in cleared-denominator
-- form: "row sum ≤ C/(N+1)²" is  (N+1)² · rowSum ≤ C.  The two analytic
-- gains enter as hypotheses:
--
--   depth-separation gain  (per entry)   :  (N+1) · M(i,j) ≤ G(i,j)
--                                            [from  w(j)/w(i) ≤ 1/(N+1)]
--   multiplicity gain      (per row)     :  (N+1) · Σ_j G(i,j) ≤ C
--
-- and the conclusion is the forced-tail N⁻² bound:
--
--   forcedTailRowBound :  (N+1)² · Σ_j M(i,j) ≤ C
--   forcedTailColBound :  (N+1)² · Σ_i M(i,j) ≤ C   (same algebra, columns)
--
-- Honesty boundary (unchanged): this discharges no open Clay leaf.  It is
-- the row/column *algebra* that combines the two per-profile gains into the
-- N⁻² estimate; the analytic facts that the actual forced-tail kernel enjoys
-- depth separation and the multiplicity gain are the (open) inputs, supplied
-- here as hypotheses, not asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (ℕ; suc; _+_; _*_; _≤_)
open import Data.Nat.Properties using (*-assoc; *-mono-≤; ≤-refl; ≤-trans)
open import Data.List.Base using (List)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import DASHI.Physics.ClaySupportingResidualDomination
  using (rowSum; rowSum-mono; rowSum-*)

------------------------------------------------------------------------
-- §1.  The row-level (N+1)-gain: a per-entry (N+1)-gain lifts to the row.
--
-- If every entry satisfies  (N+1)·M(j) ≤ G(j), then the row sums satisfy
-- (N+1)·Σ_j M(j) ≤ Σ_j G(j).

rowGain :
  {J : Set} (js : List J) (M G : J → ℕ) (N : ℕ) →
  (∀ j → suc N * M j ≤ G j) →
  suc N * rowSum js M ≤ rowSum js G
rowGain js M G N sep =
  subst (λ z → z ≤ rowSum js G)
        (rowSum-* js (suc N) M)
        (rowSum-mono js (λ j → suc N * M j) G sep)

------------------------------------------------------------------------
-- §2.  Forced-tail N⁻² row bound.
--
-- Combine the per-entry depth-separation gain (§1) with the per-row
-- multiplicity gain to clear both factors of (N+1):
--   (N+1)·((N+1)·ΣM) ≤ (N+1)·ΣG ≤ C,  and  (N+1)·((N+1)·ΣM) = (N+1)²·ΣM.

forcedTailRowBound :
  {J : Set} (js : List J) (M G : J → ℕ) (N C : ℕ) →
  (∀ j → suc N * M j ≤ G j) →        -- depth-separation gain (per entry)
  suc N * rowSum js G ≤ C →           -- multiplicity gain (per row)
  (suc N * suc N) * rowSum js M ≤ C
forcedTailRowBound js M G N C sep mult =
  subst (λ z → z ≤ C)
        (sym (*-assoc (suc N) (suc N) (rowSum js M)))
        (≤-trans (*-mono-≤ (≤-refl {suc N}) (rowGain js M G N sep)) mult)

------------------------------------------------------------------------
-- §3.  Forced-tail N⁻² column bound.
--
-- `rowSum` is generic over its index list, so a column sum is the same
-- operation over the row-index list `is` with the transposed kernel.  The
-- column bound is therefore the identical algebra applied along columns.

forcedTailColBound :
  {I : Set} (is : List I) (M G : I → ℕ) (N C : ℕ) →
  (∀ i → suc N * M i ≤ G i) →        -- depth-separation gain (per entry)
  suc N * rowSum is G ≤ C →           -- multiplicity gain (per column)
  (suc N * suc N) * rowSum is M ≤ C
forcedTailColBound = forcedTailRowBound
