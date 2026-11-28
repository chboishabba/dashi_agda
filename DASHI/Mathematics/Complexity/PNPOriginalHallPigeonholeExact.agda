module DASHI.Mathematics.Complexity.PNPOriginalHallPigeonholeExact where

-- Reuse the constructive pigeonhole owner already on master:
-- IbrahimFinitePigeonholeProducerExact uses FinProperties.pigeonhole
-- and a complete finite carrier encoding. Here the domain consists of
-- ORIGINAL required rows; the codomain is their actual neighbour columns.
-- Classical Hall / pigeonhole and Karp incidence attribution retained.
open import DASHI.Core.Prelude
import Data.Fin.Base as Fin
import Data.Fin.Properties as FinProperties
import Data.Nat.Properties as NatProperties
import DASHI.Wikimedia.IbrahimFinitePigeonholeProducerExact as PHP
import DASHI.Wikimedia.IbrahimGeneralFiniteCertificateKernelExact as Carrier
import DASHI.Mathematics.Complexity.Karp21ExactHittingTransposeExact as Karp
open import Data.Product using (proj₁; proj₂)

noFinInjection : ∀ {r c : Nat} → c < r →
  (f : Fin.Fin r → Fin.Fin c) →
  (∀ i j → f i ≡ f j → i ≡ j) → ⊥
noFinInjection {r} {c} excess f injective
  with FinProperties.pigeonhole {m = c} {n = r} excess f
... | i , j , i<j , same =
  NatProperties.<-irrefl (cong Fin.toℕ (injective i j same)) i<j

noCarrierInjection : ∀ {Column : Set} {r : Nat}
  (columns : Carrier.CompleteFiniteCarrier Column) →
  PHP.carrierSize (Carrier.allNodes columns) < r →
  (f : Fin.Fin r → Column) →
  (∀ i j → f i ≡ f j → i ≡ j) → ⊥
noCarrierInjection columns excess f injective =
  noFinInjection excess (λ i → PHP.carrierEncode columns (f i))
    (λ i j same → injective i j
      (PHP.encodedEqualityReflectsOriginal columns same))

-- A required row can choose an original selected variable. Distinct
-- rows must choose distinct variables, and each neighbour column can
-- contain at most one selected variable. A named finite carrier of
-- neighbour columns is enough; no global row/column count is needed.
requiredSubsetNoGo : ∀ {Variable Column : Set} {r : Nat}
  (columns : Carrier.CompleteFiniteCarrier Column) →
  PHP.carrierSize (Carrier.allNodes columns) < r →
  (selected : Variable → Bool) →
  (row : Fin.Fin r → Variable → Bool) →
  (column : ∀ i v → row i v ≡ true → Column) →
  (cover : ∀ i → Σ Variable (λ v → selected v ≡ true × row i v ≡ true)) →
  (rowDisjoint : ∀ i j v → row i v ≡ true → row j v ≡ true → i ≡ j) →
  (columnCapacity : ∀ i j u v (hu : row i u ≡ true) (hv : row j v ≡ true) →
    selected u ≡ true → selected v ≡ true →
    column i u hu ≡ column j v hv → u ≡ v) → ⊥
requiredSubsetNoGo columns excess selected row column cover rowDisjoint capacity =
  noCarrierInjection columns excess
    (λ i → column i (proj₁ (cover i)) (proj₂ (proj₂ (cover i))))
    (λ i j same →
      rowDisjoint i j (proj₁ (cover i))
        (proj₂ (proj₂ (cover i)))
        (trans (cong (row j) (capacity i j (proj₁ (cover i)) (proj₁ (cover j))
          (proj₂ (proj₂ (cover i))) (proj₂ (proj₂ (cover j)))
          (proj₁ (proj₂ (cover i))) (proj₁ (proj₂ (cover j))) same))
          (proj₂ (proj₂ (cover j)))))

-- Attach directly to the EXISTING Karp exact cover witness, not a new
-- Boolean flag that claims a cover. 'column' is a source-derived map
-- into the verified finite neighbour carrier, whose capacity is paid
-- by the original opposite partition constraints.
exactCoverSubsetNoGo : ∀ {Element Variable Column : Set} {r : Nat}
  (columns : Carrier.CompleteFiniteCarrier Column) →
  PHP.carrierSize (Carrier.allNodes columns) < r →
  (contains : Variable → Element → Bool) →
  (selected : Variable → Bool) →
  (rows : Fin.Fin r → Element) →
  (column : ∀ i v → contains v (rows i) ≡ true → Column) →
  Karp.ExactCover contains selected →
  (rowDisjoint : ∀ i j v → contains v (rows i) ≡ true →
    contains v (rows j) ≡ true → i ≡ j) →
  (columnCapacity : ∀ i j u v (hu : contains u (rows i) ≡ true)
    (hv : contains v (rows j) ≡ true) →
    selected u ≡ true → selected v ≡ true →
    column i u hu ≡ column j v hv → u ≡ v) → ⊥
exactCoverSubsetNoGo columns excess contains selected rows column cover disjoint capacity =
  requiredSubsetNoGo columns excess selected (λ i v → contains v (rows i))
    column (λ i → Karp.ExactlyOneIndexed.covered cover (rows i))
    disjoint capacity

-- The carrier of neighbour columns must be actually supplied from the
-- source and checked. A repeated finite orbit by itself says nothing
-- about full-code gain or SAT truth.
