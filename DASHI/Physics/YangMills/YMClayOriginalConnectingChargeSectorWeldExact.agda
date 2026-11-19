module DASHI.Physics.YangMills.YMClayOriginalConnectingChargeSectorWeldExact where

-- Attachment to the original CMP116 connecting charge sum.
-- No alternate cluster family or effective action. Sector classification
-- is supplied by the actual C2/Step V support dictionary.
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as Q
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst; sym; cong)
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as T

data Sector : Set where
  small large mixed : Sector

smallCharge : ∀ {A : Set} → (A → Sector) → (A → ℚ) → List A → ℚ
smallCharge tag w [] = 0ℚ
smallCharge tag w (a ∷ as) with tag a
... | small = w a + smallCharge tag w as
... | large = smallCharge tag w as
... | mixed = smallCharge tag w as

largeCharge : ∀ {A : Set} → (A → Sector) → (A → ℚ) → List A → ℚ
largeCharge tag w [] = 0ℚ
largeCharge tag w (a ∷ as) with tag a
... | small = largeCharge tag w as
... | large = w a + largeCharge tag w as
... | mixed = largeCharge tag w as

mixedCharge : ∀ {A : Set} → (A → Sector) → (A → ℚ) → List A → ℚ
mixedCharge tag w [] = 0ℚ
mixedCharge tag w (a ∷ as) with tag a
... | small = mixedCharge tag w as
... | large = mixedCharge tag w as
... | mixed = w a + mixedCharge tag w as

sectorChargeSum : ∀ {A : Set} (tag : A → Sector) (w : A → ℚ) (as : List A) →
  T.sumℚ (T.map w as) ≡ (smallCharge tag w as + largeCharge tag w as) + mixedCharge tag w as
sectorChargeSum tag w [] = Ring.solve-∀
sectorChargeSum tag w (a ∷ as) with tag a
... | small rewrite sectorChargeSum tag w as =
  Ring.solve-∀ (w a) (smallCharge tag w as) (largeCharge tag w as) (mixedCharge tag w as)
... | large rewrite sectorChargeSum tag w as =
  Ring.solve-∀ (w a) (smallCharge tag w as) (largeCharge tag w as) (mixedCharge tag w as)
... | mixed rewrite sectorChargeSum tag w as =
  Ring.solve-∀ (w a) (smallCharge tag w as) (largeCharge tag w as) (mixedCharge tag w as)

sectorChargeBelowShell : ∀ {A : Set} (tag : A → Sector) (w : A → ℚ) (as : List A)
  (s l m shell : ℚ) →
  smallCharge tag w as ≤ s →
  largeCharge tag w as ≤ l →
  mixedCharge tag w as ≤ m →
  (s + l) + m ≤ shell →
  T.sumℚ (T.map w as) ≤ shell
sectorChargeBelowShell tag w as s l m shell ps pl pm budget =
  subst (λ v → v ≤ shell) (sym (sectorChargeSum tag w as))
    (Q.≤-trans (Q.+-mono-≤ (Q.+-mono-≤ ps pl) pm) budget)

-- Instantiate as with BalabanLiteralTwoWilsonCMP116ConnectingTailExact.connectingClusters
-- and w with BalabanLiteralTwoWilsonMarkedPolymerExpansionExact.shellCharge.
-- The physical tag and three sector estimates are NOT constructed here.

------------------------------------------------------------------------
-- Native support classifier and direct attachment to literal CMP116.
------------------------------------------------------------------------
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as P
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonMarkedPolymerExpansionExact as M
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonCMP116ConnectingTailExact as C
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell

extendSector : Bool → Sector → Sector
extendSector false small = small
extendSector false large = mixed
extendSector false mixed = mixed
extendSector true small = mixed
extendSector true large = large
extendSector true mixed = mixed

-- Empty support is small by convention, not a large-field witness.
classifyNativeSupport : ∀ {n} → (P.PeriodicBlock n → Bool) →
  P.PeriodicPolymer n → Sector
classifyNativeSupport bad [] = small
classifyNativeSupport bad (b ∷ []) with bad b
... | true = large
... | false = small
classifyNativeSupport bad (b ∷ c ∷ cs) =
  extendSector (bad b) (classifyNativeSupport bad (c ∷ cs))

-- Literal existing charge and cluster list, no alternative sum.
nativeConnectingSectorBudget :
  ∀ {Observable Source Polymer Cluster Volume}
    {family : M.TwoWilsonSourceParameterizedKP Observable Source Polymer Cluster Volume}
    {differentiable : M.DifferentiableTwoWilsonKP family}
    (charge : M.TwoWilsonCMP116ClusterCharge differentiable)
    (cutoff : Nat) (left right : Observable)
    (tag : Cluster → Sector) (s l m bound : ℚ) →
    smallCharge tag (M.shellCharge charge cutoff left right)
      (C.connectingClusters family cutoff left right) ≤ s →
    largeCharge tag (M.shellCharge charge cutoff left right)
      (C.connectingClusters family cutoff left right) ≤ l →
    mixedCharge tag (M.shellCharge charge cutoff left right)
      (C.connectingClusters family cutoff left right) ≤ m →
    (s + l) + m ≤ bound →
    T.sumℚ (T.map (M.shellCharge charge cutoff left right)
      (C.connectingClusters family cutoff left right)) ≤ bound
nativeConnectingSectorBudget {family = family} charge cutoff left right tag =
  sectorChargeBelowShell tag (M.shellCharge charge cutoff left right)
    (C.connectingClusters family cutoff left right)

-- The prior theorem is the exact type of the charge-sum field when
-- bound is instantiated with Shell.rootedShell on the original payment.
-- No claim that the supplied bad mask is already the physical RG mask.

------------------------------------------------------------------------
-- Consume the existing proof-bearing literal Wilson bad-block predicate.
------------------------------------------------------------------------
import DASHI.Physics.YangMills.BalabanClayGate4LiteralWilsonLargeFieldPredicateExact as LF
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (yes; no)

literalBadMask : ∀ {Scale Configuration Gauge Block Plaquette}
  (dataSet : LF.LiteralWilsonLargeFieldData Scale Configuration Gauge Block Plaquette) →
  Scale → Configuration → Block → Bool
literalBadMask dataSet scale config block
  with LF.largeFieldBlockDecidable dataSet scale config block
... | yes _ = true
... | no _ = false

literalBadMaskGaugeInvariant : ∀ {Scale Configuration Gauge Block Plaquette}
  (dataSet : LF.LiteralWilsonLargeFieldData Scale Configuration Gauge Block Plaquette)
  gauge scale config block →
  literalBadMask dataSet scale (LF.transform dataSet gauge config) block
    ≡ literalBadMask dataSet scale config block
literalBadMaskGaugeInvariant dataSet gauge scale config block
  with LF.largeFieldBlockDecidable dataSet scale config block
     | LF.largeFieldBlockDecidable dataSet scale (LF.transform dataSet gauge config) block
... | yes p | yes q = refl
... | no p | no q = refl
... | yes p | no q with q (LF.largeFieldBlockGaugeForward dataSet gauge scale config block p)
...   | ()
literalBadMaskGaugeInvariant dataSet gauge scale config block
  | no p | yes q with p (LF.largeFieldBlockGaugeBackward dataSet gauge scale config block q)
...   | ()

literalClusterSector : ∀ {n Scale Configuration Gauge Plaquette Cluster}
  (dataSet : LF.LiteralWilsonLargeFieldData Scale Configuration Gauge (P.PeriodicBlock n) Plaquette) →
  Scale → Configuration → (Cluster → P.PeriodicPolymer n) → Cluster → Sector
literalClusterSector dataSet scale config support cluster =
  classifyNativeSupport (literalBadMask dataSet scale config) (support cluster)

-- IMPORTANT: a fixed configuration classifier does not classify an integrated
-- activity unless the selected activity is restricted to that sector or its
-- integration domain has been decomposed accordingly. The supplied support
-- map and the activity/domain identity remain genuine source obligations.
