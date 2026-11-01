{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayVoyagerCovariantWilsonCoarseFineBidiExact where

-- Source-specific bridge contract: the OLD coarse/fine/fibre theorems,
-- actual CompactLieLatticeGauge Wilson holonomies, CMP119 C3 physical field
-- pullback and BalabanWilsonTransferBlocking OS pullbacks are independent
-- owners. This module does NOT replace any of their mathematical results.
--
-- It exposes the exact missing commuting square on one selected
-- continuum-directed gauge/Wilson carrier:
--
--   Fine ----gauge----> Fine
--    |                    |
--   block                block
--    v                    v
--   Coarse --gauge----> Coarse
--
-- and the corresponding *same observable* Wilson square.
--
-- If the chosen coarse Wilson observable is gauge invariant, both squares
-- give the fine Wilson gauge invariance on the ACTUAL chosen fine carrier.
-- Importantly: no arbitrary jFine observer, binary/ternary fibre, Z2
-- graph twist, abstract C3, 19683 count or toy J trace automatically
-- supplies either required physical equality.
--
-- This is a conditional theorem compiler, NOT an unconditional analytic YM
-- blocking/infinite-volume/OS physical existence theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record SelectedWilsonCoarseFine
    (Fine Coarse Gauge Scalar : Set) : Set₁ where
  field
    block : Fine → Coarse
    gaugeOnFine : Gauge → Fine → Fine
    gaugeOnCoarse : Gauge → Coarse → Coarse
    wilsonFine : Fine → Scalar
    wilsonCoarse : Coarse → Scalar

    blockGaugeCovariance : ∀ gauge fine →
      block (gaugeOnFine gauge fine)
      ≡ gaugeOnCoarse gauge (block fine)

    sameSelectedWilsonAfterBlocking : ∀ fine →
      wilsonFine fine ≡ wilsonCoarse (block fine)

    coarseWilsonGaugeInvariant : ∀ gauge coarse →
      wilsonCoarse (gaugeOnCoarse gauge coarse)
      ≡ wilsonCoarse coarse

open SelectedWilsonCoarseFine public

selectedFineWilsonGaugeInvariant :
  ∀ {Fine Coarse Gauge Scalar}
    (selected : SelectedWilsonCoarseFine Fine Coarse Gauge Scalar)
    gauge fine →
  wilsonFine selected (gaugeOnFine selected gauge fine)
  ≡ wilsonFine selected fine
selectedFineWilsonGaugeInvariant selected gauge fine =
  trans
    (sameSelectedWilsonAfterBlocking selected
      (gaugeOnFine selected gauge fine))
    (trans
      (cong (wilsonCoarse selected)
        (blockGaugeCovariance selected gauge fine))
      (trans
        (coarseWilsonGaugeInvariant selected gauge (block selected fine))
        (sym (sameSelectedWilsonAfterBlocking selected fine))))

-- The same abstract statement works when Gauge is a selected spatial-C3
-- transporter, provided the *actual* gaugeOnFine and gaugeOnCoarse are the
-- required physical C3 actions. This reuse does not identify a spatial
-- C3 permutation with local non-Abelian gauge transformations.

record SelectedWilsonOSBlock
    (Fine Coarse Gauge Scalar : Set)
    (selected : SelectedWilsonCoarseFine Fine Coarse Gauge Scalar)
    (Positive : Scalar → Set) : Set₁ where
  field
    fineOSForm : Fine → Scalar
    coarseOSForm : Coarse → Scalar

    coarseOSPullback : ∀ coarse →
      coarseOSForm coarse
      ≡ fineOSForm (liftObservable coarse)
      where
        postulate-placeholder : Set
        postulate-placeholder = Scalar

    -- Must be replaced by concrete existing ReflectionPositiveBlocking
    -- where the lift maps coarse OBSERVABLES to fine OBSERVABLES.
    -- This record deliberately has no constructor here.

-- The actual OS-positive blocking theorem remains the already-owned
-- BalabanWilsonTransferBlockingExact, not this typed gauge/Wilson square.
