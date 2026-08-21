module DASHI.Cognition.PNF.StratifiedFibrewiseSupportLocalityExact where

open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Streaming / fibrewise / progressive / stratified execution law.
--
-- Runtime motivation (SensibLaw close diagnostics, 2026-08-21): close ordinal
-- is not itself a semantic state variable.  Genuine closes through ordinal
-- 4096 varied with local adjacency/anaphor activity but did not exhibit simple
-- monotone growth with accumulated document state.  The correct locality law
-- is therefore not "every close has constant cost".  It is:
--
--   global close/work must factor through the support of the closing fibre at
--   its active semantic stratum.
--
-- Unrelated accumulated state may be arbitrarily larger.  If it does not alter
-- the active local support projection, it cannot alter either the semantic close
-- result or the charged work under a certified support-local implementation.
--
-- This is internal DASHI/ITIR mathematics; no external DOI is asserted.
------------------------------------------------------------------------

sym :
  ∀ {A : Set} {left right : A} →
  left ≡ right →
  right ≡ left
sym refl = refl

trans :
  ∀ {A : Set} {left middle right : A} →
  left ≡ middle →
  middle ≡ right →
  left ≡ right
trans refl refl = refl

cong :
  ∀ {A B : Set} (f : A → B) {left right : A} →
  left ≡ right →
  f left ≡ f right
cong f refl = refl

record StratifiedFibrewiseSupportLocality
  (Stratum Fibre GlobalState Support CloseResult WorkReceipt : Set)
  : Set₁ where
  field
    activeStratum : Fibre → Stratum

    -- Projection of the whole accumulated state onto exactly the support that
    -- may affect this fibre at its active stratum.
    supportProjection :
      Stratum → Fibre → GlobalState → Support

    -- Local semantic and physical kernels consume only the projected support.
    closeFromSupport :
      Stratum → Fibre → Support → CloseResult
    workFromSupport :
      Stratum → Fibre → Support → WorkReceipt

    -- Existing/global APIs may still be phrased over GlobalState, but a
    -- certified implementation must factor through supportProjection exactly.
    closeFromGlobal : Fibre → GlobalState → CloseResult
    workFromGlobal : Fibre → GlobalState → WorkReceipt

    closeFactorsThroughSupport :
      ∀ fibre global →
      closeFromGlobal fibre global
        ≡ closeFromSupport
            (activeStratum fibre)
            fibre
            (supportProjection (activeStratum fibre) fibre global)

    workFactorsThroughSupport :
      ∀ fibre global →
      workFromGlobal fibre global
        ≡ workFromSupport
            (activeStratum fibre)
            fibre
            (supportProjection (activeStratum fibre) fibre global)

open StratifiedFibrewiseSupportLocality public

-- The semantic close cannot distinguish two accumulated states once their
-- active-stratum support fibres are equal.
sameSupportSameClose :
  ∀ {Stratum Fibre GlobalState Support CloseResult WorkReceipt : Set}
    (system : StratifiedFibrewiseSupportLocality
      Stratum Fibre GlobalState Support CloseResult WorkReceipt)
    (fibre : Fibre)
    (left right : GlobalState) →
  supportProjection system (activeStratum system fibre) fibre left
    ≡ supportProjection system (activeStratum system fibre) fibre right →
  closeFromGlobal system fibre left
    ≡ closeFromGlobal system fibre right
sameSupportSameClose system fibre left right supportEqual =
  trans
    (closeFactorsThroughSupport system fibre left)
    (trans
      (cong
        (closeFromSupport system (activeStratum system fibre) fibre)
        supportEqual)
      (sym (closeFactorsThroughSupport system fibre right)))

-- Physical work obeys the same locality boundary.  This is the exact
-- anti-amplification theorem: unrelated accumulated state cannot increase work
-- unless it changes the support visible at the active stratum.
sameSupportSameWork :
  ∀ {Stratum Fibre GlobalState Support CloseResult WorkReceipt : Set}
    (system : StratifiedFibrewiseSupportLocality
      Stratum Fibre GlobalState Support CloseResult WorkReceipt)
    (fibre : Fibre)
    (left right : GlobalState) →
  supportProjection system (activeStratum system fibre) fibre left
    ≡ supportProjection system (activeStratum system fibre) fibre right →
  workFromGlobal system fibre left
    ≡ workFromGlobal system fibre right
sameSupportSameWork system fibre left right supportEqual =
  trans
    (workFactorsThroughSupport system fibre left)
    (trans
      (cong
        (workFromSupport system (activeStratum system fibre) fibre)
        supportEqual)
      (sym (workFactorsThroughSupport system fibre right)))

------------------------------------------------------------------------
-- Unrelated accumulation.
--
-- A runtime may know a more concrete relation saying that one global state is
-- an extension of another by state irrelevant to a particular fibre/stratum.
-- We do not equate extension with support preservation by definition: the
-- certificate must prove that boundary explicitly.
------------------------------------------------------------------------

record SupportPreservingAccumulation
  {Stratum Fibre GlobalState Support CloseResult WorkReceipt : Set}
  (system : StratifiedFibrewiseSupportLocality
    Stratum Fibre GlobalState Support CloseResult WorkReceipt)
  (Extension : GlobalState → GlobalState → Set)
  : Set₁ where
  field
    accumulationPreservesSupport :
      ∀ fibre before after →
      Extension before after →
      supportProjection system (activeStratum system fibre) fibre before
        ≡ supportProjection system (activeStratum system fibre) fibre after

open SupportPreservingAccumulation public

unrelatedAccumulationCannotChangeClose :
  ∀ {Stratum Fibre GlobalState Support CloseResult WorkReceipt : Set}
    {system : StratifiedFibrewiseSupportLocality
      Stratum Fibre GlobalState Support CloseResult WorkReceipt}
    {Extension : GlobalState → GlobalState → Set}
    (certificate : SupportPreservingAccumulation system Extension)
    (fibre : Fibre)
    (before after : GlobalState) →
  Extension before after →
  closeFromGlobal system fibre before
    ≡ closeFromGlobal system fibre after
unrelatedAccumulationCannotChangeClose certificate fibre before after extension =
  sameSupportSameClose
    _ fibre before after
    (accumulationPreservesSupport certificate fibre before after extension)

unrelatedAccumulationCannotIncreaseWork :
  ∀ {Stratum Fibre GlobalState Support CloseResult WorkReceipt : Set}
    {system : StratifiedFibrewiseSupportLocality
      Stratum Fibre GlobalState Support CloseResult WorkReceipt}
    {Extension : GlobalState → GlobalState → Set}
    (certificate : SupportPreservingAccumulation system Extension)
    (fibre : Fibre)
    (before after : GlobalState) →
  Extension before after →
  workFromGlobal system fibre before
    ≡ workFromGlobal system fibre after
unrelatedAccumulationCannotIncreaseWork certificate fibre before after extension =
  sameSupportSameWork
    _ fibre before after
    (accumulationPreservesSupport certificate fibre before after extension)

------------------------------------------------------------------------
-- Progressive stratum promotion.
--
-- Promotion is a separate operation from local closure.  A local close emits a
-- residual/delta owned by its stratum; a later declared promotion consumes that
-- residual.  This prevents a higher-stratum projection from being smuggled into
-- every low-stratum close as an implicit side effect.
------------------------------------------------------------------------

record ProgressiveStratumPromotion
  (Stratum Fibre Support Residual Promoted : Set)
  : Set₁ where
  field
    residualFromSupport : Stratum → Fibre → Support → Residual
    promoteResidual : Stratum → Residual → Promoted

open ProgressiveStratumPromotion public

-- Exact helper showing that equal local support gives equal emitted residual;
-- higher-stratum promotion therefore also sees the same input.
sameSupportSameResidual :
  ∀ {Stratum Fibre Support Residual Promoted : Set}
    (promotion : ProgressiveStratumPromotion
      Stratum Fibre Support Residual Promoted)
    (stratum : Stratum)
    (fibre : Fibre)
    (left right : Support) →
  left ≡ right →
  residualFromSupport promotion stratum fibre left
    ≡ residualFromSupport promotion stratum fibre right
sameSupportSameResidual promotion stratum fibre left right supportEqual =
  cong (residualFromSupport promotion stratum fibre) supportEqual
