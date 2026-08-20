module DASHI.Governance.SelectiveMultiResidualRouting where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
import DASHI.Governance.QuotientDefectResidualRouting as Residual

------------------------------------------------------------------------
-- Selective multi-residual dynamics.
--
-- A coarse/foreground coordinate can be preserved while different hidden
-- residual coordinates are preserved, amplified, suppressed, or erased in
-- different ways.  The semantics of "amplified" and "erased" are supplied by
-- the application; the generic layer merely keeps those coordinates distinct.
------------------------------------------------------------------------

record SelectiveResidualTransform
    (Q : Residual.QuotientReceiptSystem)
    (R : Residual.ResidualFamily Q) : Set₁ where
  field
    transform : Residual.Fine Q → Residual.Fine Q

    foregroundPreserved :
      ∀ x →
      Residual.project Q (transform x) ≡ Residual.project Q x

    HistoricalPreservation :
      Residual.Residual R Residual.historical →
      Residual.Residual R Residual.historical → Set
    CausalPreservation :
      Residual.Residual R Residual.causal →
      Residual.Residual R Residual.causal → Set
    TraumaAmplification :
      Residual.Residual R Residual.trauma →
      Residual.Residual R Residual.trauma → Set
    IdentityErasure :
      Residual.Residual R Residual.identity →
      Residual.Residual R Residual.identity → Set
    AuthorityTransform :
      Residual.Residual R Residual.authority →
      Residual.Residual R Residual.authority → Set
    CounterevidenceTransform :
      Residual.Residual R Residual.counterevidence →
      Residual.Residual R Residual.counterevidence → Set

    historicalPreserved :
      ∀ x →
      HistoricalPreservation
        (Residual.observeResidual R Residual.historical x)
        (Residual.observeResidual R Residual.historical (transform x))

    causalPreserved :
      ∀ x →
      CausalPreservation
        (Residual.observeResidual R Residual.causal x)
        (Residual.observeResidual R Residual.causal (transform x))

    traumaAmplified :
      ∀ x →
      TraumaAmplification
        (Residual.observeResidual R Residual.trauma x)
        (Residual.observeResidual R Residual.trauma (transform x))

    identityErased :
      ∀ x →
      IdentityErasure
        (Residual.observeResidual R Residual.identity x)
        (Residual.observeResidual R Residual.identity (transform x))

    authorityTransformed :
      ∀ x →
      AuthorityTransform
        (Residual.observeResidual R Residual.authority x)
        (Residual.observeResidual R Residual.authority (transform x))

    counterevidenceTransformed :
      ∀ x →
      CounterevidenceTransform
        (Residual.observeResidual R Residual.counterevidence x)
        (Residual.observeResidual R Residual.counterevidence (transform x))

open SelectiveResidualTransform public

------------------------------------------------------------------------
-- This is the typed analogue of a schematic transformation such as
--   F(P,Q_trauma,Q_identity) = (P, amplify Q_trauma, erase Q_identity).
-- It deliberately does not identify "amplification" with any numeric scalar or
-- "erasure" with a particular zero until an application supplies that algebra.
------------------------------------------------------------------------

record TraumaAmplifyIdentityErase
    {Q : Residual.QuotientReceiptSystem}
    {R : Residual.ResidualFamily Q}
    (T : SelectiveResidualTransform Q R) : Set₁ where
  field
    TraumaStrictlyAmplified : Set
    traumaStrictlyAmplified : TraumaStrictlyAmplified
    IdentityActuallyErased : Set
    identityActuallyErased : IdentityActuallyErased

open TraumaAmplifyIdentityErase public

------------------------------------------------------------------------
-- Coarse equality cannot discharge any individual residual-difference witness.
-- These named specialisations make the multi-coordinate law available without
-- collapsing back to one undifferentiated Q.
------------------------------------------------------------------------

historicalDifferenceSurvivesCoarse :
  ∀ {Q R x y} →
  Residual.ResidualDifference {Q} R Residual.historical x y →
  Residual.observeResidual R Residual.historical x ≡
  Residual.observeResidual R Residual.historical y →
  ⊥
historicalDifferenceSurvivesCoarse =
  Residual.coarseEqualityCannotEraseResidualDifference

causalDifferenceSurvivesCoarse :
  ∀ {Q R x y} →
  Residual.ResidualDifference {Q} R Residual.causal x y →
  Residual.observeResidual R Residual.causal x ≡
  Residual.observeResidual R Residual.causal y →
  ⊥
causalDifferenceSurvivesCoarse =
  Residual.coarseEqualityCannotEraseResidualDifference

identityDifferenceSurvivesCoarse :
  ∀ {Q R x y} →
  Residual.ResidualDifference {Q} R Residual.identity x y →
  Residual.observeResidual R Residual.identity x ≡
  Residual.observeResidual R Residual.identity y →
  ⊥
identityDifferenceSurvivesCoarse =
  Residual.coarseEqualityCannotEraseResidualDifference

authorityDifferenceSurvivesCoarse :
  ∀ {Q R x y} →
  Residual.ResidualDifference {Q} R Residual.authority x y →
  Residual.observeResidual R Residual.authority x ≡
  Residual.observeResidual R Residual.authority y →
  ⊥
authorityDifferenceSurvivesCoarse =
  Residual.coarseEqualityCannotEraseResidualDifference

counterevidenceDifferenceSurvivesCoarse :
  ∀ {Q R x y} →
  Residual.ResidualDifference {Q} R Residual.counterevidence x y →
  Residual.observeResidual R Residual.counterevidence x ≡
  Residual.observeResidual R Residual.counterevidence y →
  ⊥
counterevidenceDifferenceSurvivesCoarse =
  Residual.coarseEqualityCannotEraseResidualDifference

traumaDifferenceSurvivesCoarse :
  ∀ {Q R x y} →
  Residual.ResidualDifference {Q} R Residual.trauma x y →
  Residual.observeResidual R Residual.trauma x ≡
  Residual.observeResidual R Residual.trauma y →
  ⊥
traumaDifferenceSurvivesCoarse =
  Residual.coarseEqualityCannotEraseResidualDifference
