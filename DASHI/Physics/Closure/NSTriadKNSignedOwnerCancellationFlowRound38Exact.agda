module DASHI.Physics.Closure.NSTriadKNSignedOwnerCancellationFlowRound38Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Round 37 retained signed owner balances before the final positive tax.  This
-- module proves the first nontrivial cancellation-flow theorem rather than
-- merely introducing another ledger interface.
--
-- Suppose a physically proved edge can move amount tau from a nonnegative raw
-- owner balance L into a nonpositive balance R, with
--
--   0 <= tau <= L,
--   tau <= -R.
--
-- The post-flow balances are
--
--   L' = L - tau,
--   R' = R + tau.
--
-- Their signed sum is exactly conserved, both signs are preserved, and the
-- positive tax drops exactly by tau:
--
--   tax_before = L = (L - tau) + tau = tax_after + tau.
--
-- Each physical edge also names its source and target in the repository's
-- literal nine-owner type.  No arbitrary cross-owner transfer is licensed:
-- every edge admitted to the eventual network must carry a proved physical
-- identity for that specific owner pair.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _-_; -_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; subst₂)

import DASHI.Physics.Closure.NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact as Tax

record AdmissibleTwoOwnerCancellationFlow : Set where
  constructor admissible-two-owner-cancellation-flow
  field
    leftRaw rightRaw transfer : ℚ
    leftRawNonnegative : 0ℚ ≤ leftRaw
    rightRawNonpositive : rightRaw ≤ 0ℚ
    transferNonnegative : 0ℚ ≤ transfer
    transferWithinLeft : transfer ≤ leftRaw
    transferFillsOnlyRightDeficit : transfer ≤ - rightRaw

open AdmissibleTwoOwnerCancellationFlow public

leftAfter rightAfter : AdmissibleTwoOwnerCancellationFlow → ℚ
leftAfter flow = leftRaw flow - transfer flow
rightAfter flow = rightRaw flow + transfer flow

signedTotalBefore signedTotalAfter :
  AdmissibleTwoOwnerCancellationFlow → ℚ
signedTotalBefore flow = leftRaw flow + rightRaw flow
signedTotalAfter flow = leftAfter flow + rightAfter flow

cancellationFlowConservesSignedTotal : ∀ flow →
  signedTotalAfter flow ≡ signedTotalBefore flow
cancellationFlowConservesSignedTotal flow =
  solve
    ( leftRaw flow
    ∷ rightRaw flow
    ∷ transfer flow
    ∷ [])

leftAfterNonnegative : ∀ flow → 0ℚ ≤ leftAfter flow
leftAfterNonnegative flow =
  let
    shifted :
      (- transfer flow) + transfer flow
      ≤ (- transfer flow) + leftRaw flow
    shifted = ℚP.+-monoʳ-≤ (- transfer flow) (transferWithinLeft flow)
  in
  subst₂ _≤_
    (solve (transfer flow ∷ []))
    (solve (leftRaw flow ∷ transfer flow ∷ []))
    shifted

rightAfterNonpositive : ∀ flow → rightAfter flow ≤ 0ℚ
rightAfterNonpositive flow =
  let
    shifted :
      rightRaw flow + transfer flow
      ≤ rightRaw flow + (- rightRaw flow)
    shifted =
      ℚP.+-monoʳ-≤ (rightRaw flow)
        (transferFillsOnlyRightDeficit flow)
  in
  subst
    (λ upper → rightAfter flow ≤ upper)
    (solve (rightRaw flow ∷ []))
    shifted

positiveTaxBefore positiveTaxAfter :
  AdmissibleTwoOwnerCancellationFlow → ℚ
positiveTaxBefore flow = leftRaw flow
positiveTaxAfter flow = leftAfter flow

positiveTaxDecreaseExact : ∀ flow →
  positiveTaxBefore flow
  ≡ positiveTaxAfter flow + transfer flow
positiveTaxDecreaseExact flow =
  solve (leftRaw flow ∷ transfer flow ∷ [])

positiveTaxCannotIncrease : ∀ flow →
  positiveTaxAfter flow ≤ positiveTaxBefore flow
positiveTaxCannotIncrease flow =
  let
    raw :
      positiveTaxAfter flow + 0ℚ
      ≤ positiveTaxAfter flow + transfer flow
    raw =
      ℚP.+-monoʳ-≤ (positiveTaxAfter flow)
        (transferNonnegative flow)
  in
  subst₂ _≤_
    (solve (leftRaw flow ∷ transfer flow ∷ []))
    (solve (leftRaw flow ∷ transfer flow ∷ []))
    raw

record PhysicalCancellationEdge : Set₁ where
  field
    sourceOwner targetOwner : Tax.TaxOwner
    flow : AdmissibleTwoOwnerCancellationFlow
    PhysicalEdgeIdentity : Set
    physicalEdgeIdentity : PhysicalEdgeIdentity

open PhysicalCancellationEdge public

physicalCancellationEdgePreservesSignedTotal :
  (edge : PhysicalCancellationEdge) →
  signedTotalAfter (flow edge) ≡ signedTotalBefore (flow edge)
physicalCancellationEdgePreservesSignedTotal edge =
  cancellationFlowConservesSignedTotal (flow edge)

physicalCancellationEdgeDoesNotIncreaseTax :
  (edge : PhysicalCancellationEdge) →
  positiveTaxAfter (flow edge) ≤ positiveTaxBefore (flow edge)
physicalCancellationEdgeDoesNotIncreaseTax edge =
  positiveTaxCannotIncrease (flow edge)

physicalCancellationEdgeTaxSavingExact :
  (edge : PhysicalCancellationEdge) →
  positiveTaxBefore (flow edge)
  ≡ positiveTaxAfter (flow edge) + transfer (flow edge)
physicalCancellationEdgeTaxSavingExact edge =
  positiveTaxDecreaseExact (flow edge)

signedOwnerCancellationFlowClosed : Bool
signedOwnerCancellationFlowClosed = true

physicalNineOwnerCancellationNetworkConstructed : Bool
physicalNineOwnerCancellationNetworkConstructed = false

signedOwnerCancellationFlowClosedIsTrue :
  signedOwnerCancellationFlowClosed ≡ true
signedOwnerCancellationFlowClosedIsTrue = refl
