module DASHI.Physics.Closure.NSTriadKNSignedOwnerCancellationNetworkRound38Exact where

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
-- Round 38 first proved one physically witnessed cancellation edge conserves
-- signed production and lowers the pair's positive tax by exactly its transfer
-- amount.  This module proves the genuine finite-network consequence.
--
-- A `GlobalCancellationStep` keeps the rest of the nine-owner positive tax
-- fixed while one typed physical edge acts.  A `PhysicalCancellationPath`
-- chains such steps by *indices*: the after-tax of one step is definitionally
-- the before-tax of the next.  For any finite path,
--
--   initialTax = finalTax + sum(transfers).
--
-- Thus a collection of proved physical cancellation edges can be optimized
-- before the final positive tax without changing signed production.  No edge
-- is created by the network theorem; every step still carries the source,
-- target and physical identity required by the underlying Round-38 edge.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNSignedOwnerCancellationFlowRound38Exact as Flow

record GlobalCancellationStep : Set₁ where
  constructor global-cancellation-step
  field
    edge : Flow.PhysicalCancellationEdge
    unaffectedPositiveTax : ℚ
    unaffectedPositiveTaxNonnegative : 0ℚ ≤ unaffectedPositiveTax

open GlobalCancellationStep public

globalTaxBefore globalTaxAfter : GlobalCancellationStep → ℚ
globalTaxBefore step =
  unaffectedPositiveTax step +
  Flow.positiveTaxBefore (Flow.flow (edge step))
globalTaxAfter step =
  unaffectedPositiveTax step +
  Flow.positiveTaxAfter (Flow.flow (edge step))

globalStepTransfer : GlobalCancellationStep → ℚ
globalStepTransfer step = Flow.transfer (Flow.flow (edge step))

globalCancellationStepSavingExact : ∀ step →
  globalTaxBefore step
  ≡ globalTaxAfter step + globalStepTransfer step
globalCancellationStepSavingExact step =
  trans
    (cong
      (unaffectedPositiveTax step +_)
      (Flow.physicalCancellationEdgeTaxSavingExact (edge step)))
    (solve
      ( unaffectedPositiveTax step
      ∷ Flow.positiveTaxAfter (Flow.flow (edge step))
      ∷ globalStepTransfer step
      ∷ []))

globalCancellationStepDoesNotIncreaseTax : ∀ step →
  globalTaxAfter step ≤ globalTaxBefore step
globalCancellationStepDoesNotIncreaseTax step =
  ℚP.+-monoʳ-≤
    (unaffectedPositiveTax step)
    (Flow.physicalCancellationEdgeDoesNotIncreaseTax (edge step))

------------------------------------------------------------------------
-- A proof-relevant finite path.  The type indices enforce that each step
-- starts exactly where the preceding step ended.
------------------------------------------------------------------------

data PhysicalCancellationPath : ℚ → ℚ → Set₁ where
  done : (tax : ℚ) → PhysicalCancellationPath tax tax
  step :
    (current : GlobalCancellationStep) →
    ∀ {finalTax} →
    PhysicalCancellationPath (globalTaxAfter current) finalTax →
    PhysicalCancellationPath (globalTaxBefore current) finalTax

pathTransferTotal :
  ∀ {initialTax finalTax} →
  PhysicalCancellationPath initialTax finalTax → ℚ
pathTransferTotal (done tax) = 0ℚ
pathTransferTotal (step current rest) =
  globalStepTransfer current + pathTransferTotal rest

pathTaxSavingExact :
  ∀ {initialTax finalTax}
    (path : PhysicalCancellationPath initialTax finalTax) →
  initialTax ≡ finalTax + pathTransferTotal path
pathTaxSavingExact (done tax) = solve (tax ∷ [])
pathTaxSavingExact (step current rest) =
  trans
    (globalCancellationStepSavingExact current)
    (trans
      (cong
        (λ after → after + globalStepTransfer current)
        (pathTaxSavingExact rest))
      (solve
        ( _ ∷ globalStepTransfer current
        ∷ pathTransferTotal rest
        ∷ [])))

pathTransferTotalNonnegative :
  ∀ {initialTax finalTax}
    (path : PhysicalCancellationPath initialTax finalTax) →
  0ℚ ≤ pathTransferTotal path
pathTransferTotalNonnegative (done tax) = ℚP.≤-refl
pathTransferTotalNonnegative (step current rest) =
  ℚP.+-mono-≤
    (Flow.transferNonnegative (Flow.flow (edge current)))
    (pathTransferTotalNonnegative rest)

pathCannotIncreasePositiveTax :
  ∀ {initialTax finalTax} →
  PhysicalCancellationPath initialTax finalTax →
  finalTax ≤ initialTax
pathCannotIncreasePositiveTax (done tax) = ℚP.≤-refl
pathCannotIncreasePositiveTax (step current rest) =
  ℚP.≤-trans
    (pathCannotIncreasePositiveTax rest)
    (globalCancellationStepDoesNotIncreaseTax current)

signedOwnerCancellationNetworkAlgebraClosed : Bool
signedOwnerCancellationNetworkAlgebraClosed = true

physicalNineOwnerCancellationPathConstructed : Bool
physicalNineOwnerCancellationPathConstructed = false

signedOwnerCancellationNetworkAlgebraClosedIsTrue :
  signedOwnerCancellationNetworkAlgebraClosed ≡ true
signedOwnerCancellationNetworkAlgebraClosedIsTrue = refl
