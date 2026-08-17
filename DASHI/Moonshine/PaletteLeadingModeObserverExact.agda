module DASHI.Moonshine.PaletteLeadingModeObserverExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre, "A Course in Arithmetic", Graduate Texts in
-- Mathematics 7, Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- Fred Diamond and Jerry Shurman, "A First Course in Modular Forms",
-- Graduate Texts in Mathematics 228, Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- ARISTOTLE / HARMONIC CONTEXT
--
-- The later supplied PaletteUniversality development proves that normalized
-- q-series with polynomially bounded coefficients eventually induce the same
-- high-cusp palette ranking because the universal leading q term dominates.
-- It then factors that common mode out to expose residual individuality.
--
-- DASHI CONTRIBUTION
--
-- This file isolates and proves the exact finite observer theorem consumed by
-- that analytic result.  If two fine score families are enclosed in the SAME
-- leading-mode intervals, and those intervals are strictly separated in the
-- declared palette order, then BOTH fine families realize exactly that order.
-- Equality of the coarse leading-mode observer is not promoted to equality of
-- fine states: quotient class plus residual reconstructs the state exactly,
-- and a two-state counterexample proves the coarse observer is non-injective.
--
-- The remaining analytic producer is deliberately visible: derive the common
-- separated intervals from q-series coefficient growth and cusp height.  No
-- numerical height or tail receipt is invented here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong)

------------------------------------------------------------------------
-- Small self-contained order calculus: no opaque comparison receipt.
------------------------------------------------------------------------

≤-trans : ∀ {a b c : Nat} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n second = z≤n
≤-trans (s≤s first) (s≤s second) = s≤s (≤-trans first second)

_<ₙ_ : Nat → Nat → Set
left <ₙ right = suc left ≤ right

≤-step-suc : ∀ {a b : Nat} → a ≤ b → suc a ≤ suc b
≤-step-suc = s≤s

------------------------------------------------------------------------
-- Common leading-mode enclosure and declared palette order.
------------------------------------------------------------------------

record FineScoreEnclosure
    (Point : Set)
    (lower upper : Point → Nat) : Set₁ where
  field
    actual : Point → Nat
    lowerBound : (point : Point) → lower point ≤ actual point
    upperBound : (point : Point) → actual point ≤ upper point

open FineScoreEnclosure public

record StrictPaletteOrder
    (Point : Set)
    (lower upper : Point → Nat) : Set₁ where
  field
    before : Point → Point → Set
    separated :
      ∀ {left right} →
      before left right →
      suc (upper left) ≤ lower right

open StrictPaletteOrder public

fineScoresRespectDeclaredOrder :
  ∀ {Point : Set}
    {lower upper : Point → Nat} →
  (order : StrictPaletteOrder Point lower upper) →
  (fine : FineScoreEnclosure Point lower upper) →
  ∀ {left right} →
  before order left right →
  actual fine left <ₙ actual fine right
fineScoresRespectDeclaredOrder order fine ordering =
  ≤-trans
    (≤-step-suc (upperBound fine _))
    (≤-trans
      (separated order ordering)
      (lowerBound fine _))

record SamePaletteRanking
    {Point : Set}
    {lower upper : Point → Nat}
    (order : StrictPaletteOrder Point lower upper)
    (leftFine rightFine : FineScoreEnclosure Point lower upper) : Set₁ where
  field
    leftRealizes :
      ∀ {left right} →
      before order left right →
      actual leftFine left <ₙ actual leftFine right
    rightRealizes :
      ∀ {left right} →
      before order left right →
      actual rightFine left <ₙ actual rightFine right

open SamePaletteRanking public

commonLeadingIntervalsForceSamePaletteRanking :
  ∀ {Point : Set}
    {lower upper : Point → Nat} →
  (order : StrictPaletteOrder Point lower upper) →
  (leftFine rightFine : FineScoreEnclosure Point lower upper) →
  SamePaletteRanking order leftFine rightFine
commonLeadingIntervalsForceSamePaletteRanking order leftFine rightFine =
  record
    { leftRealizes = fineScoresRespectDeclaredOrder order leftFine
    ; rightRealizes = fineScoresRespectDeclaredOrder order rightFine
    }

------------------------------------------------------------------------
-- Quotient observer and exact residual reconstruction.
------------------------------------------------------------------------

record LeadingResidualState : Set where
  constructor leadingResidual
  field
    leadingMode : Nat
    residualMode : Nat

open LeadingResidualState public

leadingObserver : LeadingResidualState → Nat
leadingObserver = leadingMode

residualObserver : LeadingResidualState → Nat
residualObserver = residualMode

encodeLeadingResidual : LeadingResidualState → Nat × Nat
encodeLeadingResidual state = leadingObserver state , residualObserver state

decodeLeadingResidual : Nat × Nat → LeadingResidualState
decodeLeadingResidual pair = leadingResidual (proj₁ pair) (proj₂ pair)

leadingResidualRoundTrip :
  (state : LeadingResidualState) →
  decodeLeadingResidual (encodeLeadingResidual state) ≡ state
leadingResidualRoundTrip (leadingResidual leading residual) = refl

observerPlusResidualReconstructs :
  (state : LeadingResidualState) →
  decodeLeadingResidual
    (leadingObserver state , residualObserver state)
  ≡ state
observerPlusResidualReconstructs = leadingResidualRoundTrip

coarseState0 : LeadingResidualState
coarseState0 = leadingResidual 1 0

coarseState1 : LeadingResidualState
coarseState1 = leadingResidual 1 1

sameLeadingObservation :
  leadingObserver coarseState0 ≡ leadingObserver coarseState1
sameLeadingObservation = refl

zeroNotOne : zero ≡ suc zero → ⊥
zeroNotOne ()

sameLeadingObservationDoesNotIdentifyFineState :
  coarseState0 ≡ coarseState1 → ⊥
sameLeadingObservationDoesNotIdentifyFineState equality =
  zeroNotOne (cong residualObserver equality)

------------------------------------------------------------------------
-- Boundary: finite observer theorem is exact; analytic cusp domination is the
-- genuine remaining producer from the later source.
------------------------------------------------------------------------

record PaletteObserverBoundary : Set where
  field
    commonIntervalRankingTheorem : Bool
    exactResidualReconstruction : Bool
    coarseObserverNonInjectiveWitness : Bool
    polynomialTailToSeparatedIntervals : Bool
    universalCuspHeightConstructed : Bool

canonicalPaletteObserverBoundary : PaletteObserverBoundary
canonicalPaletteObserverBoundary = record
  { commonIntervalRankingTheorem = true
  ; exactResidualReconstruction = true
  ; coarseObserverNonInjectiveWitness = true
  ; polynomialTailToSeparatedIntervals = false
  ; universalCuspHeightConstructed = false
  }
