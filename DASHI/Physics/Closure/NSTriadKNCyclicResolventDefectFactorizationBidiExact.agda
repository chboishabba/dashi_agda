module DASHI.Physics.Closure.NSTriadKNCyclicResolventDefectFactorizationBidiExact where

------------------------------------------------------------------------
-- CYCLIC RESOLVENT DEFECT = RESOLVENT PRODUCT x RATE DEFECT
--
-- The preceding cyclic-rate owner shows that the R503 denominator is not
-- invariant under the three modal-output legs.  On positive denominators the
-- existing safe reciprocal has the exact inverse law, so the failure of
-- invariance is itself structured:
--
--   inv(b) - inv(a) = inv(b) * inv(a) * (a - b).
--
-- Consequently any cyclic R503 weight defect factors through the already-
-- exposed radial multiplier difference.  This is the correct pre-estimate
-- normal form: preserve sign and the two positive resolvent factors, then
-- decide whether the rate defect cancels/sums/gains on the physical carrier.
--
-- No absolute value, norm, reciprocal majorant, shell count, or PDE estimate
-- is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; Positive; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal
import DASHI.Physics.Closure.NSTriadKNPhysicalCyclicCellRateDefectBidiExact as Cycle
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3

inv : ℚ → ℚ
inv = Reciprocal.safeRationalReciprocal

reciprocalDifferenceFactorization :
  (a b : ℚ) →
  Positive a → Positive b →
  inv b - inv a ≡ inv b * inv a * (a - b)
reciprocalDifferenceFactorization a b aPositive bPositive =
  let
    ia = inv a
    ib = inv b
    invA : ia * a ≡ 1
    invA = Reciprocal.safeRationalReciprocalTimesPositive a aPositive
    invB : ib * b ≡ 1
    invB = Reciprocal.safeRationalReciprocalTimesPositive b bPositive

    expanded :
      ib - ia ≡ ib * (ia * a) - (ib * b) * ia
    expanded = cong₂ _-_ (cong₂ _*_ refl (sym invA))
      (cong₂ _*_ (sym invB) refl)
  in
  trans expanded (solve (ia ∷ ib ∷ a ∷ b ∷ []))

pairWeight0 :
  (rho : Z3.FourierMode → ℚ) →
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → ℚ
pairWeight0 rho alpha beta =
  inv (Cycle.pairCycle0Rate rho alpha beta)

pairWeight1 :
  (rho : Z3.FourierMode → ℚ) →
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → ℚ
pairWeight1 rho alpha beta =
  inv (Cycle.pairCycle1Rate rho alpha beta)

pairWeight2 :
  (rho : Z3.FourierMode → ℚ) →
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → ℚ
pairWeight2 rho alpha beta =
  inv (Cycle.pairCycle2Rate rho alpha beta)

cycle1WeightDefectFactorization :
  (rho : Z3.FourierMode → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Positive (Cycle.pairCycle0Rate rho alpha beta) →
  Positive (Cycle.pairCycle1Rate rho alpha beta) →
  pairWeight1 rho alpha beta - pairWeight0 rho alpha beta
  ≡ pairWeight1 rho alpha beta * pairWeight0 rho alpha beta
      * (Cycle.pairCycle0Rate rho alpha beta
        - Cycle.pairCycle1Rate rho alpha beta)
cycle1WeightDefectFactorization rho alpha beta p0 p1 =
  reciprocalDifferenceFactorization
    (Cycle.pairCycle0Rate rho alpha beta)
    (Cycle.pairCycle1Rate rho alpha beta)
    p0 p1

cycle2WeightDefectFactorization :
  (rho : Z3.FourierMode → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Positive (Cycle.pairCycle0Rate rho alpha beta) →
  Positive (Cycle.pairCycle2Rate rho alpha beta) →
  pairWeight2 rho alpha beta - pairWeight0 rho alpha beta
  ≡ pairWeight2 rho alpha beta * pairWeight0 rho alpha beta
      * (Cycle.pairCycle0Rate rho alpha beta
        - Cycle.pairCycle2Rate rho alpha beta)
cycle2WeightDefectFactorization rho alpha beta p0 p2 =
  reciprocalDifferenceFactorization
    (Cycle.pairCycle0Rate rho alpha beta)
    (Cycle.pairCycle2Rate rho alpha beta)
    p0 p2

-- Expanded numerator forms.  These make the radial defect visible directly:
-- for cycle1 the original-minus-cycled denominator is
--
--   rho(p_alpha)+rho(p_beta) - rho(k_alpha)-rho(k_beta),
--
-- and cycle2 has the analogous q-defect.
cycle1PairRateDefectExpanded :
  (rho : Z3.FourierMode → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Cycle.pairCycle0Rate rho alpha beta
    - Cycle.pairCycle1Rate rho alpha beta
  ≡
  (rho (Physical.p alpha) + rho (Physical.p beta))
    - (rho (Physical.k alpha) + rho (Physical.k beta))
cycle1PairRateDefectExpanded rho alpha beta =
  solve
    (rho (Physical.p alpha)
      ∷ rho (Physical.q alpha)
      ∷ rho (Physical.k alpha)
      ∷ rho (Physical.p beta)
      ∷ rho (Physical.q beta)
      ∷ rho (Physical.k beta)
      ∷ [])

cycle2PairRateDefectExpanded :
  (rho : Z3.FourierMode → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Cycle.pairCycle0Rate rho alpha beta
    - Cycle.pairCycle2Rate rho alpha beta
  ≡
  (rho (Physical.q alpha) + rho (Physical.q beta))
    - (rho (Physical.k alpha) + rho (Physical.k beta))
cycle2PairRateDefectExpanded rho alpha beta =
  solve
    (rho (Physical.p alpha)
      ∷ rho (Physical.q alpha)
      ∷ rho (Physical.k alpha)
      ∷ rho (Physical.p beta)
      ∷ rho (Physical.q beta)
      ∷ rho (Physical.k beta)
      ∷ [])

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

cyclicResolventInvariantGenerically : Bool
cyclicResolventInvariantGenerically = false

cyclicResolventDefectFactorsThroughRateDefect : Bool
cyclicResolventDefectFactorsThroughRateDefect = true

cyclicWeightDefectAbsoluteValuedHere : Bool
cyclicWeightDefectAbsoluteValuedHere = false

cyclicWeightDefectAnalyticallyPaid : Bool
cyclicWeightDefectAnalyticallyPaid = false

r503OrderedOrientedBudgetClosed : Bool
r503OrderedOrientedBudgetClosed = false

clayPromotion : Bool
clayPromotion = false

cyclicResolventInvariantGenericallyIsFalse :
  cyclicResolventInvariantGenerically ≡ false
cyclicResolventInvariantGenericallyIsFalse = refl

cyclicResolventDefectFactorsThroughRateDefectIsTrue :
  cyclicResolventDefectFactorsThroughRateDefect ≡ true
cyclicResolventDefectFactorsThroughRateDefectIsTrue = refl

cyclicWeightDefectAbsoluteValuedHereIsFalse :
  cyclicWeightDefectAbsoluteValuedHere ≡ false
cyclicWeightDefectAbsoluteValuedHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
