module DASHI.Physics.Closure.NSTriadKNPhysicalCyclicCellRateDefectBidiExact where

------------------------------------------------------------------------
-- PHYSICAL TRIAD CYCLE DOES NOT PRESERVE THE R503 CELL RATE
--
-- R295 proves p/q swap invariance of
--
--   lambda(p,q;k) = rho(p) + rho(q).
--
-- That symmetry is exactly what R294 needs.  It must not be silently promoted
-- to invariance under the three cyclic modal-output legs.  In the physical
-- p+q=k convention, the corresponding zero-sum triad is (p,q,-k), so cycling
-- its three legs gives the input pairs
--
--   (p,q), (q,-k), (-k,p).
--
-- For an even modal rate rho(-m)=rho(m), the three cell rates are therefore
--
--   lambda0 = rho(p)+rho(q)
--   lambda1 = rho(q)+rho(k)
--   lambda2 = rho(k)+rho(p).
--
-- Hence cyclic invariance is not generic.  The exact defects are radial
-- multiplier differences, while the complete cycle obeys
--
--   lambda0 + lambda1 + lambda2
--     = 2 * (rho(p)+rho(q)+rho(k)).
--
-- This is the useful residual coordinate for the R503 same-scale search:
-- failure of cyclic descent does not merely block the quotient; it exposes the
-- multiplier-difference term that a later summed-cancellation estimate may
-- exploit.  No resolvent reciprocal estimate, norm, absolute value, or PDE
-- bound is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinWaleffeAmplitudeTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNCellRateSwapInvariantWeightRound295Exact as R295
import DASHI.Physics.Closure.NSTriadKNModeInverseSquareRealityRound35Exact as R35

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1 + 1

record EvenRate (rho : Z3.FourierMode → ℚ) : Set where
  constructor even-rate
  field
    even : (mode : Z3.FourierMode) →
      rho (Z3.negateMode mode) ≡ rho mode

open EvenRate public

cycle0Rate :
  (rho : Z3.FourierMode → ℚ) →
  Physical.PhysicalTriadIncidence → ℚ
cycle0Rate = R295.cellRate

cycle1RawRate :
  (rho : Z3.FourierMode → ℚ) →
  Physical.PhysicalTriadIncidence → ℚ
cycle1RawRate rho tau =
  rho (Physical.q tau) + rho (Z3.negateMode (Physical.k tau))

cycle2RawRate :
  (rho : Z3.FourierMode → ℚ) →
  Physical.PhysicalTriadIncidence → ℚ
cycle2RawRate rho tau =
  rho (Z3.negateMode (Physical.k tau)) + rho (Physical.p tau)

cycle1Rate :
  (rho : Z3.FourierMode → ℚ) →
  Physical.PhysicalTriadIncidence → ℚ
cycle1Rate rho tau = rho (Physical.q tau) + rho (Physical.k tau)

cycle2Rate :
  (rho : Z3.FourierMode → ℚ) →
  Physical.PhysicalTriadIncidence → ℚ
cycle2Rate rho tau = rho (Physical.k tau) + rho (Physical.p tau)

rawCycle1UsesEvenRate :
  (rho : Z3.FourierMode → ℚ) →
  EvenRate rho →
  (tau : Physical.PhysicalTriadIncidence) →
  cycle1RawRate rho tau ≡ cycle1Rate rho tau
rawCycle1UsesEvenRate rho E tau =
  cong (rho (Physical.q tau) +_)
    (even E (Physical.k tau))

rawCycle2UsesEvenRate :
  (rho : Z3.FourierMode → ℚ) →
  EvenRate rho →
  (tau : Physical.PhysicalTriadIncidence) →
  cycle2RawRate rho tau ≡ cycle2Rate rho tau
rawCycle2UsesEvenRate rho E tau =
  cong (_+ rho (Physical.p tau))
    (even E (Physical.k tau))

-- Division-free defect forms.  These are equivalent to
--   lambda1-lambda0 = rho(k)-rho(p)
-- and
--   lambda2-lambda0 = rho(k)-rho(q),
-- but avoid introducing subtraction into the reusable carrier.
cycle1DefectBalance :
  (rho : Z3.FourierMode → ℚ) →
  (tau : Physical.PhysicalTriadIncidence) →
  cycle1Rate rho tau + rho (Physical.p tau)
  ≡ cycle0Rate rho tau + rho (Physical.k tau)
cycle1DefectBalance rho tau =
  solve
    (rho (Physical.p tau)
      ∷ rho (Physical.q tau)
      ∷ rho (Physical.k tau)
      ∷ [])

cycle2DefectBalance :
  (rho : Z3.FourierMode → ℚ) →
  (tau : Physical.PhysicalTriadIncidence) →
  cycle2Rate rho tau + rho (Physical.q tau)
  ≡ cycle0Rate rho tau + rho (Physical.k tau)
cycle2DefectBalance rho tau =
  solve
    (rho (Physical.p tau)
      ∷ rho (Physical.q tau)
      ∷ rho (Physical.k tau)
      ∷ [])

completeCycleRateBalance :
  (rho : Z3.FourierMode → ℚ) →
  (tau : Physical.PhysicalTriadIncidence) →
  cycle0Rate rho tau + cycle1Rate rho tau + cycle2Rate rho tau
  ≡ two *
      (rho (Physical.p tau)
        + rho (Physical.q tau)
        + rho (Physical.k tau))
completeCycleRateBalance rho tau =
  solve
    (rho (Physical.p tau)
      ∷ rho (Physical.q tau)
      ∷ rho (Physical.k tau)
      ∷ [])

pairCycle0Rate :
  (rho : Z3.FourierMode → ℚ) →
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → ℚ
pairCycle0Rate rho alpha beta =
  cycle0Rate rho alpha + cycle0Rate rho beta

pairCycle1Rate :
  (rho : Z3.FourierMode → ℚ) →
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → ℚ
pairCycle1Rate rho alpha beta =
  cycle1Rate rho alpha + cycle1Rate rho beta

pairCycle2Rate :
  (rho : Z3.FourierMode → ℚ) →
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → ℚ
pairCycle2Rate rho alpha beta =
  cycle2Rate rho alpha + cycle2Rate rho beta

pairCycle1DefectBalance :
  (rho : Z3.FourierMode → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  pairCycle1Rate rho alpha beta
    + rho (Physical.p alpha) + rho (Physical.p beta)
  ≡ pairCycle0Rate rho alpha beta
    + rho (Physical.k alpha) + rho (Physical.k beta)
pairCycle1DefectBalance rho alpha beta =
  solve
    (rho (Physical.p alpha)
      ∷ rho (Physical.q alpha)
      ∷ rho (Physical.k alpha)
      ∷ rho (Physical.p beta)
      ∷ rho (Physical.q beta)
      ∷ rho (Physical.k beta)
      ∷ [])

pairCycle2DefectBalance :
  (rho : Z3.FourierMode → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  pairCycle2Rate rho alpha beta
    + rho (Physical.q alpha) + rho (Physical.q beta)
  ≡ pairCycle0Rate rho alpha beta
    + rho (Physical.k alpha) + rho (Physical.k beta)
pairCycle2DefectBalance rho alpha beta =
  solve
    (rho (Physical.p alpha)
      ∷ rho (Physical.q alpha)
      ∷ rho (Physical.k alpha)
      ∷ rho (Physical.p beta)
      ∷ rho (Physical.q beta)
      ∷ rho (Physical.k beta)
      ∷ [])

completePairCycleRateBalance :
  (rho : Z3.FourierMode → ℚ) →
  (alpha beta : Physical.PhysicalTriadIncidence) →
  pairCycle0Rate rho alpha beta
    + pairCycle1Rate rho alpha beta
    + pairCycle2Rate rho alpha beta
  ≡ two *
      ( rho (Physical.p alpha)
        + rho (Physical.q alpha)
        + rho (Physical.k alpha)
        + rho (Physical.p beta)
        + rho (Physical.q beta)
        + rho (Physical.k beta))
completePairCycleRateBalance rho alpha beta =
  solve
    (rho (Physical.p alpha)
      ∷ rho (Physical.q alpha)
      ∷ rho (Physical.k alpha)
      ∷ rho (Physical.p beta)
      ∷ rho (Physical.q beta)
      ∷ rho (Physical.k beta)
      ∷ [])

physicalDecayRateEven :
  (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F) →
  EvenRate (R94.physicalDecayRate physicalSystem)
physicalDecayRateEven physicalSystem =
  even-rate λ mode →
    cong
      (C3.multiply F (Field30.viscosity physicalSystem))
      (R35.normSquaredEven
        (Field30.physicalEmbedding physicalSystem)
        (Field30.physicalInverseSquare physicalSystem)
        mode)

------------------------------------------------------------------------
-- Search boundary.
------------------------------------------------------------------------

pQSwapRateInvariant : Bool
pQSwapRateInvariant = true

cyclicRateInvariantGenerically : Bool
cyclicRateInvariantGenerically = false

cyclicDefectIsRadialMultiplierDifference : Bool
cyclicDefectIsRadialMultiplierDifference = true

completeThreeLegRateBalanceClosed : Bool
completeThreeLegRateBalanceClosed = true

physicalViscousRateEvenFromExistingGeometry : Bool
physicalViscousRateEvenFromExistingGeometry = true

r503ResolventCyclicInvariantProved : Bool
r503ResolventCyclicInvariantProved = false

r503CyclicDefectEstimateClosed : Bool
r503CyclicDefectEstimateClosed = false

clayPromotion : Bool
clayPromotion = false

cyclicRateInvariantGenericallyIsFalse :
  cyclicRateInvariantGenerically ≡ false
cyclicRateInvariantGenericallyIsFalse = refl

completeThreeLegRateBalanceClosedIsTrue :
  completeThreeLegRateBalanceClosed ≡ true
completeThreeLegRateBalanceClosedIsTrue = refl

r503ResolventCyclicInvariantProvedIsFalse :
  r503ResolventCyclicInvariantProved ≡ false
r503ResolventCyclicInvariantProvedIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
