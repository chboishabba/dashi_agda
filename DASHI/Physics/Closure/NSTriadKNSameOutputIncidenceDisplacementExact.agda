module DASHI.Physics.Closure.NSTriadKNSameOutputIncidenceDisplacementExact where

------------------------------------------------------------------------
-- PERIODIC B / SAME-OUTPUT PHYSICAL INCIDENCE DISPLACEMENT
--
-- For two literal physical triads over one output k,
--
--   alpha : p_a + q_a = k
--   beta  : p_b + q_b = k,
--
-- define the ordered displacement
--
--   y(alpha,beta) = p_b - p_a.
--
-- Then exactly on Z^3
--
--   p_b = p_a + y,
--   q_b = q_a - y.
--
-- This is the physical opposite-shift coordinate needed by the R571
-- second-moment route.  Moreover, if alpha and beta are distinct proof-bearing
-- incidences over the same output, y is nonzero.  Hence R571's nonzero
-- displacement hypotheses are legitimate on the actual off-diagonal carrier;
-- they are not legitimate on the artificially completed diagonal square.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; _+_; _-_; _*_)
import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR
open import Relation.Binary.PropositionalEquality using (_≢_; cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNIntegerFourierModeAddExact as Add
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiberPermutationRound35Exact as Unique

module RingZ = NR IntRS.ring

modeSubtract : Z3.FourierMode → Z3.FourierMode → Z3.FourierMode
modeSubtract left right =
  Z3.addMode left (Z3.negateMode right)

incidenceDisplacement :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence →
  Z3.FourierMode
incidenceDisplacement alpha beta =
  modeSubtract (Physical.p beta) (Physical.p alpha)

------------------------------------------------------------------------
-- Pure additive identities.
------------------------------------------------------------------------

leftPlusDifference :
  (left right : Z3.FourierMode) →
  Z3.addMode left (modeSubtract right left) ≡ right
leftPlusDifference
    (Z3.mode lx ly lz)
    (Z3.mode rx ry rz) =
  Add.modeExt
    (RingZ.solve 2
      (λ l r → (l + (r - l) , r))
      refl lx rx)
    (RingZ.solve 2
      (λ l r → (l + (r - l) , r))
      refl ly ry)
    (RingZ.solve 2
      (λ l r → (l + (r - l) , r))
      refl lz rz)

rightMinusDifferenceToSumMinusRight :
  (pa qa pb : Z3.FourierMode) →
  Z3.addMode qa
    (Z3.negateMode (modeSubtract pb pa))
  ≡ modeSubtract (Z3.addMode pa qa) pb
rightMinusDifferenceToSumMinusRight
    (Z3.mode pax pay paz)
    (Z3.mode qax qay qaz)
    (Z3.mode pbx pby pbz) =
  Add.modeExt
    (RingZ.solve 3
      (λ pa qa pb → (qa - (pb - pa) , (pa + qa) - pb))
      refl pax qax pbx)
    (RingZ.solve 3
      (λ pa qa pb → (qa - (pb - pa) , (pa + qa) - pb))
      refl pay qay pby)
    (RingZ.solve 3
      (λ pa qa pb → (qa - (pb - pa) , (pa + qa) - pb))
      refl paz qaz pbz)

sumMinusLeft :
  (left right : Z3.FourierMode) →
  modeSubtract (Z3.addMode left right) left ≡ right
sumMinusLeft
    (Z3.mode lx ly lz)
    (Z3.mode rx ry rz) =
  Add.modeExt
    (RingZ.solve 2
      (λ l r → (((l + r) - l) , r))
      refl lx rx)
    (RingZ.solve 2
      (λ l r → (((l + r) - l) , r))
      refl ly ry)
    (RingZ.solve 2
      (λ l r → (((l + r) - l) , r))
      refl lz rz)

------------------------------------------------------------------------
-- Same-output triads are literal opposite shifts.
------------------------------------------------------------------------

sameOutputInputSums :
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  Z3.addMode (Physical.p alpha) (Physical.q alpha)
  ≡ Z3.addMode (Physical.p beta) (Physical.q beta)
sameOutputInputSums alpha beta sameOutput =
  trans
    (Physical.resonance alpha)
    (trans sameOutput (sym (Physical.resonance beta)))

betaPIsAlphaPPlusDisplacement :
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Z3.addMode
    (Physical.p alpha)
    (incidenceDisplacement alpha beta)
  ≡ Physical.p beta
betaPIsAlphaPPlusDisplacement alpha beta =
  leftPlusDifference (Physical.p alpha) (Physical.p beta)

betaQIsAlphaQMinusDisplacement :
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  Z3.addMode
    (Physical.q alpha)
    (Z3.negateMode (incidenceDisplacement alpha beta))
  ≡ Physical.q beta
betaQIsAlphaQMinusDisplacement alpha beta sameOutput =
  let
    sums = sameOutputInputSums alpha beta sameOutput
    first =
      rightMinusDifferenceToSumMinusRight
        (Physical.p alpha)
        (Physical.q alpha)
        (Physical.p beta)
    middle =
      cong
        (λ total → modeSubtract total (Physical.p beta))
        sums
    last =
      sumMinusLeft
        (Physical.p beta)
        (Physical.q beta)
  in
  trans first (trans middle last)

------------------------------------------------------------------------
-- Zero displacement on one output means the incidences are identical.
------------------------------------------------------------------------

negateZero : Z3.negateMode Z3.zeroMode ≡ Z3.zeroMode
negateZero = refl

zeroDisplacementImpliesSameP :
  (alpha beta : Physical.PhysicalTriadIncidence) →
  incidenceDisplacement alpha beta ≡ Z3.zeroMode →
  Physical.p alpha ≡ Physical.p beta
zeroDisplacementImpliesSameP alpha beta displacementZero =
  trans
    (sym (Add.addZeroRight (Physical.p alpha)))
    (trans
      (cong
        (Z3.addMode (Physical.p alpha))
        (sym displacementZero))
      (betaPIsAlphaPPlusDisplacement alpha beta))

zeroDisplacementImpliesSameQ :
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  incidenceDisplacement alpha beta ≡ Z3.zeroMode →
  Physical.q alpha ≡ Physical.q beta
zeroDisplacementImpliesSameQ alpha beta sameOutput displacementZero =
  let
    shifted =
      betaQIsAlphaQMinusDisplacement alpha beta sameOutput
    negZero :
      Z3.negateMode (incidenceDisplacement alpha beta)
      ≡ Z3.zeroMode
    negZero =
      trans (cong Z3.negateMode displacementZero) negateZero
  in
  trans
    (sym (Add.addZeroRight (Physical.q alpha)))
    (trans
      (cong
        (Z3.addMode (Physical.q alpha))
        (sym negZero))
      shifted)

zeroDisplacementImpliesSameIncidence :
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  incidenceDisplacement alpha beta ≡ Z3.zeroMode →
  alpha ≡ beta
zeroDisplacementImpliesSameIncidence alpha beta sameOutput displacementZero =
  Unique.physicalIncidenceExtPQ
    alpha beta
    (zeroDisplacementImpliesSameP alpha beta displacementZero)
    (zeroDisplacementImpliesSameQ
      alpha beta sameOutput displacementZero)

distinctSameOutputHasNonzeroDisplacement :
  (alpha beta : Physical.PhysicalTriadIncidence) →
  Physical.k alpha ≡ Physical.k beta →
  alpha ≢ beta →
  Z3.NonZeroMode (incidenceDisplacement alpha beta)
distinctSameOutputHasNonzeroDisplacement
    alpha beta sameOutput distinct = record
  { Z3.NonZeroMode.notZero =
      λ displacementZero →
        distinct
          (zeroDisplacementImpliesSameIncidence
            alpha beta sameOutput displacementZero)
  }

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

sameOutputIncidenceOppositeShiftClosed : Bool
sameOutputIncidenceOppositeShiftClosed = true

distinctOffDiagonalDisplacementNonzeroClosed : Bool
distinctOffDiagonalDisplacementNonzeroClosed = true

diagonalEligibleForNonzeroR571SecondMoment : Bool
diagonalEligibleForNonzeroR571SecondMoment = false

sameOutputIncidenceOppositeShiftClosedIsTrue :
  sameOutputIncidenceOppositeShiftClosed ≡ true
sameOutputIncidenceOppositeShiftClosedIsTrue = refl

distinctOffDiagonalDisplacementNonzeroClosedIsTrue :
  distinctOffDiagonalDisplacementNonzeroClosed ≡ true
distinctOffDiagonalDisplacementNonzeroClosedIsTrue = refl

diagonalEligibleForNonzeroR571SecondMomentIsFalse :
  diagonalEligibleForNonzeroR571SecondMoment ≡ false
diagonalEligibleForNonzeroR571SecondMomentIsFalse = refl
