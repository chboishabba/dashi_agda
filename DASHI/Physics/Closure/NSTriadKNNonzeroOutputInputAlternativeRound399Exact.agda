module DASHI.Physics.Closure.NSTriadKNNonzeroOutputInputAlternativeRound399Exact where

------------------------------------------------------------------------
-- ROUND399 / NONZERO OUTPUT FORCES AT LEAST ONE NONZERO INPUT
--
-- The primitive PhysicalTriadIncidence carrier allows zero modes.  R396 was
-- therefore right to reject a global pair-rate positivity premise.  On the
-- actual R378 fibres, however, the output list is intended to be the canonical
-- nonzero cutoff list.
--
-- This file pays the finite geometry needed by the positivity producer.  If
-- tau lies in the output fibre at a nonzero k and p+q=k, then either p is
-- nonzero or q is nonzero.  The split is executable using the repository's
-- exact Boolean mode equality; no order, viscosity, norm, or PDE estimate is
-- involved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output

data Either (A B : Set) : Set where
  left : A → Either A B
  right : B → Either A B

addZeroZero : Z3.addMode Z3.zeroMode Z3.zeroMode ≡ Z3.zeroMode
addZeroZero = refl

triadOutputZeroIfBothInputsZero :
  (tau : Physical.PhysicalTriadIncidence) →
  Physical.p tau ≡ Z3.zeroMode →
  Physical.q tau ≡ Z3.zeroMode →
  Physical.k tau ≡ Z3.zeroMode
triadOutputZeroIfBothInputsZero tau pZero qZero =
  trans
    (sym (Physical.resonance tau))
    (trans
      (cong (λ p → Z3.addMode p (Physical.q tau)) pZero)
      (trans
        (cong (Z3.addMode Z3.zeroMode) qZero)
        addZeroZero))

triadInputAlternativeFromNonzeroOutput :
  (tau : Physical.PhysicalTriadIncidence) →
  Z3.NonZeroMode (Physical.k tau) →
  Either (Z3.NonZeroMode (Physical.p tau))
         (Z3.NonZeroMode (Physical.q tau))
triadInputAlternativeFromNonzeroOutput tau outputNonzero
  with Output.modeEqual (Physical.p tau) Z3.zeroMode in pDecision
... | true =
  let
    pZero : Physical.p tau ≡ Z3.zeroMode
    pZero = Output.modeEqualSound pDecision

    qNonzero : Z3.NonZeroMode (Physical.q tau)
    qNonzero = record
      { Z3.notZero = λ qZero →
          Z3.notZero outputNonzero
            (triadOutputZeroIfBothInputsZero tau pZero qZero)
      }
  in right qNonzero
... | false =
  let
    pNonzero : Z3.NonZeroMode (Physical.p tau)
    pNonzero = record
      { Z3.notZero = λ pZero →
          Output.falseNotTrue
            (trans (sym pDecision) (Output.modeEqualComplete pZero))
      }
  in left pNonzero

fibreCellInputAlternative :
  (cutoff : Nat) (output : Z3.FourierMode) →
  Z3.NonZeroMode output →
  (tau : Physical.PhysicalTriadIncidence) →
  tau Cube.∈ Output.physicalOutputFiber cutoff output →
  Either (Z3.NonZeroMode (Physical.p tau))
         (Z3.NonZeroMode (Physical.q tau))
fibreCellInputAlternative cutoff output outputNonzero tau member =
  triadInputAlternativeFromNonzeroOutput tau kNonzero
  where
  kNonzero : Z3.NonZeroMode (Physical.k tau)
  kNonzero = record
    { Z3.notZero = λ kZero →
        Z3.notZero outputNonzero
          (trans (sym (Output.physicalOutputFiberSound member)) kZero)
    }

round399NonzeroOutputForcesNonzeroInputAlternative : Bool
round399NonzeroOutputForcesNonzeroInputAlternative = true

round399UsesAnyAnalyticEstimate : Bool
round399UsesAnyAnalyticEstimate = false

round399GlobalPrimitiveIncidenceNonzeroClaimed : Bool
round399GlobalPrimitiveIncidenceNonzeroClaimed = false

round399NonzeroOutputForcesNonzeroInputAlternativeIsTrue :
  round399NonzeroOutputForcesNonzeroInputAlternative ≡ true
round399NonzeroOutputForcesNonzeroInputAlternativeIsTrue = refl
