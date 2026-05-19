module DASHI.Physics.Toy.GaugeSummaryBundle where

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (_≤_)

open import DASHI.Physics.PhysicalTheory as PT
import DASHI.Physics.Observable as Obs
import DASHI.Physics.SymmetryQuotient as SQ
open import DASHI.Physics.Toy.GaugeShell as G

record GaugeAsymptoticBundle (n : Nat) (x : G.GaugeState n) : Set where
  field
    defect-step-monotone :
      ∀ k →
      PT.defectSize (G.gaugeTheory n) (G.stepPow n (suc k) x) ≤
      PT.defectSize (G.gaugeTheory n) (G.stepPow n k x)
    defect-bounded :
      ∀ k →
      PT.defectSize (G.gaugeTheory n) (G.stepPow n k x) ≤
      PT.defectSize (G.gaugeTheory n) x
    observable-bounded :
      ∀ k →
      Obs.ObservableTheory.eval (G.gaugeObservableTheory n) G.fieldSupportObs
        (SQ.classOf (G.gaugeQuotiented n) (G.stepPow n k x))
      ≤
      Obs.ObservableTheory.eval (G.gaugeObservableTheory n) G.fieldSupportObs
        (SQ.classOf (G.gaugeQuotiented n) x)

gaugeAsymptoticBundle :
  ∀ n (x : G.GaugeState n) → GaugeAsymptoticBundle n x
gaugeAsymptoticBundle n x =
  record
    { defect-step-monotone = λ k → G.gaugeDefectMonotoneStep n {x = G.stepPow n k x}
    ; defect-bounded = λ k → G.gaugeDefect-stepPow-monotone n k x
    ; observable-bounded = λ k → G.gaugeDefect-stepPow-monotone n k x
    }

record GaugeRecoveredTailBundle (n k : Nat) (x : G.GaugeState n) : Set where
  field
    canonical-class :
      ∀ m →
      PT.recoveredLaw (G.gaugeTheory n) (G.stepPow n k x) →
      SQ.classOf (G.gaugeQuotiented n) (G.stepPow n m (G.stepPow n k x)) ≡
      G.gaugeCanonicalClass n
    observable-collapse :
      ∀ m →
      PT.recoveredLaw (G.gaugeTheory n) (G.stepPow n k x) →
      Obs.ObservableTheory.eval (G.gaugeObservableTheory n) G.fieldSupportObs
        (SQ.classOf (G.gaugeQuotiented n) (G.stepPow n m (G.stepPow n k x)))
      ≡
      Obs.ObservableTheory.eval (G.gaugeObservableTheory n) G.fieldSupportObs
        (G.gaugeCanonicalClass n)

gaugeRecoveredTailBundle :
  ∀ n k (x : G.GaugeState n) → GaugeRecoveredTailBundle n k x
gaugeRecoveredTailBundle n k x =
  record
    { canonical-class = λ m rx → G.gaugeRecovered-stepPow-tail-class n k m x rx
    ; observable-collapse = λ m rx → G.gaugeRecovered-stepPow-tail-observable-collapse n k m x rx
    }
