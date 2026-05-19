module DASHI.Physics.Toy.GaugeShell where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (_≤_; _+_)
open import Data.Nat.Properties as NatP using (≤-refl; ≤-trans)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import DASHI.Algebra.Trit using (Trit; zer)
open import DASHI.Physics.PhysicalTheory as PT
open import DASHI.Physics.Refinement as Ref
import DASHI.Physics.SymmetryQuotient as SQ
open import DASHI.Physics.Observable as Obs
open import DASHI.Physics.LocalWitness as LW
import DASHI.Physics.Toy.ScalarContinuum as SC

record GaugeState (n : Nat) : Set where
  constructor mkGauge
  field
    gaugeOrigin : Trit
    fieldMode   : SC.Carrier n

open GaugeState public

gaugeVacuum : (n : Nat) → Trit → GaugeState n
gaugeVacuum n g = mkGauge g (SC.vacuum n)

gaugeStep : (n : Nat) → GaugeState n → GaugeState n
gaugeStep n (mkGauge g f) = mkGauge g (SC.scalarStep n f)

scalarStepPow : ∀ n → Nat → SC.Carrier n → SC.Carrier n
scalarStepPow n zero f = f
scalarStepPow n (suc k) f = SC.scalarStep n (scalarStepPow n k f)

scalarDefect-stepPow-monotone :
  ∀ n k (f : SC.Carrier n) →
  SC.countNonZero (scalarStepPow n k f) ≤ SC.countNonZero f
scalarDefect-stepPow-monotone n zero f = ≤-refl
scalarDefect-stepPow-monotone n (suc k) f =
  NatP.≤-trans
    (SC.scalarDefectMonotone n {scalarStepPow n k f})
    (scalarDefect-stepPow-monotone n k f)

gaugeTheory : (n : Nat) → PT.PhysicalTheory lzero
gaugeTheory n =
  record
    { State = GaugeState n
    ; step = gaugeStep n
    ; Defect = λ _ → ⊤
    ; defectSize = λ x → SC.countNonZero (fieldMode x)
    ; Inv = λ _ → ⊤
    ; inv-step = λ _ → tt
    ; defect-monotone = λ {x} _ → SC.scalarDefectMonotone n {fieldMode x}
    ; fixed = λ x → gaugeStep n x ≡ x
    ; recoveredLaw = λ x → fieldMode x ≡ SC.vacuum n
    }

gaugeApproxRefinement :
  (n : Nat) → Ref.ApproxRefinementStep (gaugeTheory n) (gaugeTheory (suc n))
gaugeApproxRefinement n =
  record
    { project = λ x → mkGauge (gaugeOrigin x) (SC.dropLast (fieldMode x))
    ; embed = λ x → mkGauge (gaugeOrigin x) (SC.appendZero (fieldMode x))
    ; approxEq₀ = λ x y → gaugeOrigin x ≡ gaugeOrigin y × SC.TailApprox (fieldMode x) (fieldMode y)
    ; commute-project≈ = λ x → refl , SC.dropLast-relaxSym≈-with zer (fieldMode x)
    }

gaugeTower : Ref.RefinementTower lzero
gaugeTower =
  record
    { TheoryAt = gaugeTheory
    ; refine = gaugeApproxRefinement
    }

gaugeAct : ∀ {n : Nat} → Trit → GaugeState n → GaugeState n
gaugeAct shift (mkGauge g f) = mkGauge shift f

gaugeStep-equivariant :
  ∀ n shift x →
  gaugeStep n (gaugeAct shift x) ≡ gaugeAct shift (gaugeStep n x)
gaugeStep-equivariant n shift (mkGauge g f) = refl

gaugeSymmetric : (n : Nat) → SQ.SymmetricTheory lzero
gaugeSymmetric n =
  record
    { base = gaugeTheory n
    ; Group = Trit
    ; act = gaugeAct
    ; step-equivariant = gaugeStep-equivariant n
    ; inv-invariant = λ _ _ _ → tt
    }

gaugePhysEq : (n : Nat) → SQ.PhysicalEquivalence (gaugeSymmetric n)
gaugePhysEq n =
  record
    { _≈phys_ = λ x y → fieldMode x ≡ fieldMode y
    ; orbit→phys = λ shift x → refl
    ; step-respects = λ eq → cong (SC.scalarStep n) eq
    }

gaugeQuotiented : (n : Nat) → SQ.QuotientedTheory lzero
gaugeQuotiented n =
  record
    { sym = gaugeSymmetric n
    ; physEq = gaugePhysEq n
    ; PhysState = SC.Carrier n
    ; repr = λ f → mkGauge zer f
    ; classOf = fieldMode
    ; class-sound = λ x y eq → eq
    }

data GaugeObservable : Set where
  fieldSupportObs : GaugeObservable

gaugeObservableTheory : (n : Nat) → Obs.ObservableTheory (gaugeQuotiented n)
gaugeObservableTheory n =
  record
    { Observable = GaugeObservable
    ; Value = λ where fieldSupportObs → Nat
    ; eval = λ where fieldSupportObs f → SC.countNonZero f
    }

gaugeObservableInvariant :
  (n : Nat) → Obs.SymmetryInvariantObservables (gaugeQuotiented n) (gaugeObservableTheory n)
gaugeObservableInvariant n =
  record
    { eval-well-defined = λ where
        fieldSupportObs x y eq → cong SC.countNonZero eq
    }

data GaugeOperator : Set where
  gaugeHold gaugeEvolve : GaugeOperator

gaugeOperatorWitness : (n : Nat) → LW.OperatorWitness (gaugeTheory n)
gaugeOperatorWitness n =
  record
    { Operator = GaugeOperator
    ; apply = λ where
        gaugeHold x → x
        gaugeEvolve x → gaugeStep n x
    ; unitOp = gaugeHold
    ; compose = λ where
        gaugeHold op₂ → op₂
        gaugeEvolve gaugeHold → gaugeEvolve
        gaugeEvolve gaugeEvolve → gaugeEvolve
    ; preservesInv = λ _ _ → tt
    }

gaugeScalingWitness : LW.ScalingWitness gaugeTower
gaugeScalingWitness =
  record
    { coarse-defect≤fine = λ n x → SC.countNonZero-dropLast (fieldMode x)
    }

gaugeLocalWitness : (n : Nat) → LW.LocalTheoryWitness (gaugeTheory n) gaugeTower (gaugeQuotiented n) (gaugeObservableTheory n)
gaugeLocalWitness n =
  record
    { operators = gaugeOperatorWitness n
    ; scaling = gaugeScalingWitness
    ; obsInvariant = gaugeObservableInvariant n
    }

gaugeFixed⇒recovered :
  ∀ n {x : GaugeState n} →
  PT.fixed (gaugeTheory n) x →
  PT.recoveredLaw (gaugeTheory n) x
gaugeFixed⇒recovered n {x} fx =
  SC.fixed⇒recovered n {x = fieldMode x} (cong fieldMode fx)

gaugeRecovered-refines :
  ∀ n {x : GaugeState (suc n)} →
  PT.recoveredLaw (gaugeTheory (suc n)) x →
  PT.recoveredLaw (gaugeTheory n)
    (Ref.ApproxRefinementStep.project (gaugeApproxRefinement n) x)
gaugeRecovered-refines n {x} rx =
  SC.recovered-refines n {x = fieldMode x} rx

gaugeRecovered-class :
  ∀ n {x : GaugeState n} →
  PT.recoveredLaw (gaugeTheory n) x →
  SQ.classOf (gaugeQuotiented n) x ≡ SC.vacuum n
gaugeRecovered-class n {x} rx rewrite rx = refl

gaugeRecovered-same-class :
  ∀ n {x y : GaugeState n} →
  PT.recoveredLaw (gaugeTheory n) x →
  PT.recoveredLaw (gaugeTheory n) y →
  SQ.classOf (gaugeQuotiented n) x ≡ SQ.classOf (gaugeQuotiented n) y
gaugeRecovered-same-class n {x} {y} rx ry
  rewrite gaugeRecovered-class n {x = x} rx
        | gaugeRecovered-class n {x = y} ry
  = refl

gaugeCoarseStepApprox :
  ∀ n (x : GaugeState (suc n)) →
  Ref.ApproxRefinementStep.approxEq₀ (gaugeApproxRefinement n)
    (Ref.ApproxRefinementStep.project (gaugeApproxRefinement n) (gaugeStep (suc n) x))
    (gaugeStep n (Ref.ApproxRefinementStep.project (gaugeApproxRefinement n) x))
gaugeCoarseStepApprox n (mkGauge g f) =
  refl , SC.dropLast-relaxSym≈-with zer f

gaugeCoarseStepDefect≤FineStep :
  ∀ n (x : GaugeState (suc n)) →
  PT.defectSize (gaugeTheory n)
    (Ref.ApproxRefinementStep.project (gaugeApproxRefinement n) (gaugeStep (suc n) x))
  ≤
  PT.defectSize (gaugeTheory (suc n)) (gaugeStep (suc n) x)
gaugeCoarseStepDefect≤FineStep n (mkGauge g f) =
  SC.countNonZero-dropLast (SC.scalarStep (suc n) f)

gaugeCoarseStepObservableMonotone :
  ∀ n (x : GaugeState (suc n)) →
  Obs.ObservableTheory.eval (gaugeObservableTheory n) fieldSupportObs
    (SQ.classOf (gaugeQuotiented n)
      (Ref.ApproxRefinementStep.project (gaugeApproxRefinement n) (gaugeStep (suc n) x)))
  ≤
  Obs.ObservableTheory.eval (gaugeObservableTheory (suc n)) fieldSupportObs
    (SQ.classOf (gaugeQuotiented (suc n)) (gaugeStep (suc n) x))
gaugeCoarseStepObservableMonotone n (mkGauge g f)
  rewrite SC.countTrue-supportVec (SC.scalarStep (suc n) f)
        | SC.countTrue-supportVec (SC.dropLast (SC.scalarStep (suc n) f))
  = SC.countNonZero-dropLast (SC.scalarStep (suc n) f)

gaugeObservable-stable :
  ∀ n (g : Trit) →
  Obs.ObservableTheory.eval (gaugeObservableTheory n) fieldSupportObs (SQ.classOf (gaugeQuotiented n) (gaugeVacuum n g))
  ≡
  Obs.ObservableTheory.eval (gaugeObservableTheory (suc n)) fieldSupportObs (SQ.classOf (gaugeQuotiented (suc n)) (gaugeVacuum (suc n) g))
gaugeObservable-stable n g = refl

gaugeRefinement-stable-recovery :
  ∀ n (g : Trit) →
  PT.recoveredLaw (gaugeTheory n)
    (Ref.ApproxRefinementStep.project (gaugeApproxRefinement n)
      (PT.step (gaugeTheory (suc n))
        (Ref.ApproxRefinementStep.embed (gaugeApproxRefinement n) (gaugeVacuum n g))))
gaugeRefinement-stable-recovery n g = SC.refinement-stable-recovery n

gaugeCoarseClassOnVacuum :
  ∀ n (g : Trit) →
  SQ.classOf (gaugeQuotiented n)
    (Ref.ApproxRefinementStep.project (gaugeApproxRefinement n)
      (Ref.ApproxRefinementStep.embed (gaugeApproxRefinement n) (gaugeVacuum n g)))
  ≡ SC.vacuum n
gaugeCoarseClassOnVacuum n g = SC.dropLast-appendZeroVec (SC.vacuum n)

stepPow : ∀ n → Nat → GaugeState n → GaugeState n
stepPow n k (mkGauge g f) = mkGauge g (scalarStepPow n k f)

gaugeDefectMonotoneStep :
  ∀ n {x : GaugeState n} →
  PT.defectSize (gaugeTheory n) (gaugeStep n x) ≤
  PT.defectSize (gaugeTheory n) x
gaugeDefectMonotoneStep n {mkGauge g f} = SC.scalarDefectMonotone n {f}

gaugeDefect-stepPow-monotone :
  ∀ n k (x : GaugeState n) →
  PT.defectSize (gaugeTheory n) (stepPow n k x) ≤
  PT.defectSize (gaugeTheory n) x
gaugeDefect-stepPow-monotone n k (mkGauge g f) =
  scalarDefect-stepPow-monotone n k f

coarsePow : ∀ k n → GaugeState (k + n) → GaugeState n
coarsePow zero n x = x
coarsePow (suc k) n x =
  coarsePow k n (Ref.ApproxRefinementStep.project (gaugeApproxRefinement (k + n)) x)

gaugeDefect-coarsePow-monotone :
  ∀ k n (x : GaugeState (k + n)) →
  PT.defectSize (gaugeTheory n) (coarsePow k n x) ≤
  PT.defectSize (gaugeTheory (k + n)) x
gaugeDefect-coarsePow-monotone zero n x = ≤-refl
gaugeDefect-coarsePow-monotone (suc k) n x =
  NatP.≤-trans
    (gaugeDefect-coarsePow-monotone k n (Ref.ApproxRefinementStep.project (gaugeApproxRefinement (k + n)) x))
    (SC.countNonZero-dropLast (fieldMode x))

gaugeObservable-coarsePow-monotone :
  ∀ k n (x : GaugeState (k + n)) →
  Obs.ObservableTheory.eval (gaugeObservableTheory n) fieldSupportObs (SQ.classOf (gaugeQuotiented n) (coarsePow k n x))
  ≤
  Obs.ObservableTheory.eval (gaugeObservableTheory (k + n)) fieldSupportObs (SQ.classOf (gaugeQuotiented (k + n)) x)
gaugeObservable-coarsePow-monotone k n x =
  gaugeDefect-coarsePow-monotone k n x

gaugeCanonicalClass : (n : Nat) → SC.Carrier n
gaugeCanonicalClass n = SC.vacuum n

gaugeRecovered-stepPow-class :
  ∀ n k (x : GaugeState n) →
  PT.recoveredLaw (gaugeTheory n) (stepPow n k x) →
  SQ.classOf (gaugeQuotiented n) (stepPow n k x) ≡ gaugeCanonicalClass n
gaugeRecovered-stepPow-class n k x rx =
  gaugeRecovered-class n {x = stepPow n k x} rx

gaugeRecovered-stepPow-observable-collapse :
  ∀ n k (x : GaugeState n) →
  PT.recoveredLaw (gaugeTheory n) (stepPow n k x) →
  Obs.ObservableTheory.eval (gaugeObservableTheory n) fieldSupportObs
    (SQ.classOf (gaugeQuotiented n) (stepPow n k x))
  ≡
  Obs.ObservableTheory.eval (gaugeObservableTheory n) fieldSupportObs (gaugeCanonicalClass n)
gaugeRecovered-stepPow-observable-collapse n k x rx =
  cong SC.countNonZero (gaugeRecovered-stepPow-class n k x rx)

gaugeRecovered-step :
  ∀ n {x : GaugeState n} →
  PT.recoveredLaw (gaugeTheory n) x →
  PT.recoveredLaw (gaugeTheory n) (gaugeStep n x)
gaugeRecovered-step n {mkGauge g f} rx rewrite rx = SC.relaxSym-vacuum n

gaugeRecovered-fixed :
  ∀ n {x : GaugeState n} →
  PT.recoveredLaw (gaugeTheory n) x →
  gaugeStep n x ≡ x
gaugeRecovered-fixed n {mkGauge g f} rx rewrite rx =
  cong (mkGauge g) (SC.relaxSym-vacuum n)

gaugeRecovered-stepPow-id :
  ∀ n k {x : GaugeState n} →
  PT.recoveredLaw (gaugeTheory n) x →
  stepPow n k x ≡ x
gaugeRecovered-stepPow-id n zero rx = refl
gaugeRecovered-stepPow-id n (suc k) {x} rx =
  trans (cong (gaugeStep n) (gaugeRecovered-stepPow-id n k rx))
        (gaugeRecovered-fixed n rx)

gaugeRecovered-stepPow-from :
  ∀ n k (x : GaugeState n) →
  PT.recoveredLaw (gaugeTheory n) x →
  PT.recoveredLaw (gaugeTheory n) (stepPow n k x)
gaugeRecovered-stepPow-from n k x rx =
  trans (cong fieldMode (gaugeRecovered-stepPow-id n k {x = x} rx)) rx

gaugeRecovered-stepPow-tail-class :
  ∀ n k m (x : GaugeState n) →
  PT.recoveredLaw (gaugeTheory n) (stepPow n k x) →
  SQ.classOf (gaugeQuotiented n) (stepPow n m (stepPow n k x)) ≡ gaugeCanonicalClass n
gaugeRecovered-stepPow-tail-class n k m x rx =
  gaugeRecovered-stepPow-class n m (stepPow n k x)
    (gaugeRecovered-stepPow-from n m (stepPow n k x) rx)

gaugeRecovered-stepPow-tail-observable-collapse :
  ∀ n k m (x : GaugeState n) →
  PT.recoveredLaw (gaugeTheory n) (stepPow n k x) →
  Obs.ObservableTheory.eval (gaugeObservableTheory n) fieldSupportObs
    (SQ.classOf (gaugeQuotiented n) (stepPow n m (stepPow n k x)))
  ≡
  Obs.ObservableTheory.eval (gaugeObservableTheory n) fieldSupportObs (gaugeCanonicalClass n)
gaugeRecovered-stepPow-tail-observable-collapse n k m x rx =
  cong SC.countNonZero (gaugeRecovered-stepPow-tail-class n k m x rx)
