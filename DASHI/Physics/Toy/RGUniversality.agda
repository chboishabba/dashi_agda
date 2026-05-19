module DASHI.Physics.Toy.RGUniversality where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (_≤_; _<_; _+_; _*_; z≤n; s≤s)
open import Data.Nat.Properties as NatP using (≤-trans; ≤-refl; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; cong₂)
open import Relation.Nullary using (Dec; yes; no)

open import DASHI.Algebra.Trit using (Trit; zer; neg; pos)
open import DASHI.Physics.Toy.Recovery as TR
open import DASHI.Physics.PhysicalTheory as PT
open import DASHI.Physics.Refinement as Ref
import DASHI.Physics.SymmetryQuotient as SQ
open import DASHI.Physics.Observable as Obs
import DASHI.Physics.Measurement as Meas
import DASHI.Physics.Benchmark as Bench
open import DASHI.Physics.LocalWitness as LW
import DASHI.Physics.Toy.ScalarContinuum as SC

record Coupling : Set where
  constructor _,_
  field
    relevant   : Bool
    irrelevant : Trit

open Coupling public

rgStep : Coupling → Coupling
rgStep (r , i) = r , zer

rgObs : Coupling → Bool
rgObs = relevant

defectRG : Coupling → Nat
defectRG (r , zer) = zero
defectRG (r , neg) = suc zero
defectRG (r , pos) = suc zero

RGRecoveredLaw : Set
RGRecoveredLaw = ∀ x y → relevant x ≡ relevant y → rgObs (rgStep x) ≡ rgObs (rgStep y)

rgInv : Coupling → Set
rgInv _ = ⊤

rgStable : Coupling → Set
rgStable x = irrelevant x ≡ zer

rgInv-preserved : ∀ {x} → rgInv x → rgInv (rgStep x)
rgInv-preserved _ = tt

rgDefect-desc : ∀ {x} → rgInv x → defectRG (rgStep x) ≤ defectRG x
rgDefect-desc {(r , zer)} _ = z≤n
rgDefect-desc {(r , neg)} _ = z≤n
rgDefect-desc {(r , pos)} _ = z≤n

rgDefect-strict :
  ∀ {x} → rgInv x → defectRG x TR.≢ zero → defectRG (rgStep x) < defectRG x
rgDefect-strict {(r , zer)} _ nz = ⊥-elim (nz refl)
rgDefect-strict {(r , neg)} _ _ = s≤s z≤n
rgDefect-strict {(r , pos)} _ _ = s≤s z≤n

rgStable-fixed : ∀ {x} → rgStable x → rgStep x ≡ x
rgStable-fixed {(r , zer)} refl = refl
rgStable-fixed {(r , neg)} ()
rgStable-fixed {(r , pos)} ()

rgStable-from-zero : ∀ {x} → rgInv x → defectRG x ≡ zero → rgStable x
rgStable-from-zero {(r , zer)} _ refl = refl
rgStable-from-zero {(r , neg)} _ ()
rgStable-from-zero {(r , pos)} _ ()

rgRecovered-from-stable : ∀ {x} → rgStable x → RGRecoveredLaw
rgRecovered-from-stable stable x y sameRelevant = sameRelevant

RGTheory : TR.ToyTheory
RGTheory =
  record
    { X = Coupling
    ; Obs = Bool
    ; RecoveredLaw = RGRecoveredLaw
    ; step = rgStep
    ; defect = defectRG
    ; obs = rgObs
    ; inv = rgInv
    ; inv-preserved = λ {x} → rgInv-preserved {x}
    ; defect-desc = λ {x} → rgDefect-desc {x}
    ; defect-strict = λ {x} → rgDefect-strict {x}
    ; stable = rgStable
    ; stable-fixed = λ {x} → rgStable-fixed {x}
    ; stable-from-zero-defect = λ {x} → rgStable-from-zero {x}
    ; recovered-from-stable = λ {x} → rgRecovered-from-stable {x}
    }

fixedFor : Bool → Coupling
fixedFor r = r , zer

fixedFor-fixed : ∀ r → rgStep (fixedFor r) ≡ fixedFor r
fixedFor-fixed r = refl

rgStablePoint : Bool → TR.StablePoint RGTheory
rgStablePoint r =
  record
    { point = fixedFor r
    ; fixed = fixedFor-fixed r
    ; law = λ x y sameRelevant → sameRelevant
    }

rgRecovery : TR.RecoveryAxiom RGTheory
rgRecovery =
  record
    { stable-point = λ x _ → rgStablePoint (relevant x)
    }

universality-recovery :
  ∀ x y →
  relevant x ≡ relevant y →
  rgObs (rgStep x) ≡ rgObs (rgStep y)
universality-recovery x y sameRelevant =
  TR.StablePoint.law (TR.RecoveryAxiom.stable-point rgRecovery x tt) x y sameRelevant

same-basin-same-fixed-point :
  ∀ x y →
  relevant x ≡ relevant y →
  TR.StablePoint.point (TR.RecoveryAxiom.stable-point rgRecovery x tt) ≡
  TR.StablePoint.point (TR.RecoveryAxiom.stable-point rgRecovery y tt)
same-basin-same-fixed-point x y sameRelevant = cong fixedFor sameRelevant

record RGState (n : Nat) : Set where
  constructor mkRGState
  field
    relevantMode   : Bool
    irrelevantMode : SC.Carrier n

open RGState public

rgVacuum : (n : Nat) → Bool → RGState n
rgVacuum n r = mkRGState r (SC.vacuum n)

rgShellStep : (n : Nat) → RGState n → RGState n
rgShellStep n (mkRGState r i) = mkRGState r (SC.scalarStep n i)

rgShellTheory : (n : Nat) → PT.PhysicalTheory lzero
rgShellTheory n =
  record
    { State = RGState n
    ; step = rgShellStep n
    ; Defect = λ _ → ⊤
    ; defectSize = λ x → SC.countNonZero (irrelevantMode x)
    ; Inv = λ _ → ⊤
    ; inv-step = λ _ → tt
    ; defect-monotone = λ {x} _ → SC.scalarDefectMonotone n {irrelevantMode x}
    ; fixed = λ x → rgShellStep n x ≡ x
    ; recoveredLaw = λ x → irrelevantMode x ≡ SC.vacuum n
    }

rgShellApproxRefinement :
  (n : Nat) → Ref.ApproxRefinementStep (rgShellTheory n) (rgShellTheory (suc n))
rgShellApproxRefinement n =
  record
    { project = λ x → mkRGState (relevantMode x) (SC.dropLast (irrelevantMode x))
    ; embed = λ x → mkRGState (relevantMode x) (SC.appendZero (irrelevantMode x))
    ; approxEq₀ = λ x y → relevantMode x ≡ relevantMode y × SC.TailApprox (irrelevantMode x) (irrelevantMode y)
    ; commute-project≈ = λ x → refl , SC.dropLast-relaxSym≈-with zer (irrelevantMode x)
    }

rgTower : Ref.RefinementTower lzero
rgTower =
  record
    { TheoryAt = rgShellTheory
    ; refine = rgShellApproxRefinement
    }

rgAct : ∀ {n : Nat} → Bool → RGState n → RGState n
rgAct false x = x
rgAct true (mkRGState r i) = mkRGState r (SC.flipVec i)

rgStep-equivariant :
  ∀ n g x →
  rgShellStep n (rgAct g x) ≡ rgAct g (rgShellStep n x)
rgStep-equivariant n false x = refl
rgStep-equivariant n true (mkRGState r i) =
  cong (mkRGState r) (sym (SC.flip-relaxSymVec zer i))

rgSymmetric : (n : Nat) → SQ.SymmetricTheory lzero
rgSymmetric n =
  record
    { base = rgShellTheory n
    ; Group = Bool
    ; act = rgAct
    ; step-equivariant = rgStep-equivariant n
    ; inv-invariant = λ _ _ _ → tt
    }

rgPhysEq : (n : Nat) → SQ.PhysicalEquivalence (rgSymmetric n)
rgPhysEq n =
  record
    { _≈phys_ = λ x y → (x ≡ y) ⊎ (rgAct true x ≡ y)
    ; orbit→phys = λ where
        false x → inj₁ refl
        true  x → inj₂ refl
    ; step-respects = λ where
        {x} {y} (inj₁ eq) → inj₁ (cong (rgShellStep n) eq)
        {x} {y} (inj₂ eq) →
          inj₂ (trans (sym (rgStep-equivariant n true x))
                      (cong (rgShellStep n) eq))
    }

RGPhysState : Nat → Set
RGPhysState n = Bool × SC.Support n

rgClassOf : ∀ {n : Nat} → RGState n → RGPhysState n
rgClassOf (mkRGState r i) = r , SC.supportVec i

rgClass-sound :
  ∀ {n : Nat} (x y : RGState n) →
  SQ.PhysicalEquivalence._≈phys_ (rgPhysEq n) x y →
  rgClassOf x ≡ rgClassOf y
rgClass-sound x y (inj₁ eq) = cong rgClassOf eq
rgClass-sound x y (inj₂ eq) =
  cong₂ _,_ (cong relevantMode eq)
    (trans (SC.support-flipVec (irrelevantMode x))
           (cong SC.supportVec (cong irrelevantMode eq)))

rgQuotiented : (n : Nat) → SQ.QuotientedTheory lzero
rgQuotiented n =
  record
    { sym = rgSymmetric n
    ; physEq = rgPhysEq n
    ; PhysState = RGPhysState n
    ; repr = λ where (r , _) → rgVacuum n r
    ; classOf = rgClassOf
    ; class-sound = rgClass-sound
    }

rgRawSymmetric : (n : Nat) → SQ.SymmetricTheory lzero
rgRawSymmetric n =
  record
    { base = rgShellTheory n
    ; Group = ⊤
    ; act = λ _ x → x
    ; step-equivariant = λ _ x → refl
    ; inv-invariant = λ _ _ inv → inv
    }

rgRawPhysEq : (n : Nat) → SQ.PhysicalEquivalence (rgRawSymmetric n)
rgRawPhysEq n =
  record
    { _≈phys_ = _≡_
    ; orbit→phys = λ _ _ → refl
    ; step-respects = λ eq → cong (rgShellStep n) eq
    }

rgRawQuotiented : (n : Nat) → SQ.QuotientedTheory lzero
rgRawQuotiented n =
  record
    { sym = rgRawSymmetric n
    ; physEq = rgRawPhysEq n
    ; PhysState = RGState n
    ; repr = λ x → x
    ; classOf = λ x → x
    ; class-sound = λ _ _ eq → eq
    }

data RGObservable : Set where
  relevantObs : RGObservable
  irrelevantSupportObs : RGObservable

rgObservableTheory : (n : Nat) → Obs.ObservableTheory (rgQuotiented n)
rgObservableTheory n =
  record
    { Observable = RGObservable
    ; Value = λ where
        relevantObs → Bool
        irrelevantSupportObs → Nat
    ; eval = λ where
        relevantObs (r , s) → r
        irrelevantSupportObs (r , s) → SC.countTrueVec s
    }

rgObservableInvariant :
  (n : Nat) → Obs.SymmetryInvariantObservables (rgQuotiented n) (rgObservableTheory n)
rgObservableInvariant n =
  record
    { eval-well-defined = λ where
        relevantObs x y eq → cong fst eq
        irrelevantSupportObs x y eq → cong (λ z → SC.countTrueVec (snd z)) eq
    }
  where
    fst : ∀ {A B : Set} → A × B → A
    fst (a , b) = a

    snd : ∀ {A B : Set} → A × B → B
    snd (a , b) = b

relevantAsNat : Bool → Nat
relevantAsNat false = zero
relevantAsNat true = suc zero

data RGObservableExpr : Set where
  rel#    : RGObservableExpr
  irr#    : RGObservableExpr
  zeroO   : RGObservableExpr
  _+RG_   : RGObservableExpr → RGObservableExpr → RGObservableExpr
  scaleRG : Nat → RGObservableExpr → RGObservableExpr

rgObservableExprEval : (n : Nat) → RGObservableExpr → RGPhysState n → Nat
rgObservableExprEval n rel# (r , s) = relevantAsNat r
rgObservableExprEval n irr# (r , s) = SC.countTrueVec s
rgObservableExprEval n zeroO (r , s) = zero
rgObservableExprEval n (x +RG y) st = rgObservableExprEval n x st + rgObservableExprEval n y st
rgObservableExprEval n (scaleRG k x) st = k * rgObservableExprEval n x st

rgObservableAlgebra : (n : Nat) → Obs.ObservableAlgebra (rgQuotiented n)
rgObservableAlgebra n =
  record
    { Observable = RGObservableExpr
    ; Scalar = Nat
    ; _+O_ = _+RG_
    ; _·O_ = scaleRG
    ; _*O_ = _+RG_
    }

rgPredictionTheory : (n : Nat) → Meas.PredictionTheory (rgQuotiented n)
rgPredictionTheory n =
  record
    { Observable = RGObservableExpr
    ; Prediction = λ _ → Nat
    ; predict = λ O st → rgObservableExprEval n O st
    }

RGScheduleParameter : Set
RGScheduleParameter = Nat × Nat

scheduleGain : RGScheduleParameter → Nat
scheduleGain (gain , steps) = gain

scheduleSteps : RGScheduleParameter → Nat
scheduleSteps (gain , steps) = steps

stepPowSched : ∀ n → Nat → RGState n → RGState n
stepPowSched n zero x = x
stepPowSched n (suc k) x = rgShellStep n (stepPowSched n k x)

rgRelevant-stepPowSched :
  ∀ n k (x : RGState n) →
  relevantMode (stepPowSched n k x) ≡ relevantMode x
rgRelevant-stepPowSched n zero x = refl
rgRelevant-stepPowSched n (suc k) x = rgRelevant-stepPowSched n k x

rgIrrelObs-stepPowSched-monotone :
  ∀ n k (x : RGState n) →
  rgObservableExprEval n irr# (rgClassOf (stepPowSched n (suc k) x)) ≤
  rgObservableExprEval n irr# (rgClassOf (stepPowSched n k x))
rgIrrelObs-stepPowSched-monotone n k (mkRGState r i)
  rewrite SC.countTrue-supportVec (SC.scalarStep n (irrelevantMode (stepPowSched n k (mkRGState r i))))
        | SC.countTrue-supportVec (irrelevantMode (stepPowSched n k (mkRGState r i)))
  = SC.scalarDefectMonotone n {irrelevantMode (stepPowSched n k (mkRGState r i))}

rgScheduledPredictionTheory : (n : Nat) → Meas.PredictionTheory (rgRawQuotiented n)
rgScheduledPredictionTheory n =
  record
    { Observable = RGScheduleParameter × RGObservableExpr
    ; Prediction = λ _ → Nat
    ; predict = λ where
        (sched , O) st →
          scheduleGain sched * rgObservableExprEval n O (rgClassOf (stepPowSched n (scheduleSteps sched) st))
    }

RGBenchmarkParameter : Set
RGBenchmarkParameter = Nat

rgBenchmarkTheory : (n : Nat) → Bench.BenchmarkTheory′ (rgQuotiented n)
rgBenchmarkTheory n =
  record
    { Parameter = RGBenchmarkParameter
    ; Observable = RGObservableExpr
    ; Datum = λ _ → Nat
    ; predictB = λ gain O st → gain * rgObservableExprEval n O st
    }

rgScheduledBenchmarkTheory : (n : Nat) → Bench.BenchmarkTheory′ (rgRawQuotiented n)
rgScheduledBenchmarkTheory n =
  record
    { Parameter = RGScheduleParameter
    ; Observable = RGObservableExpr
    ; Datum = λ _ → Nat
    ; predictB = λ sched O st →
        scheduleGain sched * rgObservableExprEval n O (rgClassOf (stepPowSched n (scheduleSteps sched) st))
    }

eqPenalty : Nat → Nat → Nat
eqPenalty a b with a NatP.≟ b
... | yes _ = zero
... | no _ = suc zero

eqPenalty-refl : ∀ a → eqPenalty a a ≡ zero
eqPenalty-refl a with a NatP.≟ a
... | yes _ = refl
... | no absurd = ⊥-elim (absurd refl)

recoveryResidueNat : Nat → Nat
recoveryResidueNat zero = zero
recoveryResidueNat (suc _) = suc zero

scaleProfileNat : Nat → Nat → Nat
scaleProfileNat rel irr = rel + irr

pathProfileNat : Nat → Nat → Nat
pathProfileNat rel irr = rel + (suc (suc zero) * irr)

record RGBenchmarkScore : Set where
  constructor mkRGBenchmarkScore
  field
    endpoint : Nat
    path     : Nat
    recovery : Nat
    scale    : Nat

zeroRGBenchmarkScore : RGBenchmarkScore
zeroRGBenchmarkScore = mkRGBenchmarkScore zero zero zero zero

rgBenchmarkScore :
  Nat → Nat → Nat → Nat → RGBenchmarkScore
rgBenchmarkScore predRel predIrr obsRel obsIrr =
  mkRGBenchmarkScore
    (eqPenalty predRel obsRel + eqPenalty predIrr obsIrr)
    (eqPenalty (pathProfileNat predRel predIrr) (pathProfileNat obsRel obsIrr))
    (eqPenalty (recoveryResidueNat predIrr) (recoveryResidueNat obsIrr))
    (eqPenalty (scaleProfileNat predRel predIrr) (scaleProfileNat obsRel obsIrr))

rgBenchmarkScore-refl : ∀ rel irr → rgBenchmarkScore rel irr rel irr ≡ zeroRGBenchmarkScore
rgBenchmarkScore-refl rel irr
  rewrite eqPenalty-refl rel
        | eqPenalty-refl irr
        | eqPenalty-refl (pathProfileNat rel irr)
        | eqPenalty-refl (recoveryResidueNat irr)
        | eqPenalty-refl (scaleProfileNat rel irr)
  = refl

rgBenchmarkMatch : (n : Nat) → Bench.BenchmarkMatch (rgBenchmarkTheory n)
rgBenchmarkMatch n =
  record
    { Score = Nat
    ; mismatch = λ gain st ds →
        eqPenalty
          (Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain rel# st)
          (Bench.Dataset.observed ds rel#)
      + eqPenalty
          (Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain irr# st)
          (Bench.Dataset.observed ds irr#)
    }

rgRichBenchmarkMatch : (n : Nat) → Bench.BenchmarkMatch (rgBenchmarkTheory n)
rgRichBenchmarkMatch n =
  record
    { Score = RGBenchmarkScore
    ; mismatch = λ gain st ds →
        rgBenchmarkScore
          (Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain rel# st)
          (Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain irr# st)
          (Bench.Dataset.observed ds rel#)
          (Bench.Dataset.observed ds irr#)
    }

rgBenchmarkDataset :
  (n : Nat) →
  RGBenchmarkParameter →
  RGPhysState n →
  Bench.Dataset RGObservableExpr (λ _ → Nat)
rgBenchmarkDataset n gain st =
  record
    { observed = λ O → Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain O st
    }

rgBenchmarkSelfMismatch-zero :
  ∀ n gain (st : RGPhysState n) →
  Bench.BenchmarkMatch.mismatch (rgBenchmarkMatch n) gain st (rgBenchmarkDataset n gain st) ≡ zero
rgBenchmarkSelfMismatch-zero n gain st
  rewrite eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain rel# st)
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain irr# st)
  = refl

rgRichBenchmarkSelfMismatch-zero :
  ∀ n gain (st : RGPhysState n) →
  Bench.BenchmarkMatch.mismatch (rgRichBenchmarkMatch n) gain st (rgBenchmarkDataset n gain st) ≡
  zeroRGBenchmarkScore
rgRichBenchmarkSelfMismatch-zero n gain st =
  rgBenchmarkScore-refl
    (Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain rel# st)
    (Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain irr# st)

rgBasinLabel : ∀ {n : Nat} → RGState n → Bool
rgBasinLabel = relevantMode

rgIrrelevantSize : ∀ {n : Nat} → RGState n → Nat
rgIrrelevantSize x = SC.countTrueVec (SC.supportVec (irrelevantMode x))

rgCoarse : (n : Nat) → RGState (suc n) → RGState n
rgCoarse n = Ref.ApproxRefinementStep.project (rgShellApproxRefinement n)

rgCoarseClass : (n : Nat) → RGState (suc n) → RGPhysState n
rgCoarseClass n x = SQ.classOf (rgQuotiented n) (rgCoarse n x)

data RGCoarseScheme : Set where
  tailScheme : RGCoarseScheme
  flipTailScheme : RGCoarseScheme

data RGFlowMode : Set where
  relaxMode : RGFlowMode
  holdMode  : RGFlowMode

data RGFixedPoint : Set where
  disorderedVacuumFP : RGFixedPoint
  orderedVacuumFP    : RGFixedPoint
  disorderedResidualFP : RGFixedPoint
  orderedResidualFP    : RGFixedPoint

rgCanonicalFixedPoint : Bool → RGFixedPoint
rgCanonicalFixedPoint false = disorderedVacuumFP
rgCanonicalFixedPoint true = orderedVacuumFP

rgStepBy : (mode : RGFlowMode) → (n : Nat) → RGState n → RGState n
rgStepBy relaxMode n x = rgShellStep n x
rgStepBy holdMode n x = x

rgCoarseBy : (scheme : RGCoarseScheme) → (n : Nat) → RGState (suc n) → RGState n
rgCoarseBy tailScheme n x = rgCoarse n x
rgCoarseBy flipTailScheme n (mkRGState r i) = mkRGState r (SC.flipVec (SC.dropLast i))

rgFixedPointOfClass : ∀ {n} → RGPhysState n → RGFixedPoint
rgFixedPointOfClass (false , s) with SC.countTrueVec s NatP.≟ zero
... | yes _ = disorderedVacuumFP
... | no _ = disorderedResidualFP
rgFixedPointOfClass (true , s) with SC.countTrueVec s NatP.≟ zero
... | yes _ = orderedVacuumFP
... | no _ = orderedResidualFP

rgFixedPointOfState : ∀ {n} → RGState n → RGFixedPoint
rgFixedPointOfState x = rgFixedPointOfClass (rgClassOf x)

rgCoarseBy-class :
  ∀ scheme n (x : RGState (suc n)) →
  rgClassOf (rgCoarseBy scheme n x) ≡ rgCoarseClass n x
rgCoarseBy-class tailScheme n x = refl
rgCoarseBy-class flipTailScheme n (mkRGState r i) =
  cong₂ _,_ refl (sym (SC.support-flipVec (SC.dropLast i)))

rgBasinLabel-stepBy :
  ∀ mode n (x : RGState n) →
  rgBasinLabel (rgStepBy mode n x) ≡ rgBasinLabel x
rgBasinLabel-stepBy relaxMode n (mkRGState r i) = refl
rgBasinLabel-stepBy holdMode n x = refl

rgBasinLabel-coarseBy :
  ∀ scheme n (x : RGState (suc n)) →
  rgBasinLabel (rgCoarseBy scheme n x) ≡ rgBasinLabel x
rgBasinLabel-coarseBy tailScheme n (mkRGState r i) = refl
rgBasinLabel-coarseBy flipTailScheme n x = refl

rgIrrelevantContractsUnderStepBy :
  ∀ mode n (x : RGState n) →
  rgIrrelevantSize (rgStepBy mode n x) ≤ rgIrrelevantSize x
rgIrrelevantContractsUnderStepBy relaxMode n (mkRGState r i)
  rewrite SC.countTrue-supportVec (SC.scalarStep n i)
        | SC.countTrue-supportVec i
  = SC.scalarDefectMonotone n {i}
rgIrrelevantContractsUnderStepBy holdMode n x = NatP.≤-refl

rgCoarseByRelObservableStable :
  ∀ scheme n (x : RGState (suc n)) →
  rgObservableExprEval n rel# (rgClassOf (rgCoarseBy scheme n x)) ≡
  rgObservableExprEval (suc n) rel# (rgClassOf x)
rgCoarseByRelObservableStable tailScheme n (mkRGState r i) = refl
rgCoarseByRelObservableStable flipTailScheme n (mkRGState r i) = refl

rgCoarseByIrrelObservableMonotone :
  ∀ scheme n (x : RGState (suc n)) →
  rgObservableExprEval n irr# (rgClassOf (rgCoarseBy scheme n x)) ≤
  rgObservableExprEval (suc n) irr# (rgClassOf x)
rgCoarseByIrrelObservableMonotone tailScheme n (mkRGState r i)
  rewrite SC.countTrue-supportVec (SC.dropLast i)
        | SC.countTrue-supportVec i
  = SC.countNonZero-dropLast i
rgCoarseByIrrelObservableMonotone flipTailScheme n (mkRGState r i)
  rewrite sym (SC.support-flipVec (SC.dropLast i))
        | SC.countTrue-supportVec (SC.dropLast i)
        | SC.countTrue-supportVec i
  = SC.countNonZero-dropLast i

rgIrrelevantContractsUnderCoarseBy :
  ∀ scheme n (x : RGState (suc n)) →
  rgIrrelevantSize (rgCoarseBy scheme n x) ≤ rgIrrelevantSize x
rgIrrelevantContractsUnderCoarseBy tailScheme n (mkRGState r i)
  rewrite SC.countTrue-supportVec (SC.dropLast i)
        | SC.countTrue-supportVec i
  = SC.countNonZero-dropLast i
rgIrrelevantContractsUnderCoarseBy flipTailScheme n (mkRGState r i)
  rewrite sym (SC.support-flipVec (SC.dropLast i))
        | SC.countTrue-supportVec (SC.dropLast i)
        | SC.countTrue-supportVec i
  = SC.countNonZero-dropLast i

stepPowBy : (mode : RGFlowMode) → (n : Nat) → Nat → RGState n → RGState n
stepPowBy mode n zero x = x
stepPowBy mode n (suc k) x = rgStepBy mode n (stepPowBy mode n k x)

coarsePowBy : ∀ scheme k n → RGState (k + n) → RGState n
coarsePowBy scheme zero n x = x
coarsePowBy scheme (suc k) n x = coarsePowBy scheme k n (rgCoarseBy scheme (k + n) x)

rgSchemeFlow : ∀ scheme mode k m n → RGState (k + n) → RGState n
rgSchemeFlow scheme mode k m n x = stepPowBy mode n m (coarsePowBy scheme k n x)

rgBasinLabel-stepPowBy :
  ∀ mode n k (x : RGState n) →
  rgBasinLabel (stepPowBy mode n k x) ≡ rgBasinLabel x
rgBasinLabel-stepPowBy mode n zero x = refl
rgBasinLabel-stepPowBy mode n (suc k) x =
  trans (rgBasinLabel-stepBy mode n (stepPowBy mode n k x))
        (rgBasinLabel-stepPowBy mode n k x)

rgIrrelevantSize-stepPowBy-monotone :
  ∀ mode n k (x : RGState n) →
  rgIrrelevantSize (stepPowBy mode n k x) ≤ rgIrrelevantSize x
rgIrrelevantSize-stepPowBy-monotone mode n zero x = NatP.≤-refl
rgIrrelevantSize-stepPowBy-monotone mode n (suc k) x =
  NatP.≤-trans
    (rgIrrelevantContractsUnderStepBy mode n (stepPowBy mode n k x))
    (rgIrrelevantSize-stepPowBy-monotone mode n k x)

rgBasinLabel-coarsePowBy :
  ∀ scheme k n (x : RGState (k + n)) →
  rgBasinLabel (coarsePowBy scheme k n x) ≡ rgBasinLabel x
rgBasinLabel-coarsePowBy scheme zero n x = refl
rgBasinLabel-coarsePowBy scheme (suc k) n x =
  trans
    (rgBasinLabel-coarsePowBy scheme k n (rgCoarseBy scheme (k + n) x))
    (rgBasinLabel-coarseBy scheme (k + n) x)

rgIrrelevantSize-coarsePowBy-monotone :
  ∀ scheme k n (x : RGState (k + n)) →
  rgIrrelevantSize (coarsePowBy scheme k n x) ≤ rgIrrelevantSize x
rgIrrelevantSize-coarsePowBy-monotone scheme zero n x = NatP.≤-refl
rgIrrelevantSize-coarsePowBy-monotone scheme (suc k) n x =
  NatP.≤-trans
    (rgIrrelevantSize-coarsePowBy-monotone scheme k n (rgCoarseBy scheme (k + n) x))
    (rgIrrelevantContractsUnderCoarseBy scheme (k + n) x)

rgSchemeFlow-basin-stable :
  ∀ scheme mode k m n (x : RGState (k + n)) →
  rgBasinLabel (rgSchemeFlow scheme mode k m n x) ≡ rgBasinLabel x
rgSchemeFlow-basin-stable scheme mode k m n x =
  trans (rgBasinLabel-stepPowBy mode n m (coarsePowBy scheme k n x))
        (rgBasinLabel-coarsePowBy scheme k n x)

rgSchemeFlow-irrelevant-monotone :
  ∀ scheme mode k m n (x : RGState (k + n)) →
  rgIrrelevantSize (rgSchemeFlow scheme mode k m n x) ≤ rgIrrelevantSize x
rgSchemeFlow-irrelevant-monotone scheme mode k m n x =
  NatP.≤-trans
    (rgIrrelevantSize-stepPowBy-monotone mode n m (coarsePowBy scheme k n x))
    (rgIrrelevantSize-coarsePowBy-monotone scheme k n x)

rgSchemeFlow-rel-observable-stable :
  ∀ scheme mode k m n (x : RGState (k + n)) →
  rgObservableExprEval n rel# (rgClassOf (rgSchemeFlow scheme mode k m n x)) ≡
  rgObservableExprEval (k + n) rel# (rgClassOf x)
rgSchemeFlow-rel-observable-stable scheme mode k m n x =
  cong relevantAsNat (rgSchemeFlow-basin-stable scheme mode k m n x)

rgStepBy-from-recovered :
  ∀ mode n {x : RGState n} →
  PT.recoveredLaw (rgShellTheory n) x →
  PT.recoveredLaw (rgShellTheory n) (rgStepBy mode n x)
rgStepBy-from-recovered relaxMode n {mkRGState r i} rx rewrite rx = SC.relaxSym-vacuum n
rgStepBy-from-recovered holdMode n rx = rx

rgStepPowBy-from-recovered :
  ∀ mode n k {x : RGState n} →
  PT.recoveredLaw (rgShellTheory n) x →
  PT.recoveredLaw (rgShellTheory n) (stepPowBy mode n k x)
rgStepPowBy-from-recovered mode n zero rx = rx
rgStepPowBy-from-recovered mode n (suc k) {x} rx =
  rgStepBy-from-recovered mode n (rgStepPowBy-from-recovered mode n k {x} rx)

rgSchemeFlow-canonical-on-recovered :
  ∀ scheme mode k m n (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgSchemeFlow scheme mode k m n x) →
  rgClassOf (rgSchemeFlow scheme mode k m n x) ≡ rgClassOf (rgVacuum n (rgBasinLabel x))
rgSchemeFlow-canonical-on-recovered scheme mode k m n x rx =
  cong₂ _,_
    (rgSchemeFlow-basin-stable scheme mode k m n x)
    (cong SC.supportVec rx)

rgVacuum-support-count-zero :
  ∀ n →
  SC.countTrueVec (SC.supportVec (SC.vacuum n)) ≡ zero
rgVacuum-support-count-zero n
  rewrite SC.countTrue-supportVec (SC.vacuum n)
        | SC.countNonZero-vacuum n
  = refl

rgVacuum-fixedPoint :
  ∀ n r →
  rgFixedPointOfState (rgVacuum n r) ≡ rgCanonicalFixedPoint r
rgVacuum-fixedPoint n false with SC.countTrueVec (SC.supportVec (SC.vacuum n)) NatP.≟ zero
... | yes _ = refl
... | no nz rewrite rgVacuum-support-count-zero n = ⊥-elim (nz refl)
rgVacuum-fixedPoint n true with SC.countTrueVec (SC.supportVec (SC.vacuum n)) NatP.≟ zero
... | yes _ = refl
... | no nz rewrite rgVacuum-support-count-zero n = ⊥-elim (nz refl)

rgSchemeFlow-fixedPoint-on-recovered :
  ∀ scheme mode k m n (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgSchemeFlow scheme mode k m n x) →
  rgFixedPointOfState (rgSchemeFlow scheme mode k m n x) ≡
  rgCanonicalFixedPoint (rgBasinLabel x)
rgSchemeFlow-fixedPoint-on-recovered scheme mode k m n x rx
  rewrite rgSchemeFlow-canonical-on-recovered scheme mode k m n x rx
  = rgVacuum-fixedPoint n (rgBasinLabel x)

rgBasinLabel-step :
  ∀ n (x : RGState n) →
  rgBasinLabel (rgShellStep n x) ≡ rgBasinLabel x
rgBasinLabel-step n (mkRGState r i) = refl

rgBasinLabel-coarse :
  ∀ n (x : RGState (suc n)) →
  rgBasinLabel (rgCoarse n x) ≡ rgBasinLabel x
rgBasinLabel-coarse n (mkRGState r i) = refl

rgIrrelevantContractsUnderStep :
  ∀ n (x : RGState n) →
  rgIrrelevantSize (rgShellStep n x) ≤ rgIrrelevantSize x
rgIrrelevantContractsUnderStep n (mkRGState r i)
  rewrite SC.countTrue-supportVec (SC.scalarStep n i)
        | SC.countTrue-supportVec i
  = SC.scalarDefectMonotone n {i}

rgIrrelevantContractsUnderCoarse :
  ∀ n (x : RGState (suc n)) →
  rgIrrelevantSize (rgCoarse n x) ≤ rgIrrelevantSize x
rgIrrelevantContractsUnderCoarse n (mkRGState r i)
  rewrite SC.countTrue-supportVec (SC.dropLast i)
        | SC.countTrue-supportVec i
  = SC.countNonZero-dropLast i

rgScalingRelevantIrrelevant :
  ∀ n (x : RGState (suc n)) →
  (rgBasinLabel (rgCoarse n x) ≡ rgBasinLabel x) ×
  rgIrrelevantSize (rgCoarse n x) ≤ rgIrrelevantSize x
rgScalingRelevantIrrelevant n x =
  rgBasinLabel-coarse n x , rgIrrelevantContractsUnderCoarse n x

rgCoarseStepApprox :
  ∀ n (x : RGState (suc n)) →
  Ref.ApproxRefinementStep.approxEq₀ (rgShellApproxRefinement n)
    (rgCoarse n (rgShellStep (suc n) x))
    (rgShellStep n (rgCoarse n x))
rgCoarseStepApprox n (mkRGState r i) =
  refl , SC.dropLast-relaxSym≈-with zer i

rgCoarseStepClass-stable :
  ∀ n (x : RGState (suc n)) →
  rgBasinLabel (rgCoarse n (rgShellStep (suc n) x)) ≡
  rgBasinLabel (rgShellStep n (rgCoarse n x))
rgCoarseStepClass-stable n x = refl

rgCoarseRelObservableStable :
  ∀ n (x : RGState (suc n)) →
  rgObservableExprEval n rel# (rgCoarseClass n x) ≡
  rgObservableExprEval (suc n) rel# (rgClassOf x)
rgCoarseRelObservableStable n (mkRGState r i) = refl

rgCoarseIrrelObservableMonotone :
  ∀ n (x : RGState (suc n)) →
  rgObservableExprEval n irr# (rgCoarseClass n x) ≤
  rgObservableExprEval (suc n) irr# (rgClassOf x)
rgCoarseIrrelObservableMonotone n (mkRGState r i)
  rewrite SC.countTrue-supportVec (SC.dropLast i)
        | SC.countTrue-supportVec i
  = SC.countNonZero-dropLast i

stepPow : ∀ n → Nat → RGState n → RGState n
stepPow n zero x = x
stepPow n (suc k) x = rgShellStep n (stepPow n k x)

rgStepPow-vacuum :
  ∀ n k r →
  stepPow n k (mkRGState r (SC.vacuum n)) ≡ mkRGState r (SC.vacuum n)
rgStepPow-vacuum n zero r = refl
rgStepPow-vacuum n (suc k) r =
  trans (cong (rgShellStep n) (rgStepPow-vacuum n k r))
        (cong (mkRGState r) (SC.relaxSym-vacuum n))

rgStepPow-from-recovered :
  ∀ n k {x : RGState n} →
  PT.recoveredLaw (rgShellTheory n) x →
  PT.recoveredLaw (rgShellTheory n) (stepPow n k x)
rgStepPow-from-recovered n zero rx = rx
rgStepPow-from-recovered n (suc k) {mkRGState r i} rx rewrite rx =
  cong irrelevantMode (rgStepPow-vacuum n (suc k) r)

rgBasinLabel-stepPow :
  ∀ n k (x : RGState n) →
  rgBasinLabel (stepPow n k x) ≡ rgBasinLabel x
rgBasinLabel-stepPow n zero x = refl
rgBasinLabel-stepPow n (suc k) x =
  trans (rgBasinLabel-step n (stepPow n k x))
        (rgBasinLabel-stepPow n k x)

rgIrrelevantSize-stepPow-monotone :
  ∀ n k (x : RGState n) →
  rgIrrelevantSize (stepPow n k x) ≤ rgIrrelevantSize x
rgIrrelevantSize-stepPow-monotone n zero x = NatP.≤-refl
rgIrrelevantSize-stepPow-monotone n (suc k) x =
  NatP.≤-trans
    (rgIrrelevantContractsUnderStep n (stepPow n k x))
    (rgIrrelevantSize-stepPow-monotone n k x)

rgIrrelevantSize-stepPow≤initial :
  ∀ n k (x : RGState n) →
  rgIrrelevantSize (stepPow n k x) ≤ rgIrrelevantSize x
rgIrrelevantSize-stepPow≤initial n zero x = NatP.≤-refl
rgIrrelevantSize-stepPow≤initial n (suc k) x =
  NatP.≤-trans
    (rgIrrelevantContractsUnderStep n (stepPow n k x))
    (rgIrrelevantSize-stepPow≤initial n k x)

rgIrrelevantSize-class :
  ∀ {n} (x : RGState n) →
  rgIrrelevantSize x ≡ rgObservableExprEval n irr# (rgClassOf x)
rgIrrelevantSize-class (mkRGState r i) = refl

rgIrrelObs-stepPow-monotone :
  ∀ n k (x : RGState n) →
  rgObservableExprEval n irr# (rgClassOf (stepPow n (suc k) x)) ≤
  rgObservableExprEval n irr# (rgClassOf (stepPow n k x))
rgIrrelObs-stepPow-monotone n k x
  rewrite rgIrrelevantSize-class (stepPow n (suc k) x)
        | rgIrrelevantSize-class (stepPow n k x)
  = rgIrrelevantContractsUnderStep n (stepPow n k x)

rgAsymptotic :
  ∀ n (x : RGState n) → Set
rgAsymptotic n x =
  (∀ k → rgBasinLabel (stepPow n k x) ≡ rgBasinLabel x)
  × (∀ k → rgIrrelevantSize (stepPow n (suc k) x) ≤ rgIrrelevantSize (stepPow n k x))
  × (∀ k → rgIrrelevantSize (stepPow n k x) ≤ rgIrrelevantSize x)
  × (∀ k → rgObservableExprEval n rel# (rgClassOf (stepPow n k x)) ≡ rgObservableExprEval n rel# (rgClassOf x))
  × (∀ k →
      rgObservableExprEval n irr# (rgClassOf (stepPow n (suc k) x)) ≤
      rgObservableExprEval n irr# (rgClassOf (stepPow n k x)))

rgAsymptoticWitness :
  ∀ n (x : RGState n) → rgAsymptotic n x
rgAsymptoticWitness n x =
  (λ k → rgBasinLabel-stepPow n k x)
  , (λ k → rgIrrelevantContractsUnderStep n (stepPow n k x))
  , (λ k → rgIrrelevantSize-stepPow≤initial n k x)
  , (λ k → cong relevantAsNat (rgBasinLabel-stepPow n k x))
  , (λ k → rgIrrelObs-stepPow-monotone n k x)

coarsePow : ∀ k n → RGState (k + n) → RGState n
coarsePow zero n x = x
coarsePow (suc k) n x = coarsePow k n (rgCoarse (k + n) x)

rgBasinLabel-coarsePow :
  ∀ k n (x : RGState (k + n)) →
  rgBasinLabel (coarsePow k n x) ≡ rgBasinLabel x
rgBasinLabel-coarsePow zero n x = refl
rgBasinLabel-coarsePow (suc k) n x =
  trans (rgBasinLabel-coarsePow k n (rgCoarse (k + n) x))
        (rgBasinLabel-coarse (k + n) x)

rgIrrelevantSize-coarsePow-monotone :
  ∀ k n (x : RGState (k + n)) →
  rgIrrelevantSize (coarsePow k n x) ≤ rgIrrelevantSize x
rgIrrelevantSize-coarsePow-monotone zero n x = NatP.≤-refl
rgIrrelevantSize-coarsePow-monotone (suc k) n x =
  NatP.≤-trans
    (rgIrrelevantSize-coarsePow-monotone k n (rgCoarse (k + n) x))
    (rgIrrelevantContractsUnderCoarse (k + n) x)

rgCoarsePowRelObservableStable :
  ∀ k n (x : RGState (k + n)) →
  rgObservableExprEval n rel# (rgClassOf (coarsePow k n x)) ≡
  rgObservableExprEval (k + n) rel# (rgClassOf x)
rgCoarsePowRelObservableStable k n x =
  cong relevantAsNat (rgBasinLabel-coarsePow k n x)

rgCoarsePowIrrelObservableMonotone :
  ∀ k n (x : RGState (k + n)) →
  rgObservableExprEval n irr# (rgClassOf (coarsePow k n x)) ≤
  rgObservableExprEval (k + n) irr# (rgClassOf x)
rgCoarsePowIrrelObservableMonotone k n x
  rewrite sym (rgIrrelevantSize-class (coarsePow k n x))
        | sym (rgIrrelevantSize-class x)
  = rgIrrelevantSize-coarsePow-monotone k n x

rgRenormalize : ∀ k n → RGState (k + n) → RGState n
rgRenormalize k n x = rgShellStep n (coarsePow k n x)

rgRenormalize-basin-stable :
  ∀ k n (x : RGState (k + n)) →
  rgBasinLabel (rgRenormalize k n x) ≡ rgBasinLabel x
rgRenormalize-basin-stable k n x =
  trans (rgBasinLabel-step n (coarsePow k n x))
        (rgBasinLabel-coarsePow k n x)

rgRenormalize-irrelevant-monotone :
  ∀ k n (x : RGState (k + n)) →
  rgIrrelevantSize (rgRenormalize k n x) ≤ rgIrrelevantSize x
rgRenormalize-irrelevant-monotone k n x =
  NatP.≤-trans
    (rgIrrelevantContractsUnderStep n (coarsePow k n x))
    (rgIrrelevantSize-coarsePow-monotone k n x)

rgRenormalize-rel-observable-stable :
  ∀ k n (x : RGState (k + n)) →
  rgObservableExprEval n rel# (rgClassOf (rgRenormalize k n x)) ≡
  rgObservableExprEval (k + n) rel# (rgClassOf x)
rgRenormalize-rel-observable-stable k n x =
  cong relevantAsNat (rgRenormalize-basin-stable k n x)

rgRenormalize-irr-observable-monotone :
  ∀ k n (x : RGState (k + n)) →
  rgObservableExprEval n irr# (rgClassOf (rgRenormalize k n x)) ≤
  rgObservableExprEval (k + n) irr# (rgClassOf x)
rgRenormalize-irr-observable-monotone k n x
  rewrite sym (rgIrrelevantSize-class (rgRenormalize k n x))
        | sym (rgIrrelevantSize-class x)
  = rgRenormalize-irrelevant-monotone k n x

rgFlow : ∀ k m n → RGState (k + n) → RGState n
rgFlow k m n x = stepPow n m (coarsePow k n x)

rgFlow-basin-stable :
  ∀ k m n (x : RGState (k + n)) →
  rgBasinLabel (rgFlow k m n x) ≡ rgBasinLabel x
rgFlow-basin-stable k m n x =
  trans (rgBasinLabel-stepPow n m (coarsePow k n x))
        (rgBasinLabel-coarsePow k n x)

rgFlow-irrelevant-monotone :
  ∀ k m n (x : RGState (k + n)) →
  rgIrrelevantSize (rgFlow k m n x) ≤ rgIrrelevantSize x
rgFlow-irrelevant-monotone k m n x =
  NatP.≤-trans
    (rgIrrelevantSize-stepPow-monotone n m (coarsePow k n x))
    (rgIrrelevantSize-coarsePow-monotone k n x)

rgFlow-rel-observable-stable :
  ∀ k m n (x : RGState (k + n)) →
  rgObservableExprEval n rel# (rgClassOf (rgFlow k m n x)) ≡
  rgObservableExprEval (k + n) rel# (rgClassOf x)
rgFlow-rel-observable-stable k m n x =
  cong relevantAsNat (rgFlow-basin-stable k m n x)

rgFlow-irr-observable-monotone :
  ∀ k m n (x : RGState (k + n)) →
  rgObservableExprEval n irr# (rgClassOf (rgFlow k m n x)) ≤
  rgObservableExprEval (k + n) irr# (rgClassOf x)
rgFlow-irr-observable-monotone k m n x
  rewrite sym (rgIrrelevantSize-class (rgFlow k m n x))
        | sym (rgIrrelevantSize-class x)
  = rgFlow-irrelevant-monotone k m n x

rgFlow-canonical-on-recovered :
  ∀ k m n (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgFlow k m n x) →
  rgClassOf (rgFlow k m n x) ≡ rgClassOf (rgVacuum n (rgBasinLabel x))
rgFlow-canonical-on-recovered k m n x rx =
  cong₂ _,_
    (rgFlow-basin-stable k m n x)
    (cong SC.supportVec rx)

rgFlow-canonical-observable :
  ∀ k m n (O : RGObservableExpr) (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgFlow k m n x) →
  rgObservableExprEval n O (rgClassOf (rgFlow k m n x)) ≡
  rgObservableExprEval n O (rgClassOf (rgVacuum n (rgBasinLabel x)))
rgFlow-canonical-observable k m n O x rx =
  cong (rgObservableExprEval n O) (rgFlow-canonical-on-recovered k m n x rx)

rgFlow-step-monotone :
  ∀ k m n (x : RGState (k + n)) →
  rgIrrelevantSize (rgFlow k (suc m) n x) ≤
  rgIrrelevantSize (rgFlow k m n x)
rgFlow-step-monotone k m n x =
  rgIrrelevantContractsUnderStep n (rgFlow k m n x)

rgFlow-irr-observable-step-monotone :
  ∀ k m n (x : RGState (k + n)) →
  rgObservableExprEval n irr# (rgClassOf (rgFlow k (suc m) n x)) ≤
  rgObservableExprEval n irr# (rgClassOf (rgFlow k m n x))
rgFlow-irr-observable-step-monotone k m n x
  rewrite sym (rgIrrelevantSize-class (rgFlow k (suc m) n x))
        | sym (rgIrrelevantSize-class (rgFlow k m n x))
  = rgFlow-step-monotone k m n x

rgFlow-irr-benchmark-step-monotone :
  ∀ k m n gain (x : RGState (k + n)) →
  Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain irr# (rgClassOf (rgFlow k (suc m) n x)) ≤
  Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain irr# (rgClassOf (rgFlow k m n x))
rgFlow-irr-benchmark-step-monotone k m n zero x = z≤n
rgFlow-irr-benchmark-step-monotone k m n (suc gain) x =
  NatP.+-mono-≤
    (rgFlow-irr-observable-step-monotone k m n x)
    (rgFlow-irr-benchmark-step-monotone k m n gain x)

data RGMixedSchedule (n : Nat) : Nat → Set where
  mixed-done : Nat → RGMixedSchedule n zero
  mixed-layer : ∀ {k} → Nat → RGMixedSchedule n k → RGMixedSchedule n (suc k)

rgRunMixed : ∀ {k n} → RGMixedSchedule n k → RGState (k + n) → RGState n
rgRunMixed {n = n} (mixed-done m) x = stepPow n m x
rgRunMixed {n = n} (mixed-layer {k} m sch) x =
  rgRunMixed sch (rgCoarse (k + n) (stepPow (suc (k + n)) m x))

rgMixedPathMass : ∀ {k n} → RGMixedSchedule n k → RGState (k + n) → Nat
rgMixedPathMass {n = n} (mixed-done m) x =
  rgIrrelevantSize (stepPow n m x)
rgMixedPathMass {n = n} (mixed-layer {k} m sch) x =
  let coarseState = rgCoarse (k + n) (stepPow (suc (k + n)) m x) in
  rgIrrelevantSize coarseState + rgMixedPathMass sch coarseState

rgMixedRecoveryMass : ∀ {k n} → RGMixedSchedule n k → RGState (k + n) → Nat
rgMixedRecoveryMass {n = n} (mixed-done m) x =
  recoveryResidueNat (rgIrrelevantSize (stepPow n m x))
rgMixedRecoveryMass {n = n} (mixed-layer {k} m sch) x =
  let coarseState = rgCoarse (k + n) (stepPow (suc (k + n)) m x) in
  recoveryResidueNat (rgIrrelevantSize coarseState) + rgMixedRecoveryMass sch coarseState

rgMixedScaleMass : ∀ {k n} → RGMixedSchedule n k → RGState (k + n) → Nat
rgMixedScaleMass {n = n} (mixed-done m) x =
  scaleProfileNat (relevantAsNat (rgBasinLabel (stepPow n m x)))
                  (rgIrrelevantSize (stepPow n m x))
rgMixedScaleMass {n = n} (mixed-layer {k} m sch) x =
  let coarseState = rgCoarse (k + n) (stepPow (suc (k + n)) m x) in
  scaleProfileNat (relevantAsNat (rgBasinLabel coarseState))
                  (rgIrrelevantSize coarseState)
  + rgMixedScaleMass sch coarseState

uniformMixed : (n k m : Nat) → RGMixedSchedule n k
uniformMixed n zero m = mixed-done m
uniformMixed n (suc k) m = mixed-layer m (uniformMixed n k m)

data RGMixedSchedule2 (n : Nat) : Nat → Set where
  mixed2-done : RGFlowMode → Nat → RGMixedSchedule2 n zero
  mixed2-layer : ∀ {k} → RGCoarseScheme → RGFlowMode → Nat → RGMixedSchedule2 n k → RGMixedSchedule2 n (suc k)

rgRunMixed2 : ∀ {k n} → RGMixedSchedule2 n k → RGState (k + n) → RGState n
rgRunMixed2 {n = n} (mixed2-done mode m) x = stepPowBy mode n m x
rgRunMixed2 {n = n} (mixed2-layer {k} scheme mode m sch) x =
  rgRunMixed2 sch (rgCoarseBy scheme (k + n) (stepPowBy mode (suc (k + n)) m x))

uniformMixed2 : (scheme : RGCoarseScheme) → (mode : RGFlowMode) → (n k m : Nat) → RGMixedSchedule2 n k
uniformMixed2 scheme mode n zero m = mixed2-done mode m
uniformMixed2 scheme mode n (suc k) m = mixed2-layer scheme mode m (uniformMixed2 scheme mode n k m)

rgMixed2-basin-stable :
  ∀ {k n} (sch : RGMixedSchedule2 n k) (x : RGState (k + n)) →
  rgBasinLabel (rgRunMixed2 sch x) ≡ rgBasinLabel x
rgMixed2-basin-stable (mixed2-done mode m) x = rgBasinLabel-stepPowBy mode _ m x
rgMixed2-basin-stable {n = n} (mixed2-layer {k} scheme mode m sch) x =
  trans
    (rgMixed2-basin-stable sch (rgCoarseBy scheme (k + n) (stepPowBy mode (suc (k + n)) m x)))
    (trans
      (rgBasinLabel-coarseBy scheme (k + n) (stepPowBy mode (suc (k + n)) m x))
      (rgBasinLabel-stepPowBy mode (suc (k + n)) m x))

rgMixed2-irrelevant-bounded :
  ∀ {k n} (sch : RGMixedSchedule2 n k) (x : RGState (k + n)) →
  rgObservableExprEval n irr# (rgClassOf (rgRunMixed2 sch x)) ≤ rgIrrelevantSize x
rgMixed2-irrelevant-bounded (mixed2-done mode m) x
  rewrite sym (rgIrrelevantSize-class (stepPowBy mode _ m x))
        | sym (rgIrrelevantSize-class x)
  = rgIrrelevantSize-stepPowBy-monotone mode _ m x
rgMixed2-irrelevant-bounded {n = n} (mixed2-layer {k} scheme mode m sch) x =
  NatP.≤-trans
    (rgMixed2-irrelevant-bounded sch (rgCoarseBy scheme (k + n) (stepPowBy mode (suc (k + n)) m x)))
    (NatP.≤-trans
      (rgIrrelevantContractsUnderCoarseBy scheme (k + n) (stepPowBy mode (suc (k + n)) m x))
      (rgIrrelevantSize-stepPowBy-monotone mode (suc (k + n)) m x))

rgMixed2-recovered-same-class :
  ∀ {k} n (sch₁ sch₂ : RGMixedSchedule2 n k) (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed2 sch₁ x) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed2 sch₂ x) →
  rgClassOf (rgRunMixed2 sch₁ x) ≡ rgClassOf (rgRunMixed2 sch₂ x)
rgMixed2-recovered-same-class n sch₁ sch₂ x rx₁ rx₂ =
  cong₂ _,_
    (trans (rgMixed2-basin-stable sch₁ x)
           (sym (rgMixed2-basin-stable sch₂ x)))
    (trans (cong SC.supportVec rx₁)
           (sym (cong SC.supportVec rx₂)))

rgMixed2-rel-observable-stable :
  ∀ {k} n (sch : RGMixedSchedule2 n k) gain (x : RGState (k + n)) →
  gain * rgObservableExprEval n rel# (rgClassOf (rgRunMixed2 sch x)) ≡
  gain * rgObservableExprEval (k + n) rel# (rgClassOf x)
rgMixed2-rel-observable-stable n sch gain x =
  cong (gain *_) (cong relevantAsNat (rgMixed2-basin-stable sch x))

data RGMixedTraceObservable2 : Set where
  endpoint2RG : RGObservableExpr → RGMixedTraceObservable2
  path2RG     : RGMixedTraceObservable2
  recovery2RG : RGMixedTraceObservable2
  scale2RG#   : RGMixedTraceObservable2

schemeMass : RGCoarseScheme → Nat
schemeMass tailScheme = zero
schemeMass flipTailScheme = suc zero

modeMass : RGFlowMode → Nat
modeMass relaxMode = suc zero
modeMass holdMode = zero

rgMixed2PathMass : ∀ {k n} → RGMixedSchedule2 n k → RGState (k + n) → Nat
rgMixed2PathMass {n = n} (mixed2-done mode m) x =
  modeMass mode + rgIrrelevantSize (stepPowBy mode n m x)
rgMixed2PathMass {n = n} (mixed2-layer {k} scheme mode m sch) x =
  let coarseState = rgCoarseBy scheme (k + n) (stepPowBy mode (suc (k + n)) m x) in
  schemeMass scheme + modeMass mode + rgIrrelevantSize coarseState + rgMixed2PathMass sch coarseState

rgMixed2RecoveryMass : ∀ {k n} → RGMixedSchedule2 n k → RGState (k + n) → Nat
rgMixed2RecoveryMass {n = n} (mixed2-done mode m) x =
  modeMass mode + recoveryResidueNat (rgIrrelevantSize (stepPowBy mode n m x))
rgMixed2RecoveryMass {n = n} (mixed2-layer {k} scheme mode m sch) x =
  let coarseState = rgCoarseBy scheme (k + n) (stepPowBy mode (suc (k + n)) m x) in
  schemeMass scheme + modeMass mode + recoveryResidueNat (rgIrrelevantSize coarseState) + rgMixed2RecoveryMass sch coarseState

rgMixed2ScaleMass : ∀ {k n} → RGMixedSchedule2 n k → RGState (k + n) → Nat
rgMixed2ScaleMass {n = n} (mixed2-done mode m) x =
  modeMass mode +
  scaleProfileNat (relevantAsNat (rgBasinLabel (stepPowBy mode n m x)))
                  (rgIrrelevantSize (stepPowBy mode n m x))
rgMixed2ScaleMass {n = n} (mixed2-layer {k} scheme mode m sch) x =
  let coarseState = rgCoarseBy scheme (k + n) (stepPowBy mode (suc (k + n)) m x) in
  schemeMass scheme + modeMass mode +
  scaleProfileNat (relevantAsNat (rgBasinLabel coarseState))
                  (rgIrrelevantSize coarseState)
  + rgMixed2ScaleMass sch coarseState

rgMixed2TraceObservableEval :
  ∀ {k} n (sch : RGMixedSchedule2 n k) →
  RGMixedTraceObservable2 → RGState (k + n) → Nat
rgMixed2TraceObservableEval n sch (endpoint2RG O) st =
  rgObservableExprEval n O (rgClassOf (rgRunMixed2 sch st))
rgMixed2TraceObservableEval n sch path2RG st = rgMixed2PathMass sch st
rgMixed2TraceObservableEval n sch recovery2RG st = rgMixed2RecoveryMass sch st
rgMixed2TraceObservableEval n sch scale2RG# st = rgMixed2ScaleMass sch st

rgMixed2TraceBenchmarkTheory :
  ∀ {k} (n : Nat) →
  (sch : RGMixedSchedule2 n k) →
  Bench.BenchmarkTheory′ (rgRawQuotiented (k + n))
rgMixed2TraceBenchmarkTheory n sch =
  record
    { Parameter = RGBenchmarkParameter
    ; Observable = RGMixedTraceObservable2
    ; Datum = λ _ → Nat
    ; predictB = λ gain O st → gain * rgMixed2TraceObservableEval n sch O st
    }

rgMixed2TraceBenchmarkDataset :
  ∀ {k} (n : Nat) →
  (sch : RGMixedSchedule2 n k) →
  RGBenchmarkParameter →
  RGState (k + n) →
  Bench.Dataset RGMixedTraceObservable2 (λ _ → Nat)
rgMixed2TraceBenchmarkDataset n sch gain st =
  record
    { observed = λ O → Bench.BenchmarkTheory′.predictB (rgMixed2TraceBenchmarkTheory n sch) gain O st
    }

rgMixed2TraceBenchmarkMatch :
  ∀ {k} (n : Nat) →
  (sch : RGMixedSchedule2 n k) →
  Bench.BenchmarkMatch (rgMixed2TraceBenchmarkTheory n sch)
rgMixed2TraceBenchmarkMatch n sch =
  record
    { Score = RGBenchmarkScore
    ; mismatch = λ gain st ds →
        mkRGBenchmarkScore
          (eqPenalty
             (Bench.BenchmarkTheory′.predictB (rgMixed2TraceBenchmarkTheory n sch) gain (endpoint2RG rel#) st)
             (Bench.Dataset.observed ds (endpoint2RG rel#))
           + eqPenalty
             (Bench.BenchmarkTheory′.predictB (rgMixed2TraceBenchmarkTheory n sch) gain (endpoint2RG irr#) st)
             (Bench.Dataset.observed ds (endpoint2RG irr#)))
          (eqPenalty
             (Bench.BenchmarkTheory′.predictB (rgMixed2TraceBenchmarkTheory n sch) gain path2RG st)
             (Bench.Dataset.observed ds path2RG))
          (eqPenalty
             (Bench.BenchmarkTheory′.predictB (rgMixed2TraceBenchmarkTheory n sch) gain recovery2RG st)
             (Bench.Dataset.observed ds recovery2RG))
          (eqPenalty
             (Bench.BenchmarkTheory′.predictB (rgMixed2TraceBenchmarkTheory n sch) gain scale2RG# st)
             (Bench.Dataset.observed ds scale2RG#))
    }

rgMixed2TraceBenchmarkSelfMismatch-zero :
  ∀ {k} n (sch : RGMixedSchedule2 n k) gain (st : RGState (k + n)) →
  Bench.BenchmarkMatch.mismatch (rgMixed2TraceBenchmarkMatch n sch) gain st (rgMixed2TraceBenchmarkDataset n sch gain st) ≡
  zeroRGBenchmarkScore
rgMixed2TraceBenchmarkSelfMismatch-zero n sch gain st
  rewrite eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixed2TraceBenchmarkTheory n sch) gain (endpoint2RG rel#) st)
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixed2TraceBenchmarkTheory n sch) gain (endpoint2RG irr#) st)
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixed2TraceBenchmarkTheory n sch) gain path2RG st)
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixed2TraceBenchmarkTheory n sch) gain recovery2RG st)
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixed2TraceBenchmarkTheory n sch) gain scale2RG# st)
  = refl

rgMixed2TraceRecovered-endpoint-zero :
  ∀ {k} n (sch₁ sch₂ : RGMixedSchedule2 n k) gain (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed2 sch₁ x) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed2 sch₂ x) →
  RGBenchmarkScore.endpoint
        (Bench.BenchmarkMatch.mismatch
          (rgMixed2TraceBenchmarkMatch n sch₁)
          gain
          x
          (rgMixed2TraceBenchmarkDataset n sch₂ gain x))
  ≡ zero
rgMixed2TraceRecovered-endpoint-zero n sch₁ sch₂ gain x rx₁ rx₂
  rewrite cong (gain *_) (cong (rgObservableExprEval n rel#) (rgMixed2-recovered-same-class n sch₁ sch₂ x rx₁ rx₂))
        | cong (gain *_) (cong (rgObservableExprEval n irr#) (rgMixed2-recovered-same-class n sch₁ sch₂ x rx₁ rx₂))
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixed2TraceBenchmarkTheory n sch₂) gain (endpoint2RG rel#) x)
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixed2TraceBenchmarkTheory n sch₂) gain (endpoint2RG irr#) x)
  = refl

rgFlipVacuum-support-count-zero :
  ∀ n →
  SC.countTrueVec (SC.supportVec (SC.flipVec (SC.vacuum n))) ≡ zero
rgFlipVacuum-support-count-zero n =
  trans
    (cong SC.countTrueVec (sym (SC.support-flipVec (SC.vacuum n))))
    (rgVacuum-support-count-zero n)

rgVacuum-irrelevantSize-zero :
  ∀ n r →
  rgIrrelevantSize (rgVacuum n r) ≡ zero
rgVacuum-irrelevantSize-zero n r = rgVacuum-support-count-zero n

rgCoarseBy-vacuum :
  ∀ scheme n r →
  rgCoarseBy scheme n (rgVacuum (suc n) r) ≡ rgVacuum n r
rgCoarseBy-vacuum tailScheme n r
  rewrite SC.project-vacuum n
  = refl
rgCoarseBy-vacuum flipTailScheme n r
  rewrite SC.project-vacuum n
        | SC.flip-vacuum n
  = refl

rgRunUniformMixed2-hold-vacuum :
  ∀ scheme k n r →
  rgRunMixed2 (uniformMixed2 scheme holdMode n k zero) (rgVacuum (k + n) r) ≡
  rgVacuum n r
rgRunUniformMixed2-hold-vacuum scheme zero n r = refl
rgRunUniformMixed2-hold-vacuum scheme (suc k) n r
  rewrite rgCoarseBy-vacuum scheme (k + n) r
  = rgRunUniformMixed2-hold-vacuum scheme k n r

rgUniformMixed2-tail-path-on-vacuum :
  ∀ k n r →
  rgMixed2TraceObservableEval n (uniformMixed2 tailScheme holdMode n k zero) path2RG (rgVacuum (k + n) r) ≡ zero
rgUniformMixed2-tail-path-on-vacuum zero n r
  rewrite rgVacuum-irrelevantSize-zero n r
  = refl
rgUniformMixed2-tail-path-on-vacuum (suc k) n r
  rewrite SC.project-vacuum (k + n)
        | rgVacuum-irrelevantSize-zero (k + n) r
  = rgUniformMixed2-tail-path-on-vacuum k n r

mutual
  rgUniformMixed2-flip-path-on-vacuum :
    ∀ k n r →
    rgMixed2TraceObservableEval n (uniformMixed2 flipTailScheme holdMode n k zero) path2RG (rgVacuum (k + n) r) ≡ k
  rgUniformMixed2-flip-path-on-vacuum zero n r
    rewrite rgVacuum-irrelevantSize-zero n r
    = refl
  rgUniformMixed2-flip-path-on-vacuum (suc k) n r
    rewrite SC.project-vacuum (k + n)
          | rgFlipVacuum-support-count-zero (k + n)
          | rgUniformMixed2-flip-path-on-flipped-vacuum k n r
    = refl

  rgUniformMixed2-flip-path-on-flipped-vacuum :
    ∀ k n r →
    rgMixed2PathMass (uniformMixed2 flipTailScheme holdMode n k zero) (mkRGState r (SC.flipVec (SC.vacuum (k + n)))) ≡ k
  rgUniformMixed2-flip-path-on-flipped-vacuum k n r
    rewrite SC.flip-vacuum (k + n)
    = rgUniformMixed2-flip-path-on-vacuum k n r

eqPenalty-zero-suc : ∀ k → eqPenalty zero (suc k) ≡ suc zero
eqPenalty-zero-suc k with zero NatP.≟ suc k
... | yes ()
... | no _ = refl

rgMixed2-tail-vs-flip-endpoint-class-on-vacuum :
  ∀ n r →
  rgClassOf (rgRunMixed2 (uniformMixed2 tailScheme holdMode n (suc zero) zero) (rgVacuum (suc n) r)) ≡
  rgClassOf (rgRunMixed2 (uniformMixed2 flipTailScheme holdMode n (suc zero) zero) (rgVacuum (suc n) r))
rgMixed2-tail-vs-flip-endpoint-class-on-vacuum n r
  rewrite SC.project-vacuum n
        | SC.project-vacuum n
        | sym (SC.support-flipVec (SC.vacuum n))
  = refl

rgMixed2-tail-vs-flip-path-channel-on-vacuum :
  ∀ n r →
  rgMixed2TraceObservableEval n (uniformMixed2 tailScheme holdMode n (suc zero) zero) path2RG (rgVacuum (suc n) r) ≡ zero
  ×
  rgMixed2TraceObservableEval n (uniformMixed2 flipTailScheme holdMode n (suc zero) zero) path2RG (rgVacuum (suc n) r) ≡ suc zero
rgMixed2-tail-vs-flip-path-channel-on-vacuum n r
  rewrite SC.project-vacuum n
        | SC.project-vacuum n
        | rgVacuum-support-count-zero n
        | rgFlipVacuum-support-count-zero n
  = refl , refl

rgCoarseBy-flip-irrelevantSize :
  ∀ n (x : RGState (suc n)) →
  rgIrrelevantSize (rgCoarseBy flipTailScheme n x) ≡
  rgIrrelevantSize (rgCoarseBy tailScheme n x)
rgCoarseBy-flip-irrelevantSize n (mkRGState r i)
  rewrite sym (SC.support-flipVec (SC.dropLast i))
  = refl

rgMixed2-tail-vs-flip-one-layer-hold-endpoint-class :
  ∀ n (x : RGState (suc n)) →
  rgClassOf (rgRunMixed2 (uniformMixed2 tailScheme holdMode n (suc zero) zero) x) ≡
  rgClassOf (rgRunMixed2 (uniformMixed2 flipTailScheme holdMode n (suc zero) zero) x)
rgMixed2-tail-vs-flip-one-layer-hold-endpoint-class n x
  rewrite rgCoarseBy-class tailScheme n x
        | rgCoarseBy-class flipTailScheme n x
  = refl

rgMixed2-tail-vs-flip-one-layer-hold-path-step :
  ∀ n (x : RGState (suc n)) →
  suc (rgMixed2TraceObservableEval n (uniformMixed2 tailScheme holdMode n (suc zero) zero) path2RG x) ≡
  rgMixed2TraceObservableEval n (uniformMixed2 flipTailScheme holdMode n (suc zero) zero) path2RG x
rgMixed2-tail-vs-flip-one-layer-hold-path-step n x
  rewrite rgCoarseBy-flip-irrelevantSize n x
  = refl

rgUniformMixed2-tail-vs-flip-endpoint-class-on-vacuum :
  ∀ k n r →
  rgClassOf (rgRunMixed2 (uniformMixed2 tailScheme holdMode n k zero) (rgVacuum (k + n) r)) ≡
  rgClassOf (rgRunMixed2 (uniformMixed2 flipTailScheme holdMode n k zero) (rgVacuum (k + n) r))
rgUniformMixed2-tail-vs-flip-endpoint-class-on-vacuum k n r
  rewrite rgRunUniformMixed2-hold-vacuum tailScheme k n r
        | rgRunUniformMixed2-hold-vacuum flipTailScheme k n r
  = refl

rgMixed2-tail-vs-flip-trace-benchmark-split :
  ∀ n r →
  let x = rgVacuum (suc n) r in
  RGBenchmarkScore.endpoint
    (Bench.BenchmarkMatch.mismatch
      (rgMixed2TraceBenchmarkMatch n (uniformMixed2 tailScheme holdMode n (suc zero) zero))
      (suc zero)
      x
      (rgMixed2TraceBenchmarkDataset n (uniformMixed2 flipTailScheme holdMode n (suc zero) zero) (suc zero) x))
  ≡ zero
  ×
  RGBenchmarkScore.path
    (Bench.BenchmarkMatch.mismatch
      (rgMixed2TraceBenchmarkMatch n (uniformMixed2 tailScheme holdMode n (suc zero) zero))
      (suc zero)
      x
      (rgMixed2TraceBenchmarkDataset n (uniformMixed2 flipTailScheme holdMode n (suc zero) zero) (suc zero) x))
  ≡ suc zero
rgMixed2-tail-vs-flip-trace-benchmark-split n r
  rewrite rgMixed2-tail-vs-flip-endpoint-class-on-vacuum n r
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB
            (rgMixed2TraceBenchmarkTheory n (uniformMixed2 flipTailScheme holdMode n (suc zero) zero))
            (suc zero) (endpoint2RG rel#) (rgVacuum (suc n) r))
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB
            (rgMixed2TraceBenchmarkTheory n (uniformMixed2 flipTailScheme holdMode n (suc zero) zero))
            (suc zero) (endpoint2RG irr#) (rgVacuum (suc n) r))
        | SC.project-vacuum n
        | SC.project-vacuum n
        | rgVacuum-support-count-zero n
        | rgFlipVacuum-support-count-zero n
  = refl , refl

rgUniformMixed2-tail-vs-flip-trace-benchmark-split :
  ∀ k n r →
  let x = rgVacuum ((suc k) + n) r in
  RGBenchmarkScore.endpoint
    (Bench.BenchmarkMatch.mismatch
      (rgMixed2TraceBenchmarkMatch n (uniformMixed2 tailScheme holdMode n (suc k) zero))
      (suc zero)
      x
      (rgMixed2TraceBenchmarkDataset n (uniformMixed2 flipTailScheme holdMode n (suc k) zero) (suc zero) x))
  ≡ zero
  ×
  RGBenchmarkScore.path
    (Bench.BenchmarkMatch.mismatch
      (rgMixed2TraceBenchmarkMatch n (uniformMixed2 tailScheme holdMode n (suc k) zero))
      (suc zero)
      x
      (rgMixed2TraceBenchmarkDataset n (uniformMixed2 flipTailScheme holdMode n (suc k) zero) (suc zero) x))
  ≡ suc zero
rgUniformMixed2-tail-vs-flip-trace-benchmark-split k n r
  rewrite cong (suc zero *_) (cong (rgObservableExprEval n rel#)
            (rgUniformMixed2-tail-vs-flip-endpoint-class-on-vacuum (suc k) n r))
        | cong (suc zero *_) (cong (rgObservableExprEval n irr#)
            (rgUniformMixed2-tail-vs-flip-endpoint-class-on-vacuum (suc k) n r))
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB
            (rgMixed2TraceBenchmarkTheory n (uniformMixed2 flipTailScheme holdMode n (suc k) zero))
            (suc zero) (endpoint2RG rel#) (rgVacuum ((suc k) + n) r))
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB
            (rgMixed2TraceBenchmarkTheory n (uniformMixed2 flipTailScheme holdMode n (suc k) zero))
            (suc zero) (endpoint2RG irr#) (rgVacuum ((suc k) + n) r))
        | rgUniformMixed2-tail-path-on-vacuum (suc k) n r
        | rgUniformMixed2-flip-path-on-vacuum (suc k) n r
        | eqPenalty-zero-suc k
  = refl , refl

rgMixed-basin-stable :
  ∀ {k n} (sch : RGMixedSchedule n k) (x : RGState (k + n)) →
  rgBasinLabel (rgRunMixed sch x) ≡ rgBasinLabel x
rgMixed-basin-stable (mixed-done m) x = rgBasinLabel-stepPow _ m x
rgMixed-basin-stable {n = n} (mixed-layer {k} m sch) x =
  trans
    (rgMixed-basin-stable sch (rgCoarse (k + n) (stepPow (suc (k + n)) m x)))
    (trans
      (rgBasinLabel-coarse (k + n) (stepPow (suc (k + n)) m x))
      (rgBasinLabel-stepPow (suc (k + n)) m x))

rgMixed-irrelevant-bounded :
  ∀ {k n} (sch : RGMixedSchedule n k) (x : RGState (k + n)) →
  rgObservableExprEval n irr# (rgClassOf (rgRunMixed sch x)) ≤ rgIrrelevantSize x
rgMixed-irrelevant-bounded (mixed-done m) x
  rewrite sym (rgIrrelevantSize-class (stepPow _ m x))
        | sym (rgIrrelevantSize-class x)
  = rgIrrelevantSize-stepPow-monotone _ m x
rgMixed-irrelevant-bounded {n = n} (mixed-layer {k} m sch) x =
  NatP.≤-trans
    (rgMixed-irrelevant-bounded sch (rgCoarse (k + n) (stepPow (suc (k + n)) m x)))
    (NatP.≤-trans
      (rgIrrelevantContractsUnderCoarse (k + n) (stepPow (suc (k + n)) m x))
      (rgIrrelevantSize-stepPow-monotone (suc (k + n)) m x))

rgMixedBenchmarkTheory :
  ∀ {k} (n : Nat) →
  RGMixedSchedule n k →
  Bench.BenchmarkTheory′ (rgRawQuotiented (k + n))
rgMixedBenchmarkTheory {k} n sch =
  record
    { Parameter = RGBenchmarkParameter
    ; Observable = RGObservableExpr
    ; Datum = λ _ → Nat
    ; predictB = λ gain O st → gain * rgObservableExprEval n O (rgClassOf (rgRunMixed sch st))
    }

data RGMixedTraceObservable : Set where
  endpointRG : RGObservableExpr → RGMixedTraceObservable
  pathRG     : RGMixedTraceObservable
  recoveryRG : RGMixedTraceObservable
  scaleRG#   : RGMixedTraceObservable

rgMixedTraceObservableEval :
  ∀ {k} n (sch : RGMixedSchedule n k) →
  RGMixedTraceObservable → RGState (k + n) → Nat
rgMixedTraceObservableEval n sch (endpointRG O) st =
  rgObservableExprEval n O (rgClassOf (rgRunMixed sch st))
rgMixedTraceObservableEval n sch pathRG st = rgMixedPathMass sch st
rgMixedTraceObservableEval n sch recoveryRG st = rgMixedRecoveryMass sch st
rgMixedTraceObservableEval n sch scaleRG# st = rgMixedScaleMass sch st

rgMixedTraceBenchmarkTheory :
  ∀ {k} (n : Nat) →
  (sch : RGMixedSchedule n k) →
  Bench.BenchmarkTheory′ (rgRawQuotiented (k + n))
rgMixedTraceBenchmarkTheory n sch =
  record
    { Parameter = RGBenchmarkParameter
    ; Observable = RGMixedTraceObservable
    ; Datum = λ _ → Nat
    ; predictB = λ gain O st → gain * rgMixedTraceObservableEval n sch O st
    }

rgMixedTraceBenchmarkDataset :
  ∀ {k} (n : Nat) →
  (sch : RGMixedSchedule n k) →
  RGBenchmarkParameter →
  RGState (k + n) →
  Bench.Dataset RGMixedTraceObservable (λ _ → Nat)
rgMixedTraceBenchmarkDataset n sch gain st =
  record
    { observed = λ O → Bench.BenchmarkTheory′.predictB (rgMixedTraceBenchmarkTheory n sch) gain O st
    }

rgMixedBenchmarkDataset :
  ∀ {k} (n : Nat) →
  (sch : RGMixedSchedule n k) →
  RGBenchmarkParameter →
  RGState (k + n) →
  Bench.Dataset RGObservableExpr (λ _ → Nat)
rgMixedBenchmarkDataset n sch gain st =
  record
    { observed = λ O → Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch) gain O st
    }

rgMixedBenchmarkMatch :
  ∀ {k} (n : Nat) →
  (sch : RGMixedSchedule n k) →
  Bench.BenchmarkMatch (rgMixedBenchmarkTheory n sch)
rgMixedBenchmarkMatch n sch =
  record
    { Score = Nat
    ; mismatch = λ gain st ds →
        eqPenalty
          (Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch) gain rel# st)
          (Bench.Dataset.observed ds rel#)
      + eqPenalty
          (Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch) gain irr# st)
          (Bench.Dataset.observed ds irr#)
    }

rgMixedRichBenchmarkMatch :
  ∀ {k} (n : Nat) →
  (sch : RGMixedSchedule n k) →
  Bench.BenchmarkMatch (rgMixedBenchmarkTheory n sch)
rgMixedRichBenchmarkMatch n sch =
  record
    { Score = RGBenchmarkScore
    ; mismatch = λ gain st ds →
        rgBenchmarkScore
          (Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch) gain rel# st)
          (Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch) gain irr# st)
          (Bench.Dataset.observed ds rel#)
          (Bench.Dataset.observed ds irr#)
    }

rgMixedTraceBenchmarkMatch :
  ∀ {k} (n : Nat) →
  (sch : RGMixedSchedule n k) →
  Bench.BenchmarkMatch (rgMixedTraceBenchmarkTheory n sch)
rgMixedTraceBenchmarkMatch n sch =
  record
    { Score = RGBenchmarkScore
    ; mismatch = λ gain st ds →
        mkRGBenchmarkScore
          (eqPenalty
             (Bench.BenchmarkTheory′.predictB (rgMixedTraceBenchmarkTheory n sch) gain (endpointRG rel#) st)
             (Bench.Dataset.observed ds (endpointRG rel#))
           + eqPenalty
             (Bench.BenchmarkTheory′.predictB (rgMixedTraceBenchmarkTheory n sch) gain (endpointRG irr#) st)
             (Bench.Dataset.observed ds (endpointRG irr#)))
          (eqPenalty
             (Bench.BenchmarkTheory′.predictB (rgMixedTraceBenchmarkTheory n sch) gain pathRG st)
             (Bench.Dataset.observed ds pathRG))
          (eqPenalty
             (Bench.BenchmarkTheory′.predictB (rgMixedTraceBenchmarkTheory n sch) gain recoveryRG st)
             (Bench.Dataset.observed ds recoveryRG))
          (eqPenalty
             (Bench.BenchmarkTheory′.predictB (rgMixedTraceBenchmarkTheory n sch) gain scaleRG# st)
             (Bench.Dataset.observed ds scaleRG#))
    }

rgMixedBenchmarkSelfMismatch-zero :
  ∀ {k} n (sch : RGMixedSchedule n k) gain (st : RGState (k + n)) →
  Bench.BenchmarkMatch.mismatch (rgMixedBenchmarkMatch n sch) gain st (rgMixedBenchmarkDataset n sch gain st) ≡ zero
rgMixedBenchmarkSelfMismatch-zero n sch gain st
  rewrite eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch) gain rel# st)
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch) gain irr# st)
  = refl

rgMixedRichBenchmarkSelfMismatch-zero :
  ∀ {k} n (sch : RGMixedSchedule n k) gain (st : RGState (k + n)) →
  Bench.BenchmarkMatch.mismatch (rgMixedRichBenchmarkMatch n sch) gain st (rgMixedBenchmarkDataset n sch gain st) ≡
  zeroRGBenchmarkScore
rgMixedRichBenchmarkSelfMismatch-zero n sch gain st =
  rgBenchmarkScore-refl
    (Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch) gain rel# st)
    (Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch) gain irr# st)

rgMixedTraceBenchmarkSelfMismatch-zero :
  ∀ {k} n (sch : RGMixedSchedule n k) gain (st : RGState (k + n)) →
  Bench.BenchmarkMatch.mismatch (rgMixedTraceBenchmarkMatch n sch) gain st (rgMixedTraceBenchmarkDataset n sch gain st) ≡
  zeroRGBenchmarkScore
rgMixedTraceBenchmarkSelfMismatch-zero n sch gain st
  rewrite eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixedTraceBenchmarkTheory n sch) gain (endpointRG rel#) st)
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixedTraceBenchmarkTheory n sch) gain (endpointRG irr#) st)
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixedTraceBenchmarkTheory n sch) gain pathRG st)
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixedTraceBenchmarkTheory n sch) gain recoveryRG st)
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixedTraceBenchmarkTheory n sch) gain scaleRG# st)
  = refl

rgMixed-rel-benchmark-stable :
  ∀ {k} n (sch : RGMixedSchedule n k) gain (x : RGState (k + n)) →
  Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch) gain rel# x ≡
  gain * rgObservableExprEval (k + n) rel# (rgClassOf x)
rgMixed-rel-benchmark-stable n sch gain x =
  cong (gain *_) (cong relevantAsNat (rgMixed-basin-stable sch x))

rgMixed-irr-benchmark-bounded :
  ∀ {k} n (sch : RGMixedSchedule n k) gain (x : RGState (k + n)) →
  Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch) gain irr# x ≤
  gain * rgIrrelevantSize x
rgMixed-irr-benchmark-bounded n sch zero x = z≤n
rgMixed-irr-benchmark-bounded n sch (suc gain) x =
  NatP.+-mono-≤
    (rgMixed-irrelevant-bounded sch x)
    (rgMixed-irr-benchmark-bounded n sch gain x)

rgMixed-rel-benchmark-agree :
  ∀ {k} n (sch₁ sch₂ : RGMixedSchedule n k) gain (O : RGObservableExpr) (x : RGState (k + n)) →
  O ≡ rel# →
  Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch₁) gain O x ≡
  Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch₂) gain O x
rgMixed-rel-benchmark-agree n sch₁ sch₂ gain rel# x refl =
  cong (gain *_) (cong relevantAsNat
    (trans (rgMixed-basin-stable sch₁ x)
           (sym (rgMixed-basin-stable sch₂ x))))

rgMixed-recovered-same-class :
  ∀ {k} n (sch₁ sch₂ : RGMixedSchedule n k) (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed sch₁ x) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed sch₂ x) →
  rgClassOf (rgRunMixed sch₁ x) ≡ rgClassOf (rgRunMixed sch₂ x)
rgMixed-recovered-same-class n sch₁ sch₂ x rx₁ rx₂ =
  cong₂ _,_
    (trans (rgMixed-basin-stable sch₁ x)
           (sym (rgMixed-basin-stable sch₂ x)))
    (trans (cong SC.supportVec rx₁)
           (sym (cong SC.supportVec rx₂)))

rgMixed-recovered-observable-agree :
  ∀ {k} n (sch₁ sch₂ : RGMixedSchedule n k) (O : RGObservableExpr) (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed sch₁ x) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed sch₂ x) →
  rgObservableExprEval n O (rgClassOf (rgRunMixed sch₁ x)) ≡
  rgObservableExprEval n O (rgClassOf (rgRunMixed sch₂ x))
rgMixed-recovered-observable-agree n sch₁ sch₂ O x rx₁ rx₂ =
  cong (rgObservableExprEval n O) (rgMixed-recovered-same-class n sch₁ sch₂ x rx₁ rx₂)

rgMixed-recovered-benchmark-mismatch-zero :
  ∀ {k} n (sch₁ sch₂ : RGMixedSchedule n k) gain (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed sch₁ x) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed sch₂ x) →
  Bench.BenchmarkMatch.mismatch
    (rgMixedBenchmarkMatch n sch₁)
    gain
    x
    (rgMixedBenchmarkDataset n sch₂ gain x)
  ≡ zero
rgMixed-recovered-benchmark-mismatch-zero n sch₁ sch₂ gain x rx₁ rx₂
  rewrite rgMixed-recovered-observable-agree n sch₁ sch₂ rel# x rx₁ rx₂
        | rgMixed-recovered-observable-agree n sch₁ sch₂ irr# x rx₁ rx₂
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch₂) gain rel# x)
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch₂) gain irr# x)
  = refl

rgMixed-recovered-rich-benchmark-mismatch-zero :
  ∀ {k} n (sch₁ sch₂ : RGMixedSchedule n k) gain (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed sch₁ x) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed sch₂ x) →
  Bench.BenchmarkMatch.mismatch
    (rgMixedRichBenchmarkMatch n sch₁)
    gain
    x
    (rgMixedBenchmarkDataset n sch₂ gain x)
  ≡ zeroRGBenchmarkScore
rgMixed-recovered-rich-benchmark-mismatch-zero n sch₁ sch₂ gain x rx₁ rx₂
  rewrite rgMixed-recovered-observable-agree n sch₁ sch₂ rel# x rx₁ rx₂
        | rgMixed-recovered-observable-agree n sch₁ sch₂ irr# x rx₁ rx₂
  = rgBenchmarkScore-refl (Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch₂) gain rel# x)
                         (Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n sch₂) gain irr# x)

rgMixedTraceRecovered-endpoint-zero :
  ∀ {k} n (sch₁ sch₂ : RGMixedSchedule n k) gain (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed sch₁ x) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed sch₂ x) →
  RGBenchmarkScore.endpoint
    (Bench.BenchmarkMatch.mismatch
      (rgMixedTraceBenchmarkMatch n sch₁)
      gain
      x
      (rgMixedTraceBenchmarkDataset n sch₂ gain x))
  ≡ zero
rgMixedTraceRecovered-endpoint-zero n sch₁ sch₂ gain x rx₁ rx₂
  rewrite rgMixed-recovered-observable-agree n sch₁ sch₂ rel# x rx₁ rx₂
        | rgMixed-recovered-observable-agree n sch₁ sch₂ irr# x rx₁ rx₂
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixedTraceBenchmarkTheory n sch₂) gain (endpointRG rel#) x)
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgMixedTraceBenchmarkTheory n sch₂) gain (endpointRG irr#) x)
  = refl

rgMixed-step-tail-canonical :
  ∀ {k} n (sch : RGMixedSchedule n k) t (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed sch x) →
  rgClassOf (stepPow n t (rgRunMixed sch x)) ≡
  rgClassOf (rgVacuum n (rgBasinLabel x))
rgMixed-step-tail-canonical n sch t x rx =
  cong₂ _,_
    (trans (rgBasinLabel-stepPow n t (rgRunMixed sch x))
           (rgMixed-basin-stable sch x))
    (cong SC.supportVec
      (rgStepPow-from-recovered n t {x = rgRunMixed sch x} rx))

rgMixed-step-tail-canonical-observable :
  ∀ {k} n (sch : RGMixedSchedule n k) t (O : RGObservableExpr) (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed sch x) →
  rgObservableExprEval n O (rgClassOf (stepPow n t (rgRunMixed sch x))) ≡
  rgObservableExprEval n O (rgClassOf (rgVacuum n (rgBasinLabel x)))
rgMixed-step-tail-canonical-observable n sch t O x rx =
  cong (rgObservableExprEval n O) (rgMixed-step-tail-canonical n sch t x rx)

rgMixed-step-tail-benchmark-mismatch-zero :
  ∀ {k} n (sch : RGMixedSchedule n k) t gain (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed sch x) →
  Bench.BenchmarkMatch.mismatch
    (rgBenchmarkMatch n)
    gain
    (rgClassOf (stepPow n t (rgRunMixed sch x)))
    (rgBenchmarkDataset n gain (rgClassOf (rgVacuum n (rgBasinLabel x))))
  ≡ zero
rgMixed-step-tail-benchmark-mismatch-zero n sch t gain x rx
  rewrite rgMixed-step-tail-canonical-observable n sch t rel# x rx
        | rgMixed-step-tail-canonical-observable n sch t irr# x rx
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain rel# (rgClassOf (rgVacuum n (rgBasinLabel x))))
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain irr# (rgClassOf (rgVacuum n (rgBasinLabel x))))
  = refl

rgMixed-step-tail-cross-benchmark-mismatch-zero :
  ∀ {k} n (sch₁ sch₂ : RGMixedSchedule n k) t gain (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed sch₁ x) →
  PT.recoveredLaw (rgShellTheory n) (rgRunMixed sch₂ x) →
  Bench.BenchmarkMatch.mismatch
    (rgBenchmarkMatch n)
    gain
    (rgClassOf (stepPow n t (rgRunMixed sch₁ x)))
    (rgBenchmarkDataset n gain (rgClassOf (stepPow n t (rgRunMixed sch₂ x))))
  ≡ zero
rgMixed-step-tail-cross-benchmark-mismatch-zero n sch₁ sch₂ t gain x rx₁ rx₂
  rewrite rgMixed-step-tail-canonical-observable n sch₁ t rel# x rx₁
        | rgMixed-step-tail-canonical-observable n sch₁ t irr# x rx₁
        | rgMixed-step-tail-canonical-observable n sch₂ t rel# x rx₂
        | rgMixed-step-tail-canonical-observable n sch₂ t irr# x rx₂
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain rel# (rgClassOf (rgVacuum n (rgBasinLabel x))))
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain irr# (rgClassOf (rgVacuum n (rgBasinLabel x))))
  = refl

rgScheduled-rel-benchmark-stable :
  ∀ n gain t (x : RGState n) →
  Bench.BenchmarkTheory′.predictB (rgScheduledBenchmarkTheory n) (gain , t) rel# x ≡
  gain * rgObservableExprEval n rel# (rgClassOf x)
rgScheduled-rel-benchmark-stable n gain t x =
  cong (gain *_) (cong relevantAsNat (rgRelevant-stepPowSched n t x))

rgScheduled-irr-benchmark-step-monotone :
  ∀ n gain t (x : RGState n) →
  Bench.BenchmarkTheory′.predictB (rgScheduledBenchmarkTheory n) (gain , suc t) irr# x ≤
  Bench.BenchmarkTheory′.predictB (rgScheduledBenchmarkTheory n) (gain , t) irr# x
rgScheduled-irr-benchmark-step-monotone n zero t x = z≤n
rgScheduled-irr-benchmark-step-monotone n (suc gain) t x =
  NatP.+-mono-≤
    (rgIrrelObs-stepPowSched-monotone n t x)
    (rgScheduled-irr-benchmark-step-monotone n gain t x)

rgFlow-step-tail-canonical :
  ∀ k m t n (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgFlow k m n x) →
  rgClassOf (stepPow n t (rgFlow k m n x)) ≡
  rgClassOf (rgVacuum n (rgBasinLabel x))
rgFlow-step-tail-canonical k m t n x rx =
  cong₂ _,_
    (trans (rgBasinLabel-stepPow n t (rgFlow k m n x))
           (rgFlow-basin-stable k m n x))
    (cong SC.supportVec
      (rgStepPow-from-recovered n t {x = rgFlow k m n x} rx))

rgFlow-step-tail-canonical-observable :
  ∀ k m t n (O : RGObservableExpr) (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgFlow k m n x) →
  rgObservableExprEval n O (rgClassOf (stepPow n t (rgFlow k m n x))) ≡
  rgObservableExprEval n O (rgClassOf (rgVacuum n (rgBasinLabel x)))
rgFlow-step-tail-canonical-observable k m t n O x rx =
  cong (rgObservableExprEval n O) (rgFlow-step-tail-canonical k m t n x rx)

rgFused : ∀ k n → RGState (k + n) → RGState n
rgFused zero n x = rgShellStep n x
rgFused (suc k) n x = rgFused k n (rgCoarse (k + n) (rgShellStep (suc (k + n)) x))

rgFused-zero-is-flow :
  ∀ n (x : RGState n) →
  rgFused zero n x ≡ rgFlow zero (suc zero) n x
rgFused-zero-is-flow n x = refl

rgUniformMixed-one-is-fused :
  ∀ k n (x : RGState (k + n)) →
  rgRunMixed (uniformMixed n k (suc zero)) x ≡ rgFused k n x
rgUniformMixed-one-is-fused zero n x = refl
rgUniformMixed-one-is-fused (suc k) n x =
  rgUniformMixed-one-is-fused k n
    (rgCoarse (k + n) (rgShellStep (suc (k + n)) x))

rgUniformMixed-one-benchmark-agree :
  ∀ k n gain (O : RGObservableExpr) (x : RGState (k + n)) →
  Bench.BenchmarkTheory′.predictB (rgMixedBenchmarkTheory n (uniformMixed n k (suc zero))) gain O x ≡
  Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain O (rgClassOf (rgFused k n x))
rgUniformMixed-one-benchmark-agree k n gain O x =
  cong (λ st → gain * rgObservableExprEval n O (rgClassOf st))
    (rgUniformMixed-one-is-fused k n x)

rgFused-basin-stable :
  ∀ k n (x : RGState (k + n)) →
  rgBasinLabel (rgFused k n x) ≡ rgBasinLabel x
rgFused-basin-stable zero n x = rgBasinLabel-step n x
rgFused-basin-stable (suc k) n x =
  trans
    (rgFused-basin-stable k n (rgCoarse (k + n) (rgShellStep (suc (k + n)) x)))
    (trans (rgBasinLabel-coarse (k + n) (rgShellStep (suc (k + n)) x))
           (rgBasinLabel-step (suc (k + n)) x))

rgFused-irrelevant-monotone :
  ∀ k n (x : RGState (k + n)) →
  rgIrrelevantSize (rgFused k n x) ≤ rgIrrelevantSize x
rgFused-irrelevant-monotone zero n x =
  rgIrrelevantContractsUnderStep n x
rgFused-irrelevant-monotone (suc k) n x =
  NatP.≤-trans
    (rgFused-irrelevant-monotone k n (rgCoarse (k + n) (rgShellStep (suc (k + n)) x)))
    (NatP.≤-trans
      (rgIrrelevantContractsUnderCoarse (k + n) (rgShellStep (suc (k + n)) x))
      (rgIrrelevantContractsUnderStep (suc (k + n)) x))

rgFused-rel-observable-stable :
  ∀ k n (x : RGState (k + n)) →
  rgObservableExprEval n rel# (rgClassOf (rgFused k n x)) ≡
  rgObservableExprEval (k + n) rel# (rgClassOf x)
rgFused-rel-observable-stable k n x =
  cong relevantAsNat (rgFused-basin-stable k n x)

rgFused-irr-observable-monotone :
  ∀ k n (x : RGState (k + n)) →
  rgObservableExprEval n irr# (rgClassOf (rgFused k n x)) ≤
  rgObservableExprEval (k + n) irr# (rgClassOf x)
rgFused-irr-observable-monotone k n x
  rewrite sym (rgIrrelevantSize-class (rgFused k n x))
        | sym (rgIrrelevantSize-class x)
  = rgFused-irrelevant-monotone k n x

rgFused-canonical-on-recovered :
  ∀ k n (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgFused k n x) →
  rgClassOf (rgFused k n x) ≡ rgClassOf (rgVacuum n (rgBasinLabel x))
rgFused-canonical-on-recovered k n x rx =
  cong₂ _,_
    (rgFused-basin-stable k n x)
    (cong SC.supportVec rx)

rgFused-canonical-observable :
  ∀ k n (O : RGObservableExpr) (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgFused k n x) →
  rgObservableExprEval n O (rgClassOf (rgFused k n x)) ≡
  rgObservableExprEval n O (rgClassOf (rgVacuum n (rgBasinLabel x)))
rgFused-canonical-observable k n O x rx =
  cong (rgObservableExprEval n O) (rgFused-canonical-on-recovered k n x rx)

rgFused-step-tail-canonical :
  ∀ k t n (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgFused k n x) →
  rgClassOf (stepPow n t (rgFused k n x)) ≡
  rgClassOf (rgVacuum n (rgBasinLabel x))
rgFused-step-tail-canonical k t n x rx =
  cong₂ _,_
    (trans (rgBasinLabel-stepPow n t (rgFused k n x))
           (rgFused-basin-stable k n x))
    (cong SC.supportVec
      (rgStepPow-from-recovered n t {x = rgFused k n x} rx))

rgFused-step-tail-canonical-observable :
  ∀ k t n (O : RGObservableExpr) (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgFused k n x) →
  rgObservableExprEval n O (rgClassOf (stepPow n t (rgFused k n x))) ≡
  rgObservableExprEval n O (rgClassOf (rgVacuum n (rgBasinLabel x)))
rgFused-step-tail-canonical-observable k t n O x rx =
  cong (rgObservableExprEval n O) (rgFused-step-tail-canonical k t n x rx)

rgFused-flow-basin-agree :
  ∀ k m n (x : RGState (k + n)) →
  rgBasinLabel (rgFused k n x) ≡ rgBasinLabel (rgFlow k m n x)
rgFused-flow-basin-agree k m n x =
  trans (rgFused-basin-stable k n x)
        (sym (rgFlow-basin-stable k m n x))

rgFused-flow-rel-observable-agree :
  ∀ k m n (x : RGState (k + n)) →
  rgObservableExprEval n rel# (rgClassOf (rgFused k n x)) ≡
  rgObservableExprEval n rel# (rgClassOf (rgFlow k m n x))
rgFused-flow-rel-observable-agree k m n x =
  cong relevantAsNat (rgFused-flow-basin-agree k m n x)

rgFused-stepPow-flow-basin-agree :
  ∀ k t n (x : RGState (k + n)) →
  rgBasinLabel (stepPow n t (rgFused k n x)) ≡
  rgBasinLabel (rgFlow k (suc t) n x)
rgFused-stepPow-flow-basin-agree k t n x =
  trans
    (rgBasinLabel-stepPow n t (rgFused k n x))
    (trans
      (rgFused-basin-stable k n x)
      (sym (rgFlow-basin-stable k (suc t) n x)))

rgFused-stepPow-flow-rel-observable-agree :
  ∀ k t n (x : RGState (k + n)) →
  rgObservableExprEval n rel# (rgClassOf (stepPow n t (rgFused k n x))) ≡
  rgObservableExprEval n rel# (rgClassOf (rgFlow k (suc t) n x))
rgFused-stepPow-flow-rel-observable-agree k t n x =
  cong relevantAsNat (rgFused-stepPow-flow-basin-agree k t n x)

rgFused-flow-rel-benchmark-agree :
  ∀ k m n gain (x : RGState (k + n)) →
  Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain rel# (rgClassOf (rgFused k n x)) ≡
  Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain rel# (rgClassOf (rgFlow k m n x))
rgFused-flow-rel-benchmark-agree k m n gain x =
  cong (gain *_) (rgFused-flow-rel-observable-agree k m n x)

rgFused-stepPow-flow-rel-benchmark-agree :
  ∀ k t n gain (x : RGState (k + n)) →
  Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain rel# (rgClassOf (stepPow n t (rgFused k n x))) ≡
  Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain rel# (rgClassOf (rgFlow k (suc t) n x))
rgFused-stepPow-flow-rel-benchmark-agree k t n gain x =
  cong (gain *_) (rgFused-stepPow-flow-rel-observable-agree k t n x)

rgFused-flow-recovered-same-class :
  ∀ k m n (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgFused k n x) →
  PT.recoveredLaw (rgShellTheory n) (rgFlow k m n x) →
  rgClassOf (rgFused k n x) ≡ rgClassOf (rgFlow k m n x)
rgFused-flow-recovered-same-class k m n x rxf rflow =
  trans
    (rgFused-canonical-on-recovered k n x rxf)
    (sym (rgFlow-canonical-on-recovered k m n x rflow))

rgFused-flow-recovered-observable-agree :
  ∀ k m n (O : RGObservableExpr) (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgFused k n x) →
  PT.recoveredLaw (rgShellTheory n) (rgFlow k m n x) →
  rgObservableExprEval n O (rgClassOf (rgFused k n x)) ≡
  rgObservableExprEval n O (rgClassOf (rgFlow k m n x))
rgFused-flow-recovered-observable-agree k m n O x rxf rflow =
  cong (rgObservableExprEval n O)
    (rgFused-flow-recovered-same-class k m n x rxf rflow)

rgFused-flow-recovered-benchmark-mismatch-zero :
  ∀ k m n gain (x : RGState (k + n)) →
  PT.recoveredLaw (rgShellTheory n) (rgFused k n x) →
  PT.recoveredLaw (rgShellTheory n) (rgFlow k m n x) →
  Bench.BenchmarkMatch.mismatch
    (rgBenchmarkMatch n)
    gain
    (rgClassOf (rgFused k n x))
    (rgBenchmarkDataset n gain (rgClassOf (rgFlow k m n x)))
  ≡ zero
rgFused-flow-recovered-benchmark-mismatch-zero k m n gain x rxf rflow
  rewrite rgFused-flow-recovered-observable-agree k m n rel# x rxf rflow
        | rgFused-flow-recovered-observable-agree k m n irr# x rxf rflow
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain rel# (rgClassOf (rgFlow k m n x)))
        | eqPenalty-refl (Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain irr# (rgClassOf (rgFlow k m n x)))
  = refl

record RGFusedBundle : Set₁ where
  field
    fused : ∀ k n → RGState (k + n) → RGState n
    zero-is-flow :
      ∀ n (x : RGState n) →
      fused zero n x ≡ rgFlow zero (suc zero) n x
    basin-stable :
      ∀ k n (x : RGState (k + n)) →
      rgBasinLabel (fused k n x) ≡ rgBasinLabel x
    irrelevant-monotone :
      ∀ k n (x : RGState (k + n)) →
      rgIrrelevantSize (fused k n x) ≤ rgIrrelevantSize x
    rel-observable-stable :
      ∀ k n (x : RGState (k + n)) →
      rgObservableExprEval n rel# (rgClassOf (fused k n x)) ≡
      rgObservableExprEval (k + n) rel# (rgClassOf x)
    irr-observable-monotone :
      ∀ k n (x : RGState (k + n)) →
      rgObservableExprEval n irr# (rgClassOf (fused k n x)) ≤
      rgObservableExprEval (k + n) irr# (rgClassOf x)
    canonical-on-recovered :
      ∀ k n (x : RGState (k + n)) →
      PT.recoveredLaw (rgShellTheory n) (fused k n x) →
      rgClassOf (fused k n x) ≡ rgClassOf (rgVacuum n (rgBasinLabel x))
    canonical-observable :
      ∀ k n (O : RGObservableExpr) (x : RGState (k + n)) →
      PT.recoveredLaw (rgShellTheory n) (fused k n x) →
      rgObservableExprEval n O (rgClassOf (fused k n x)) ≡
      rgObservableExprEval n O (rgClassOf (rgVacuum n (rgBasinLabel x)))
    step-tail-canonical :
      ∀ k t n (x : RGState (k + n)) →
      PT.recoveredLaw (rgShellTheory n) (fused k n x) →
      rgClassOf (stepPow n t (fused k n x)) ≡
      rgClassOf (rgVacuum n (rgBasinLabel x))
    step-tail-canonical-observable :
      ∀ k t n (O : RGObservableExpr) (x : RGState (k + n)) →
      PT.recoveredLaw (rgShellTheory n) (fused k n x) →
      rgObservableExprEval n O (rgClassOf (stepPow n t (fused k n x))) ≡
      rgObservableExprEval n O (rgClassOf (rgVacuum n (rgBasinLabel x)))
    flow-basin-agree :
      ∀ k m n (x : RGState (k + n)) →
      rgBasinLabel (fused k n x) ≡ rgBasinLabel (rgFlow k m n x)
    flow-rel-observable-agree :
      ∀ k m n (x : RGState (k + n)) →
      rgObservableExprEval n rel# (rgClassOf (fused k n x)) ≡
      rgObservableExprEval n rel# (rgClassOf (rgFlow k m n x))
    stepPow-flow-basin-agree :
      ∀ k t n (x : RGState (k + n)) →
      rgBasinLabel (stepPow n t (fused k n x)) ≡
      rgBasinLabel (rgFlow k (suc t) n x)
    stepPow-flow-rel-observable-agree :
      ∀ k t n (x : RGState (k + n)) →
      rgObservableExprEval n rel# (rgClassOf (stepPow n t (fused k n x))) ≡
      rgObservableExprEval n rel# (rgClassOf (rgFlow k (suc t) n x))
    flow-rel-benchmark-agree :
      ∀ k m n gain (x : RGState (k + n)) →
      Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain rel# (rgClassOf (fused k n x)) ≡
      Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain rel# (rgClassOf (rgFlow k m n x))
    stepPow-flow-rel-benchmark-agree :
      ∀ k t n gain (x : RGState (k + n)) →
      Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain rel# (rgClassOf (stepPow n t (fused k n x))) ≡
      Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain rel# (rgClassOf (rgFlow k (suc t) n x))
    flow-recovered-same-class :
      ∀ k m n (x : RGState (k + n)) →
      PT.recoveredLaw (rgShellTheory n) (fused k n x) →
      PT.recoveredLaw (rgShellTheory n) (rgFlow k m n x) →
      rgClassOf (fused k n x) ≡ rgClassOf (rgFlow k m n x)
    flow-recovered-observable-agree :
      ∀ k m n (O : RGObservableExpr) (x : RGState (k + n)) →
      PT.recoveredLaw (rgShellTheory n) (fused k n x) →
      PT.recoveredLaw (rgShellTheory n) (rgFlow k m n x) →
      rgObservableExprEval n O (rgClassOf (fused k n x)) ≡
      rgObservableExprEval n O (rgClassOf (rgFlow k m n x))

rgFusedBundle : RGFusedBundle
rgFusedBundle =
  record
    { fused = rgFused
    ; zero-is-flow = rgFused-zero-is-flow
    ; basin-stable = rgFused-basin-stable
    ; irrelevant-monotone = rgFused-irrelevant-monotone
    ; rel-observable-stable = rgFused-rel-observable-stable
    ; irr-observable-monotone = rgFused-irr-observable-monotone
    ; canonical-on-recovered = rgFused-canonical-on-recovered
    ; canonical-observable = rgFused-canonical-observable
    ; step-tail-canonical = rgFused-step-tail-canonical
    ; step-tail-canonical-observable = rgFused-step-tail-canonical-observable
    ; flow-basin-agree = rgFused-flow-basin-agree
    ; flow-rel-observable-agree = rgFused-flow-rel-observable-agree
    ; stepPow-flow-basin-agree = rgFused-stepPow-flow-basin-agree
    ; stepPow-flow-rel-observable-agree = rgFused-stepPow-flow-rel-observable-agree
    ; flow-rel-benchmark-agree = rgFused-flow-rel-benchmark-agree
    ; stepPow-flow-rel-benchmark-agree = rgFused-stepPow-flow-rel-benchmark-agree
    ; flow-recovered-same-class = rgFused-flow-recovered-same-class
    ; flow-recovered-observable-agree = rgFused-flow-recovered-observable-agree
    }

record RGRenormalizationBundle : Set₁ where
  field
    renormalize : ∀ k n → RGState (k + n) → RGState n
    basin-stable :
      ∀ k n (x : RGState (k + n)) →
      rgBasinLabel (renormalize k n x) ≡ rgBasinLabel x
    irrelevant-monotone :
      ∀ k n (x : RGState (k + n)) →
      rgIrrelevantSize (renormalize k n x) ≤ rgIrrelevantSize x
    rel-observable-stable :
      ∀ k n (x : RGState (k + n)) →
      rgObservableExprEval n rel# (rgClassOf (renormalize k n x)) ≡
      rgObservableExprEval (k + n) rel# (rgClassOf x)
    irr-observable-monotone :
      ∀ k n (x : RGState (k + n)) →
      rgObservableExprEval n irr# (rgClassOf (renormalize k n x)) ≤
      rgObservableExprEval (k + n) irr# (rgClassOf x)

rgRenormalizationBundle : RGRenormalizationBundle
rgRenormalizationBundle =
  record
    { renormalize = rgRenormalize
    ; basin-stable = rgRenormalize-basin-stable
    ; irrelevant-monotone = rgRenormalize-irrelevant-monotone
    ; rel-observable-stable = rgRenormalize-rel-observable-stable
    ; irr-observable-monotone = rgRenormalize-irr-observable-monotone
    }

record RGFlowBundle : Set₁ where
  field
    flow : ∀ (k m n : Nat) → RGState (k + n) → RGState n
    basin-stable :
      ∀ (k m n : Nat) (x : RGState (k + n)) →
      rgBasinLabel (flow k m n x) ≡ rgBasinLabel x
    irrelevant-monotone :
      ∀ (k m n : Nat) (x : RGState (k + n)) →
      rgIrrelevantSize (flow k m n x) ≤ rgIrrelevantSize x
    rel-observable-stable :
      ∀ (k m n : Nat) (x : RGState (k + n)) →
      rgObservableExprEval n rel# (rgClassOf (flow k m n x)) ≡
      rgObservableExprEval (k + n) rel# (rgClassOf x)
    irr-observable-monotone :
      ∀ (k m n : Nat) (x : RGState (k + n)) →
      rgObservableExprEval n irr# (rgClassOf (flow k m n x)) ≤
      rgObservableExprEval (k + n) irr# (rgClassOf x)
    canonical-on-recovered :
      ∀ (k m n : Nat) (x : RGState (k + n)) →
      PT.recoveredLaw (rgShellTheory n) (flow k m n x) →
      rgClassOf (flow k m n x) ≡ rgClassOf (rgVacuum n (rgBasinLabel x))
    canonical-observable :
      ∀ (k m n : Nat) (O : RGObservableExpr) (x : RGState (k + n)) →
      PT.recoveredLaw (rgShellTheory n) (flow k m n x) →
      rgObservableExprEval n O (rgClassOf (flow k m n x)) ≡
      rgObservableExprEval n O (rgClassOf (rgVacuum n (rgBasinLabel x)))
    step-monotone :
      ∀ (k m n : Nat) (x : RGState (k + n)) →
      rgIrrelevantSize (flow k (suc m) n x) ≤
      rgIrrelevantSize (flow k m n x)
    irr-observable-step-monotone :
      ∀ (k m n : Nat) (x : RGState (k + n)) →
      rgObservableExprEval n irr# (rgClassOf (flow k (suc m) n x)) ≤
      rgObservableExprEval n irr# (rgClassOf (flow k m n x))
    irr-benchmark-step-monotone :
      ∀ (k m n gain : Nat) (x : RGState (k + n)) →
      Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain irr# (rgClassOf (flow k (suc m) n x)) ≤
      Bench.BenchmarkTheory′.predictB (rgBenchmarkTheory n) gain irr# (rgClassOf (flow k m n x))
    step-tail-canonical :
      ∀ (k m t n : Nat) (x : RGState (k + n)) →
      PT.recoveredLaw (rgShellTheory n) (flow k m n x) →
      rgClassOf (stepPow n t (flow k m n x)) ≡
      rgClassOf (rgVacuum n (rgBasinLabel x))
    step-tail-canonical-observable :
      ∀ (k m t n : Nat) (O : RGObservableExpr) (x : RGState (k + n)) →
      PT.recoveredLaw (rgShellTheory n) (flow k m n x) →
      rgObservableExprEval n O (rgClassOf (stepPow n t (flow k m n x))) ≡
      rgObservableExprEval n O (rgClassOf (rgVacuum n (rgBasinLabel x)))

rgFlowBundle : RGFlowBundle
rgFlowBundle =
  record
    { flow = rgFlow
    ; basin-stable = rgFlow-basin-stable
    ; irrelevant-monotone = rgFlow-irrelevant-monotone
    ; rel-observable-stable = rgFlow-rel-observable-stable
    ; irr-observable-monotone = rgFlow-irr-observable-monotone
    ; canonical-on-recovered = rgFlow-canonical-on-recovered
    ; canonical-observable = rgFlow-canonical-observable
    ; step-monotone = rgFlow-step-monotone
    ; irr-observable-step-monotone = rgFlow-irr-observable-step-monotone
    ; irr-benchmark-step-monotone = rgFlow-irr-benchmark-step-monotone
    ; step-tail-canonical = rgFlow-step-tail-canonical
    ; step-tail-canonical-observable = rgFlow-step-tail-canonical-observable
    }

record RGPhase2HierarchyBundle : Set₁ where
  field
    coarseBy : RGCoarseScheme → ∀ n → RGState (suc n) → RGState n
    stepBy : RGFlowMode → ∀ n → RGState n → RGState n
    fixedPointOfState : ∀ {n} → RGState n → RGFixedPoint
    canonicalFixedPoint : Bool → RGFixedPoint
    coarseBy-class :
      ∀ scheme n (x : RGState (suc n)) →
      rgClassOf (coarseBy scheme n x) ≡ rgCoarseClass n x
    coarseBy-rel-observable-stable :
      ∀ scheme n (x : RGState (suc n)) →
      rgObservableExprEval n rel# (rgClassOf (coarseBy scheme n x)) ≡
      rgObservableExprEval (suc n) rel# (rgClassOf x)
    coarseBy-irr-observable-monotone :
      ∀ scheme n (x : RGState (suc n)) →
      rgObservableExprEval n irr# (rgClassOf (coarseBy scheme n x)) ≤
      rgObservableExprEval (suc n) irr# (rgClassOf x)
    schemeFlow :
      ∀ (scheme : RGCoarseScheme) (mode : RGFlowMode) (k m n : Nat) → RGState (k + n) → RGState n
    schemeFlow-basin-stable :
      ∀ (scheme : RGCoarseScheme) (mode : RGFlowMode) (k m n : Nat) (x : RGState (k + n)) →
      rgBasinLabel (schemeFlow scheme mode k m n x) ≡ rgBasinLabel x
    schemeFlow-irrelevant-monotone :
      ∀ (scheme : RGCoarseScheme) (mode : RGFlowMode) (k m n : Nat) (x : RGState (k + n)) →
      rgIrrelevantSize (schemeFlow scheme mode k m n x) ≤ rgIrrelevantSize x
    schemeFlow-rel-observable-stable :
      ∀ (scheme : RGCoarseScheme) (mode : RGFlowMode) (k m n : Nat) (x : RGState (k + n)) →
      rgObservableExprEval n rel# (rgClassOf (schemeFlow scheme mode k m n x)) ≡
      rgObservableExprEval (k + n) rel# (rgClassOf x)
    schemeFlow-canonical-on-recovered :
      ∀ (scheme : RGCoarseScheme) (mode : RGFlowMode) (k m n : Nat) (x : RGState (k + n)) →
      PT.recoveredLaw (rgShellTheory n) (schemeFlow scheme mode k m n x) →
      rgClassOf (schemeFlow scheme mode k m n x) ≡
      rgClassOf (rgVacuum n (rgBasinLabel x))
    schemeFlow-fixedPoint-on-recovered :
      ∀ (scheme : RGCoarseScheme) (mode : RGFlowMode) (k m n : Nat) (x : RGState (k + n)) →
      PT.recoveredLaw (rgShellTheory n) (schemeFlow scheme mode k m n x) →
      fixedPointOfState (schemeFlow scheme mode k m n x) ≡
      canonicalFixedPoint (rgBasinLabel x)

rgPhase2HierarchyBundle : RGPhase2HierarchyBundle
rgPhase2HierarchyBundle =
  record
    { coarseBy = rgCoarseBy
    ; stepBy = rgStepBy
    ; fixedPointOfState = rgFixedPointOfState
    ; canonicalFixedPoint = rgCanonicalFixedPoint
    ; coarseBy-class = rgCoarseBy-class
    ; coarseBy-rel-observable-stable = rgCoarseByRelObservableStable
    ; coarseBy-irr-observable-monotone = rgCoarseByIrrelObservableMonotone
    ; schemeFlow = rgSchemeFlow
    ; schemeFlow-basin-stable = rgSchemeFlow-basin-stable
    ; schemeFlow-irrelevant-monotone = rgSchemeFlow-irrelevant-monotone
    ; schemeFlow-rel-observable-stable = rgSchemeFlow-rel-observable-stable
    ; schemeFlow-canonical-on-recovered = rgSchemeFlow-canonical-on-recovered
    ; schemeFlow-fixedPoint-on-recovered = rgSchemeFlow-fixedPoint-on-recovered
    }

rgRelevantPreserved :
  ∀ n (x : RGState n) →
  relevantMode (rgShellStep n x) ≡ relevantMode x
rgRelevantPreserved n (mkRGState r i) = refl

rgCoarseThenStepDefectContracts :
  ∀ n (x : RGState (suc n)) →
  PT.defectSize (rgShellTheory n) (PT.step (rgShellTheory n) (rgCoarse n x))
  ≤
  PT.defectSize (rgShellTheory n) (rgCoarse n x)
rgCoarseThenStepDefectContracts n x =
  PT.defect-monotone (rgShellTheory n) {x = rgCoarse n x} tt

rgCoarseProjectClassOnVacuum :
  ∀ n (r : Bool) →
  rgCoarseClass n (PT.step (rgShellTheory (suc n))
    (Ref.ApproxRefinementStep.embed (rgShellApproxRefinement n) (rgVacuum n r)))
  ≡
  SQ.classOf (rgQuotiented n) (rgVacuum n r)
rgCoarseProjectClassOnVacuum n r =
  cong (λ f → r , SC.supportVec f) (SC.refinement-stable-recovery n)

support-vacuum : ∀ n → SC.supportVec (SC.vacuum n) ≡ SC.supportVec (SC.vacuum n)
support-vacuum n = refl

rgRecovered-same-basin-same-class :
  ∀ n {x y : RGState n} →
  PT.recoveredLaw (rgShellTheory n) x →
  PT.recoveredLaw (rgShellTheory n) y →
  relevantMode x ≡ relevantMode y →
  rgClassOf x ≡ rgClassOf y
rgRecovered-same-basin-same-class n {x} {y} rx ry sameRelevant =
  cong₂ _,_ sameRelevant
    (trans (cong SC.supportVec rx)
           (trans (support-vacuum n)
                  (sym (cong SC.supportVec ry))))

rgRecovered-class-from-basin :
  ∀ n (r : Bool) {x : RGState n} →
  PT.recoveredLaw (rgShellTheory n) x →
  relevantMode x ≡ r →
  rgClassOf x ≡ rgClassOf (rgVacuum n r)
rgRecovered-class-from-basin n r {x} rx sameRelevant =
  rgRecovered-same-basin-same-class n rx refl sameRelevant

rgCanonicalClass : (n : Nat) → Bool → RGPhysState n
rgCanonicalClass n r = rgClassOf (rgVacuum n r)

rgRecovered-stepPow-canonical :
  ∀ n k (x : RGState n) →
  PT.recoveredLaw (rgShellTheory n) (stepPow n k x) →
  rgClassOf (stepPow n k x) ≡ rgCanonicalClass n (rgBasinLabel x)
rgRecovered-stepPow-canonical n k x rx =
  rgRecovered-class-from-basin n (rgBasinLabel x) rx (rgBasinLabel-stepPow n k x)

rgRecovered-stepPow-canonical-observable :
  ∀ n k (O : RGObservableExpr) (x : RGState n) →
  PT.recoveredLaw (rgShellTheory n) (stepPow n k x) →
  rgObservableExprEval n O (rgClassOf (stepPow n k x)) ≡
  rgObservableExprEval n O (rgCanonicalClass n (rgBasinLabel x))
rgRecovered-stepPow-canonical-observable n k O x rx =
  cong (rgObservableExprEval n O) (rgRecovered-stepPow-canonical n k x rx)

rgRecovered-step :
  ∀ n {x : RGState n} →
  PT.recoveredLaw (rgShellTheory n) x →
  PT.recoveredLaw (rgShellTheory n) (rgShellStep n x)
rgRecovered-step n {mkRGState r i} rx rewrite rx = SC.relaxSym-vacuum n

rgRecovered-fixed :
  ∀ n {x : RGState n} →
  PT.recoveredLaw (rgShellTheory n) x →
  rgShellStep n x ≡ x
rgRecovered-fixed n {mkRGState r i} rx rewrite rx =
  cong (mkRGState r) (SC.relaxSym-vacuum n)

rgRecovered-stepPow-id :
  ∀ n k {x : RGState n} →
  PT.recoveredLaw (rgShellTheory n) x →
  stepPow n k x ≡ x
rgRecovered-stepPow-id n zero rx = refl
rgRecovered-stepPow-id n (suc k) {x} rx =
  trans (cong (rgShellStep n) (rgRecovered-stepPow-id n k rx))
        (rgRecovered-fixed n rx)

rgRecovered-stepPow-from :
  ∀ n k (x : RGState n) →
  PT.recoveredLaw (rgShellTheory n) x →
  PT.recoveredLaw (rgShellTheory n) (stepPow n k x)
rgRecovered-stepPow-from n k x rx =
  trans (cong irrelevantMode (rgRecovered-stepPow-id n k rx)) rx

rgRecovered-stepPow-tail-canonical :
  ∀ n k m (x : RGState n) →
  PT.recoveredLaw (rgShellTheory n) (stepPow n k x) →
  rgClassOf (stepPow n m (stepPow n k x)) ≡ rgCanonicalClass n (rgBasinLabel x)
rgRecovered-stepPow-tail-canonical n k m x rx =
  rgRecovered-class-from-basin
    n
    (rgBasinLabel x)
    (rgRecovered-stepPow-from n m (stepPow n k x) rx)
    (trans (rgBasinLabel-stepPow n m (stepPow n k x))
           (rgBasinLabel-stepPow n k x))

rgRecovered-stepPow-tail-canonical-observable :
  ∀ n k m (O : RGObservableExpr) (x : RGState n) →
  PT.recoveredLaw (rgShellTheory n) (stepPow n k x) →
  rgObservableExprEval n O (rgClassOf (stepPow n m (stepPow n k x))) ≡
  rgObservableExprEval n O (rgCanonicalClass n (rgBasinLabel x))
rgRecovered-stepPow-tail-canonical-observable n k m O x rx =
  cong (rgObservableExprEval n O) (rgRecovered-stepPow-tail-canonical n k m x rx)

rgRecovered-observables-depend-only-on-relevant :
  ∀ n (O : RGObservableExpr) {x y : RGState n} →
  PT.recoveredLaw (rgShellTheory n) x →
  PT.recoveredLaw (rgShellTheory n) y →
  relevantMode x ≡ relevantMode y →
  rgObservableExprEval n O (rgClassOf x) ≡ rgObservableExprEval n O (rgClassOf y)
rgRecovered-observables-depend-only-on-relevant n rel# rx ry sameRelevant =
  cong relevantAsNat sameRelevant
rgRecovered-observables-depend-only-on-relevant n irr# rx ry sameRelevant =
  cong SC.countTrueVec
    (trans (cong SC.supportVec rx)
           (sym (cong SC.supportVec ry)))
rgRecovered-observables-depend-only-on-relevant n zeroO rx ry sameRelevant = refl
rgRecovered-observables-depend-only-on-relevant n (x +RG y) rx ry sameRelevant =
  cong₂ _+_
    (rgRecovered-observables-depend-only-on-relevant n x rx ry sameRelevant)
    (rgRecovered-observables-depend-only-on-relevant n y rx ry sameRelevant)
rgRecovered-observables-depend-only-on-relevant n (scaleRG k x) rx ry sameRelevant =
  cong (k *_)
    (rgRecovered-observables-depend-only-on-relevant n x rx ry sameRelevant)

rgUniversalityObservableCollapse :
  ∀ n (O : RGObservableExpr) (r : Bool) {x : RGState n} →
  PT.recoveredLaw (rgShellTheory n) x →
  relevantMode x ≡ r →
  rgObservableExprEval n O (rgClassOf x) ≡
  rgObservableExprEval n O (rgClassOf (rgVacuum n r))
rgUniversalityObservableCollapse n O r {x} rx sameRelevant =
  rgRecovered-observables-depend-only-on-relevant n O rx refl sameRelevant

data RGOperator : Set where
  hold evolve : RGOperator

rgOperatorWitness : (n : Nat) → LW.OperatorWitness (rgShellTheory n)
rgOperatorWitness n =
  record
    { Operator = RGOperator
    ; apply = λ where
        hold x → x
        evolve x → rgShellStep n x
    ; unitOp = hold
    ; compose = λ where
        hold op₂ → op₂
        evolve hold → evolve
        evolve evolve → evolve
    ; preservesInv = λ _ _ → tt
    }

rgScalingWitness : LW.ScalingWitness rgTower
rgScalingWitness =
  record
    { coarse-defect≤fine = λ n x → SC.countNonZero-dropLast (irrelevantMode x)
    }

rgLocalWitness : (n : Nat) → LW.LocalTheoryWitness (rgShellTheory n) rgTower (rgQuotiented n) (rgObservableTheory n)
rgLocalWitness n =
  record
    { operators = rgOperatorWitness n
    ; scaling = rgScalingWitness
    ; obsInvariant = rgObservableInvariant n
    }

rgFixed⇒recovered :
  ∀ n {x : RGState n} →
  PT.fixed (rgShellTheory n) x →
  PT.recoveredLaw (rgShellTheory n) x
rgFixed⇒recovered n {x} fx =
  SC.fixed⇒recovered n {x = irrelevantMode x} (cong irrelevantMode fx)

rgRecovered-refines :
  ∀ n {x : RGState (suc n)} →
  PT.recoveredLaw (rgShellTheory (suc n)) x →
  PT.recoveredLaw (rgShellTheory n)
    (Ref.ApproxRefinementStep.project (rgShellApproxRefinement n) x)
rgRecovered-refines n {x} rx =
  SC.recovered-refines n {x = irrelevantMode x} rx

rgObservable-stable :
  ∀ n (r : Bool) →
  Obs.ObservableTheory.eval (rgObservableTheory n) relevantObs (SQ.classOf (rgQuotiented n) (rgVacuum n r))
  ≡
  Obs.ObservableTheory.eval (rgObservableTheory (suc n)) relevantObs (SQ.classOf (rgQuotiented (suc n)) (rgVacuum (suc n) r))
rgObservable-stable n r = refl

rgRefinement-stable-recovery :
  ∀ n (r : Bool) →
  PT.recoveredLaw (rgShellTheory n)
    (Ref.ApproxRefinementStep.project (rgShellApproxRefinement n)
      (PT.step (rgShellTheory (suc n))
        (Ref.ApproxRefinementStep.embed (rgShellApproxRefinement n) (rgVacuum n r))))
rgRefinement-stable-recovery n r = SC.refinement-stable-recovery n
