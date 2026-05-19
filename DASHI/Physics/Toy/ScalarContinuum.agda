module DASHI.Physics.Toy.ScalarContinuum where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; replicate; map)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

open import DASHI.Algebra.Trit using (Trit; zer)
import DASHI.Algebra.Trit as T
open import DASHI.Physics.PhysicalTheory as PT
open import DASHI.Physics.Refinement as Ref
import DASHI.Physics.SymmetryQuotient as SQ
open import DASHI.Physics.Observable as Obs
open import DASHI.Physics.LocalWitness as LW

Carrier : Nat → Set
Carrier n = Vec Trit (suc n)

Support : Nat → Set
Support n = Vec Bool (suc n)

vacuum : (n : Nat) → Carrier n
vacuum n = replicate (suc n) zer

countNonZeroVec : ∀ {n : Nat} → Vec Trit n → Nat
countNonZeroVec [] = zero
countNonZeroVec (zer ∷ xs) = countNonZeroVec xs
countNonZeroVec (_ ∷ xs) = suc (countNonZeroVec xs)

countNonZero : ∀ {n : Nat} → Carrier n → Nat
countNonZero = countNonZeroVec

countNonZero-vacuum : ∀ n → countNonZero (vacuum n) ≡ zero
countNonZero-vacuum zero = refl
countNonZero-vacuum (suc n) = countNonZero-vacuum n

countTrueVec : ∀ {n : Nat} → Vec Bool n → Nat
countTrueVec [] = zero
countTrueVec (false ∷ xs) = countTrueVec xs
countTrueVec (true ∷ xs) = suc (countTrueVec xs)

supportTrit : Trit → Bool
supportTrit zer = false
supportTrit _ = true

supportVec : ∀ {n : Nat} → Carrier n → Support n
supportVec = map supportTrit

countTrue-supportVecN :
  ∀ {n : Nat} (x : Vec Trit n) →
  countTrueVec (map supportTrit x) ≡ countNonZeroVec x
countTrue-supportVecN [] = refl
countTrue-supportVecN (zer ∷ xs) = countTrue-supportVecN xs
countTrue-supportVecN (T.neg ∷ xs) = cong suc (countTrue-supportVecN xs)
countTrue-supportVecN (T.pos ∷ xs) = cong suc (countTrue-supportVecN xs)

countTrue-supportVec :
  ∀ {n : Nat} (x : Carrier n) →
  countTrueVec (supportVec x) ≡ countNonZero x
countTrue-supportVec = countTrue-supportVecN

flipTrit : Trit → Trit
flipTrit = T.inv

flipVecN : ∀ {n : Nat} → Vec Trit n → Vec Trit n
flipVecN = map flipTrit

flipVec : ∀ {n : Nat} → Carrier n → Carrier n
flipVec = flipVecN

flip-vacuum : ∀ n → flipVec (vacuum n) ≡ vacuum n
flip-vacuum zero = refl
flip-vacuum (suc n) = cong (zer ∷_) (flip-vacuum n)

support-flipTrit : ∀ t → supportTrit (flipTrit t) ≡ supportTrit t
support-flipTrit zer = refl
support-flipTrit T.neg = refl
support-flipTrit T.pos = refl

support-flipVec : ∀ {n : Nat} (x : Carrier n) → supportVec x ≡ supportVec (flipVec x)
support-flipVec {zero} (x ∷ []) = cong (λ b → b ∷ []) (sym (support-flipTrit x))
support-flipVec {suc n} (x ∷ y ∷ xs) =
  cong₂ _∷_ (sym (support-flipTrit x)) (support-flipVec (y ∷ xs))

headVec : ∀ {m} {A : Set} → Vec A (suc m) → A
headVec (h ∷ _) = h

tailVec : ∀ {m} {A : Set} → Vec A (suc m) → Vec A m
tailVec (_ ∷ t) = t

dropLast : ∀ {n : Nat} → Carrier (suc n) → Carrier n
dropLast {zero} (x ∷ y ∷ []) = x ∷ []
dropLast {suc n} (x ∷ y ∷ xs) = x ∷ dropLast (y ∷ xs)

appendZeroVec : ∀ {n : Nat} → Vec Trit n → Vec Trit (suc n)
appendZeroVec [] = zer ∷ []
appendZeroVec (x ∷ xs) = x ∷ appendZeroVec xs

appendZero : ∀ {n : Nat} → Carrier n → Carrier (suc n)
appendZero = appendZeroVec

appendZero-vacuum : ∀ n → appendZero (vacuum n) ≡ vacuum (suc n)
appendZero-vacuum zero = refl
appendZero-vacuum (suc n) = cong (zer ∷_) (appendZero-vacuum n)

dropLast-appendZeroVec :
  ∀ {n : Nat} (x : Vec Trit (suc n)) →
  dropLast (appendZeroVec x) ≡ x
dropLast-appendZeroVec {zero} (x ∷ []) = refl
dropLast-appendZeroVec {suc n} (x ∷ y ∷ xs) =
  cong (x ∷_) (dropLast-appendZeroVec {n} (y ∷ xs))

countNonZero-dropLast :
  ∀ {n : Nat} (x : Carrier (suc n)) →
  countNonZero (dropLast x) ≤ countNonZero x
countNonZero-dropLast {zero} (x ∷ y ∷ []) with x
... | zer = z≤n
... | T.neg = s≤s z≤n
... | T.pos = s≤s z≤n
countNonZero-dropLast {suc n} (zer ∷ y ∷ xs) = countNonZero-dropLast (y ∷ xs)
countNonZero-dropLast {suc n} (T.neg ∷ y ∷ xs) = s≤s (countNonZero-dropLast (y ∷ xs))
countNonZero-dropLast {suc n} (T.pos ∷ y ∷ xs) = s≤s (countNonZero-dropLast (y ∷ xs))

≤-step : ∀ {m n : Nat} → m ≤ n → m ≤ suc n
≤-step z≤n = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

gate : Trit → Trit → Trit
gate zer zer = zer
gate zer T.neg = zer
gate zer T.pos = zer
gate T.neg zer = zer
gate T.neg T.neg = T.neg
gate T.neg T.pos = zer
gate T.pos zer = zer
gate T.pos T.neg = zer
gate T.pos T.pos = T.pos

gate-zero-left : ∀ right → gate zer right ≡ zer
gate-zero-left zer = refl
gate-zero-left T.neg = refl
gate-zero-left T.pos = refl

gate-inv : ∀ a b → gate (flipTrit a) (flipTrit b) ≡ flipTrit (gate a b)
gate-inv zer zer = refl
gate-inv zer T.neg = refl
gate-inv zer T.pos = refl
gate-inv T.neg zer = refl
gate-inv T.neg T.neg = refl
gate-inv T.neg T.pos = refl
gate-inv T.pos zer = refl
gate-inv T.pos T.neg = refl
gate-inv T.pos T.pos = refl

centerGate : Trit → Trit → Trit → Trit
centerGate left x right = gate (gate left x) right

centerGate-inv :
  ∀ left x right →
  centerGate (flipTrit left) (flipTrit x) (flipTrit right)
  ≡
  flipTrit (centerGate left x right)
centerGate-inv left x right =
  trans (cong (λ z → gate z (flipTrit right)) (gate-inv left x))
        (gate-inv (gate left x) right)

centerGate-zero-left : ∀ x right → centerGate zer x right ≡ zer
centerGate-zero-left zer zer = refl
centerGate-zero-left zer T.neg = refl
centerGate-zero-left zer T.pos = refl
centerGate-zero-left T.neg zer = refl
centerGate-zero-left T.neg T.neg = refl
centerGate-zero-left T.neg T.pos = refl
centerGate-zero-left T.pos zer = refl
centerGate-zero-left T.pos T.neg = refl
centerGate-zero-left T.pos T.pos = refl

centerGate-right-zero : ∀ left x → centerGate left x zer ≡ zer
centerGate-right-zero zer zer = refl
centerGate-right-zero zer T.neg = refl
centerGate-right-zero zer T.pos = refl
centerGate-right-zero T.neg zer = refl
centerGate-right-zero T.neg T.neg = refl
centerGate-right-zero T.neg T.pos = refl
centerGate-right-zero T.pos zer = refl
centerGate-right-zero T.pos T.neg = refl
centerGate-right-zero T.pos T.pos = refl

centerGate-middle-zero : ∀ left right → centerGate left zer right ≡ zer
centerGate-middle-zero zer zer = refl
centerGate-middle-zero zer T.neg = refl
centerGate-middle-zero zer T.pos = refl
centerGate-middle-zero T.neg zer = refl
centerGate-middle-zero T.neg T.neg = refl
centerGate-middle-zero T.neg T.pos = refl
centerGate-middle-zero T.pos zer = refl
centerGate-middle-zero T.pos T.neg = refl
centerGate-middle-zero T.pos T.pos = refl

centerGate-from-inner-zero :
  ∀ left x right →
  gate left x ≡ zer →
  centerGate left x right ≡ zer
centerGate-from-inner-zero left x right inner rewrite inner = gate-zero-left right

centerGate-zero-fixed→zero :
  ∀ x right →
  centerGate zer x right ≡ x →
  x ≡ zer
centerGate-zero-fixed→zero zer right _ = refl
centerGate-zero-fixed→zero T.neg zer ()
centerGate-zero-fixed→zero T.neg T.neg ()
centerGate-zero-fixed→zero T.neg T.pos ()
centerGate-zero-fixed→zero T.pos zer ()
centerGate-zero-fixed→zero T.pos T.neg ()
centerGate-zero-fixed→zero T.pos T.pos ()

relaxSymVec : ∀ {n : Nat} → Trit → Vec Trit n → Vec Trit n
relaxSymVec left [] = []
relaxSymVec left (x ∷ []) = centerGate left x zer ∷ []
relaxSymVec left (x ∷ y ∷ xs) = centerGate left x y ∷ relaxSymVec x (y ∷ xs)

flip-relaxSymVec :
  ∀ {n : Nat} left (x : Vec Trit n) →
  flipVecN (relaxSymVec left x) ≡ relaxSymVec (flipTrit left) (flipVecN x)
flip-relaxSymVec left [] = refl
flip-relaxSymVec left (x ∷ []) = cong (λ h → h ∷ []) (sym (centerGate-inv left x zer))
flip-relaxSymVec left (x ∷ y ∷ xs) =
  cong₂ _∷_ (sym (centerGate-inv left x y)) (flip-relaxSymVec x (y ∷ xs))

{-# TERMINATING #-}
countNonZero-relaxSymVec :
  ∀ {n : Nat} (left : Trit) (x : Vec Trit n) →
  countNonZeroVec (relaxSymVec left x) ≤ countNonZeroVec x
countNonZero-relaxSymVec left [] = z≤n
countNonZero-relaxSymVec left (x ∷ []) rewrite centerGate-right-zero left x = z≤n
countNonZero-relaxSymVec left (zer ∷ y ∷ xs)
  rewrite centerGate-middle-zero left y
  = countNonZero-relaxSymVec zer (y ∷ xs)
countNonZero-relaxSymVec zer (T.neg ∷ y ∷ xs)
  rewrite centerGate-zero-left T.neg y
  = ≤-step (countNonZero-relaxSymVec T.neg (y ∷ xs))
countNonZero-relaxSymVec zer (T.pos ∷ y ∷ xs)
  rewrite centerGate-zero-left T.pos y
  = ≤-step (countNonZero-relaxSymVec T.pos (y ∷ xs))
countNonZero-relaxSymVec T.neg (T.neg ∷ zer ∷ xs)
  rewrite centerGate-right-zero T.neg T.neg
  = ≤-step (countNonZero-relaxSymVec T.neg (zer ∷ xs))
countNonZero-relaxSymVec T.neg (T.neg ∷ T.neg ∷ xs) = s≤s (countNonZero-relaxSymVec T.neg (T.neg ∷ xs))
countNonZero-relaxSymVec T.neg (T.neg ∷ T.pos ∷ xs) = ≤-step (countNonZero-relaxSymVec T.neg (T.pos ∷ xs))
countNonZero-relaxSymVec T.neg (T.pos ∷ y ∷ xs)
  rewrite centerGate-from-inner-zero T.neg T.pos y refl
  = ≤-step (countNonZero-relaxSymVec T.pos (y ∷ xs))
countNonZero-relaxSymVec T.pos (T.neg ∷ y ∷ xs)
  rewrite centerGate-from-inner-zero T.pos T.neg y refl
  = ≤-step (countNonZero-relaxSymVec T.neg (y ∷ xs))
countNonZero-relaxSymVec T.pos (T.pos ∷ zer ∷ xs)
  rewrite centerGate-right-zero T.pos T.pos
  = ≤-step (countNonZero-relaxSymVec T.pos (zer ∷ xs))
countNonZero-relaxSymVec T.pos (T.pos ∷ T.neg ∷ xs) = ≤-step (countNonZero-relaxSymVec T.pos (T.neg ∷ xs))
countNonZero-relaxSymVec T.pos (T.pos ∷ T.pos ∷ xs) = s≤s (countNonZero-relaxSymVec T.pos (T.pos ∷ xs))

relaxSym-fixed→vacuum :
  ∀ {n : Nat} (x : Carrier n) →
  relaxSymVec zer x ≡ x →
  x ≡ vacuum n
relaxSym-fixed→vacuum {zero} (x ∷ []) eq =
  cong (λ h → h ∷ []) (centerGate-zero-fixed→zero x zer (cong headVec eq))
relaxSym-fixed→vacuum {suc n} (x ∷ y ∷ xs) eq
  with centerGate-zero-fixed→zero x y (cong headVec eq)
... | headZero rewrite headZero =
  cong₂ _∷_ refl (relaxSym-fixed→vacuum (y ∷ xs) (cong tailVec eq))

TailApprox : ∀ {n : Nat} → Carrier n → Carrier n → Set
TailApprox {zero} x y = ⊤
TailApprox {suc n} (x ∷ xs) (y ∷ ys) = x ≡ y × TailApprox xs ys

relaxSym-dropLast-unfold :
  ∀ {n : Nat} (left x y : Trit) (zs : Vec Trit (suc n)) →
  relaxSymVec left (x ∷ dropLast (y ∷ zs))
  ≡
  centerGate left x y ∷ relaxSymVec x (dropLast (y ∷ zs))
relaxSym-dropLast-unfold {zero} left x y (z ∷ []) = refl
relaxSym-dropLast-unfold {suc n} left x y (z ∷ w ∷ zs) = refl

dropLast-relaxSym≈-with :
  ∀ {n : Nat} (left : Trit) (x : Carrier (suc n)) →
  TailApprox (dropLast (relaxSymVec left x)) (relaxSymVec left (dropLast x))
dropLast-relaxSym≈-with {zero} left (x ∷ y ∷ []) = tt
dropLast-relaxSym≈-with {suc n} left (x ∷ y ∷ z ∷ xs) rewrite relaxSym-dropLast-unfold left x y (z ∷ xs) =
  refl , dropLast-relaxSym≈-with x (y ∷ z ∷ xs)

project-vacuum : ∀ n → dropLast (vacuum (suc n)) ≡ vacuum n
project-vacuum zero = refl
project-vacuum (suc n) = cong (zer ∷_) (project-vacuum n)

relaxSym-vacuum : ∀ n → relaxSymVec zer (vacuum n) ≡ vacuum n
relaxSym-vacuum zero = refl
relaxSym-vacuum (suc n) = cong (zer ∷_) (relaxSym-vacuum n)

scalarStep : (n : Nat) → Carrier n → Carrier n
scalarStep n x = relaxSymVec zer x

scalarDefectMonotone :
  ∀ n {x : Carrier n} →
  countNonZero (scalarStep n x) ≤ countNonZero x
scalarDefectMonotone n {x} = countNonZero-relaxSymVec zer x

scalarTheory : (n : Nat) → PT.PhysicalTheory lzero
scalarTheory n =
  record
    { State = Carrier n
    ; step = scalarStep n
    ; Defect = λ _ → ⊤
    ; defectSize = countNonZero
    ; Inv = λ _ → ⊤
    ; inv-step = λ _ → tt
    ; defect-monotone = λ {x} _ → scalarDefectMonotone n {x}
    ; fixed = λ x → scalarStep n x ≡ x
    ; recoveredLaw = λ x → x ≡ vacuum n
    }

scalarApproxRefinement : (n : Nat) → Ref.ApproxRefinementStep (scalarTheory n) (scalarTheory (suc n))
scalarApproxRefinement n =
  record
    { project = dropLast
    ; embed = appendZero
    ; approxEq₀ = TailApprox
    ; commute-project≈ = λ x → dropLast-relaxSym≈-with zer x
    }

scalarTower : Ref.RefinementTower lzero
scalarTower =
  record
    { TheoryAt = scalarTheory
    ; refine = scalarApproxRefinement
    }

scalarAct : ∀ {n : Nat} → Bool → Carrier n → Carrier n
scalarAct false x = x
scalarAct true x = flipVec x

scalarStep-equivariant :
  ∀ n g x →
  scalarStep n (scalarAct g x) ≡ scalarAct g (scalarStep n x)
scalarStep-equivariant n false x = refl
scalarStep-equivariant n true x = sym (flip-relaxSymVec zer x)

scalarSymmetric : (n : Nat) → SQ.SymmetricTheory lzero
scalarSymmetric n =
  record
    { base = scalarTheory n
    ; Group = Bool
    ; act = scalarAct
    ; step-equivariant = scalarStep-equivariant n
    ; inv-invariant = λ _ _ _ → tt
    }

scalarPhysEq : (n : Nat) → SQ.PhysicalEquivalence (scalarSymmetric n)
scalarPhysEq n =
  record
    { _≈phys_ = λ x y → (x ≡ y) ⊎ (flipVec x ≡ y)
    ; orbit→phys = λ where
        false x → inj₁ refl
        true  x → inj₂ refl
    ; step-respects = λ where
        {x} {y} (inj₁ eq) → inj₁ (cong (scalarStep n) eq)
        {x} {y} (inj₂ eq) →
          inj₂ (trans (sym (scalarStep-equivariant n true x))
                      (cong (scalarStep n) eq))
    }

scalarClass-sound :
  ∀ {n : Nat} (x y : Carrier n) →
  SQ.PhysicalEquivalence._≈phys_ (scalarPhysEq n) x y →
  supportVec x ≡ supportVec y
scalarClass-sound x y (inj₁ eq) = cong supportVec eq
scalarClass-sound x y (inj₂ eq) = trans (support-flipVec x) (cong supportVec eq)

scalarQuotiented : (n : Nat) → SQ.QuotientedTheory lzero
scalarQuotiented n =
  record
    { sym = scalarSymmetric n
    ; physEq = scalarPhysEq n
    ; PhysState = Support n
    ; repr = λ _ → vacuum n
    ; classOf = supportVec
    ; class-sound = scalarClass-sound
    }

data ScalarObservable : Set where
  totalSupport : ScalarObservable

scalarObservableTheory : (n : Nat) → Obs.ObservableTheory (scalarQuotiented n)
scalarObservableTheory n =
  record
    { Observable = ScalarObservable
    ; Value = λ where totalSupport → Nat
    ; eval = λ where totalSupport x → countTrueVec x
    }

scalarObservableInvariant :
  (n : Nat) → Obs.SymmetryInvariantObservables (scalarQuotiented n) (scalarObservableTheory n)
scalarObservableInvariant n =
  record
    { eval-well-defined = λ where
        totalSupport x y eq → cong countTrueVec eq
    }

data ScalarOperator : Set where
  hold evolve : ScalarOperator

scalarOperatorWitness : (n : Nat) → LW.OperatorWitness (scalarTheory n)
scalarOperatorWitness n =
  record
    { Operator = ScalarOperator
    ; apply = λ where
        hold x → x
        evolve x → scalarStep n x
    ; unitOp = hold
    ; compose = λ where
        hold op₂ → op₂
        evolve hold → evolve
        evolve evolve → evolve
    ; preservesInv = λ _ _ → tt
    }

scalarScalingWitness : LW.ScalingWitness scalarTower
scalarScalingWitness =
  record
    { coarse-defect≤fine = λ n x → countNonZero-dropLast x
    }

scalarLocalWitness : (n : Nat) → LW.LocalTheoryWitness (scalarTheory n) scalarTower (scalarQuotiented n) (scalarObservableTheory n)
scalarLocalWitness n =
  record
    { operators = scalarOperatorWitness n
    ; scaling = scalarScalingWitness
    ; obsInvariant = scalarObservableInvariant n
    }

fixed⇒recovered :
  ∀ n {x : Carrier n} →
  PT.fixed (scalarTheory n) x →
  PT.recoveredLaw (scalarTheory n) x
fixed⇒recovered n {x} fx = relaxSym-fixed→vacuum x fx

recovered-refines :
  ∀ n {x : Carrier (suc n)} →
  PT.recoveredLaw (scalarTheory (suc n)) x →
  PT.recoveredLaw (scalarTheory n) (dropLast x)
recovered-refines n {x} rx = trans (cong dropLast rx) (project-vacuum n)

observable-vacuum-stable :
  ∀ n →
  Obs.ObservableTheory.eval (scalarObservableTheory n) totalSupport (SQ.classOf (scalarQuotiented n) (vacuum n))
  ≡
  Obs.ObservableTheory.eval (scalarObservableTheory (suc n)) totalSupport (SQ.classOf (scalarQuotiented (suc n)) (vacuum (suc n)))
observable-vacuum-stable n = refl

refinement-stable-recovery :
  ∀ n →
  PT.recoveredLaw (scalarTheory n)
    (dropLast (PT.step (scalarTheory (suc n)) (appendZero (vacuum n))))
refinement-stable-recovery n =
  trans
    (cong dropLast
      (trans (cong (relaxSymVec zer) (appendZero-vacuum n))
             (relaxSym-vacuum (suc n))))
    (project-vacuum n)
