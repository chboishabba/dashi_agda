module DASHI.Analysis.RiemannFiniteExplicitFormulaBoundary where

-- Exact boundary between the computable tracked-prime truncation and the full
-- prime-power term in the Riemann explicit formula.  A finite computation may
-- be promoted only after an explicit tail witness is supplied.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.RiemannPrimePowerArithmetic

cong :
  {A B : Set} →
  (f : A → B) →
  {x y : A} →
  x ≡ y →
  f x ≡ f y
cong f refl = refl

record TrackedPrimePowerLimitBridge
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space)
  (kernel : PrimePowerKernel space) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  field
    primePowerTail : Nat → Test → Scalar

    PrimePowerTailDefined : Nat → Test → Set
    TailConvergesToZero : Test → Set
    AllPrimeLanesRecovered : Set

    primePowerTailDefined :
      (cutoff : Nat) →
      (f : Test) →
      admissible f →
      PrimePowerTailDefined cutoff f

    fullPrimePowerDecomposition :
      (cutoff : Nat) →
      (f : Test) →
      admissible f →
      primePowerTerm f
      ≡
      (trackedPrimePowerTerm space kernel cutoff f
       +S primePowerTail cutoff f)

    tailConvergesToZero :
      (f : Test) →
      admissible f →
      TailConvergesToZero f

    allPrimeLanesRecovered : AllPrimeLanesRecovered

    addZeroRight :
      (x : Scalar) →
      (x +S zeroS) ≡ x

finiteCutoffExactWhenTailZero :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  (kernel : PrimePowerKernel space) →
  (bridge : TrackedPrimePowerLimitBridge space formula kernel) →
  (cutoff : Nat) →
  (f : WeilTestSpace.Test space) →
  WeilTestSpace.admissible space f →
  TrackedPrimePowerLimitBridge.primePowerTail bridge cutoff f
    ≡ WeilTestSpace.zeroS space →
  RiemannExplicitFormula.primePowerTerm formula f
    ≡ trackedPrimePowerTerm space kernel cutoff f
finiteCutoffExactWhenTailZero space formula kernel bridge cutoff f admissibleF tailZero =
  ≡-trans
    (TrackedPrimePowerLimitBridge.fullPrimePowerDecomposition bridge
      cutoff f admissibleF)
    (≡-trans
      (cong
        (λ tail →
          WeilTestSpace._+S_ space
            (trackedPrimePowerTerm space kernel cutoff f)
            tail)
        tailZero)
      (TrackedPrimePowerLimitBridge.addZeroRight bridge
        (trackedPrimePowerTerm space kernel cutoff f)))

record FiniteExplicitFormulaPromotionBoundary : Set where
  field
    finiteTrackedPrimePositivityIsNotUniversal : ⊤
    finiteExponentPositivityIsNotTailControl : ⊤
    boundedZeroSearchIsNotDensity : ⊤
    exactTailOrLimitBridgeRequired : ⊤
    noFiniteTruncationToRHInference : ⊤

finiteExplicitFormulaPromotionBoundary :
  FiniteExplicitFormulaPromotionBoundary
finiteExplicitFormulaPromotionBoundary = record
  { finiteTrackedPrimePositivityIsNotUniversal = tt
  ; finiteExponentPositivityIsNotTailControl = tt
  ; boundedZeroSearchIsNotDensity = tt
  ; exactTailOrLimitBridgeRequired = tt
  ; noFiniteTruncationToRHInference = tt
  }
