module DASHI.Analysis.RiemannVonMangoldtPrimeSide where

-- Exact finite partial sums of the all-prime von Mangoldt specification, plus
-- the tail bridge required to recover the full prime-power term of the Riemann
-- explicit formula.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.RiemannVonMangoldtSpecification

cong :
  {A B : Set} →
  (f : A → B) →
  {x y : A} →
  x ≡ y →
  f x ≡ f y
cong f refl = refl

vonMangoldtPartialSum :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  VonMangoldtFunction space arithmetic →
  Nat →
  WeilTestSpace.Test space →
  WeilTestSpace.Scalar space
vonMangoldtPartialSum space arithmetic mangoldt zero f =
  WeilTestSpace.zeroS space
vonMangoldtPartialSum space arithmetic mangoldt (suc cutoff) f =
  WeilTestSpace._+S_ space
    (vonMangoldtSampleTerm space arithmetic mangoldt f (suc cutoff))
    (vonMangoldtPartialSum space arithmetic mangoldt cutoff f)

record VonMangoldtPrimeSideLimit
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space)
  (arithmetic : AllPrimeArithmetic space)
  (mangoldt : VonMangoldtFunction space arithmetic) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  field
    tail : Nat → Test → Scalar

    TailDefined : Nat → Test → Set
    TailConvergesToZero : Test → Set
    PrimeSeriesConverges : Test → Set

    tailDefined :
      (cutoff : Nat) →
      (f : Test) →
      admissible f →
      TailDefined cutoff f

    primeSeriesConverges :
      (f : Test) →
      admissible f →
      PrimeSeriesConverges f

    tailConvergesToZero :
      (f : Test) →
      admissible f →
      TailConvergesToZero f

    primePowerTermDecomposition :
      (cutoff : Nat) →
      (f : Test) →
      admissible f →
      primePowerTerm f
      ≡
      (vonMangoldtPartialSum space arithmetic mangoldt cutoff f
       +S tail cutoff f)

    addZeroRight :
      (x : Scalar) →
      (x +S zeroS) ≡ x

finiteVonMangoldtSumExactWhenTailZero :
  (space : WeilTestSpace) →
  (formula : RiemannExplicitFormula space) →
  (arithmetic : AllPrimeArithmetic space) →
  (mangoldt : VonMangoldtFunction space arithmetic) →
  (limit : VonMangoldtPrimeSideLimit space formula arithmetic mangoldt) →
  (cutoff : Nat) →
  (f : WeilTestSpace.Test space) →
  WeilTestSpace.admissible space f →
  VonMangoldtPrimeSideLimit.tail limit cutoff f
    ≡ WeilTestSpace.zeroS space →
  RiemannExplicitFormula.primePowerTerm formula f
    ≡ vonMangoldtPartialSum space arithmetic mangoldt cutoff f
finiteVonMangoldtSumExactWhenTailZero
  space formula arithmetic mangoldt limit cutoff f admissibleF tailZero =
  ≡-trans
    (VonMangoldtPrimeSideLimit.primePowerTermDecomposition limit
      cutoff f admissibleF)
    (≡-trans
      (cong
        (λ remainder →
          WeilTestSpace._+S_ space
            (vonMangoldtPartialSum
              space arithmetic mangoldt cutoff f)
            remainder)
        tailZero)
      (VonMangoldtPrimeSideLimit.addZeroRight limit
        (vonMangoldtPartialSum
          space arithmetic mangoldt cutoff f)))
