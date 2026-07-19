module DASHI.Analysis.RiemannPrimeExhaustion where

-- Exhaustive finite-prime / finite-exponent approximation of the classical
-- prime-power side.  Unlike the fixed 15-lane surface, every prime is required
-- to enter some duplicate-free stage.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)
open import DASHI.Analysis.WeilTestSpace
open import DASHI.Analysis.RiemannExplicitFormula
open import DASHI.Analysis.RiemannVonMangoldtSpecification

------------------------------------------------------------------------
-- Finite support structure
------------------------------------------------------------------------

data _∈_ {A : Set} (x : A) : List A → Set where
  here : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

data NoDuplicates {A : Set} : List A → Set where
  ndNil : NoDuplicates []
  ndCons :
    {x : A} {xs : List A} →
    (x ∈ xs → ⊥) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

record PrimeExhaustion
  (space : WeilTestSpace)
  (arithmetic : AllPrimeArithmetic space) : Set₁ where
  field
    stage : Nat → List (AllPrimeArithmetic.Prime arithmetic)

    stageNoDuplicates :
      (level : Nat) →
      NoDuplicates (stage level)

    stageMonotone :
      (level : Nat) →
      (p : AllPrimeArithmetic.Prime arithmetic) →
      p ∈ stage level →
      p ∈ stage (suc level)

    exhaustive :
      (p : AllPrimeArithmetic.Prime arithmetic) →
      Σ Nat (λ level → p ∈ stage level)

------------------------------------------------------------------------
-- Finite Euler/prime-power sums
------------------------------------------------------------------------

allPrimePowerSample :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  WeilTestSpace.Test space →
  AllPrimeArithmetic.Prime arithmetic →
  Nat →
  WeilTestSpace.Scalar space
allPrimePowerSample space arithmetic f p exponentIndex =
  AllPrimeArithmetic._*S_ arithmetic
    (AllPrimeArithmetic.logPrimeWeight arithmetic p)
    (AllPrimeArithmetic.sampleAtNat arithmetic f
      (primePowerNat space arithmetic p exponentIndex))

sumPrimeExponents :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  Nat →
  WeilTestSpace.Test space →
  AllPrimeArithmetic.Prime arithmetic →
  WeilTestSpace.Scalar space
sumPrimeExponents space arithmetic zero f p =
  WeilTestSpace.zeroS space
sumPrimeExponents space arithmetic (suc cutoff) f p =
  WeilTestSpace._+S_ space
    (allPrimePowerSample space arithmetic f p cutoff)
    (sumPrimeExponents space arithmetic cutoff f p)

sumPrimeList :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  Nat →
  WeilTestSpace.Test space →
  List (AllPrimeArithmetic.Prime arithmetic) →
  WeilTestSpace.Scalar space
sumPrimeList space arithmetic exponentCutoff f [] =
  WeilTestSpace.zeroS space
sumPrimeList space arithmetic exponentCutoff f (p ∷ ps) =
  WeilTestSpace._+S_ space
    (sumPrimeExponents space arithmetic exponentCutoff f p)
    (sumPrimeList space arithmetic exponentCutoff f ps)

primeExponentTruncation :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  PrimeExhaustion space arithmetic →
  Nat →
  Nat →
  WeilTestSpace.Test space →
  WeilTestSpace.Scalar space
primeExponentTruncation
  space arithmetic exhaustion primeStage exponentCutoff f =
  sumPrimeList space arithmetic exponentCutoff f
    (PrimeExhaustion.stage exhaustion primeStage)

------------------------------------------------------------------------
-- Exact relation to the von Mangoldt specification
------------------------------------------------------------------------

cong₂ :
  {A B C : Set} →
  (op : A → B → C) →
  {x x′ : A} {y y′ : B} →
  x ≡ x′ → y ≡ y′ →
  op x y ≡ op x′ y′
cong₂ op refl refl = refl

allPrimePowerSampleAgreesWithVonMangoldt :
  (space : WeilTestSpace) →
  (arithmetic : AllPrimeArithmetic space) →
  (mangoldt : VonMangoldtFunction space arithmetic) →
  (f : WeilTestSpace.Test space) →
  (p : AllPrimeArithmetic.Prime arithmetic) →
  (exponentIndex : Nat) →
  allPrimePowerSample space arithmetic f p exponentIndex
  ≡
  vonMangoldtSampleTerm space arithmetic mangoldt f
    (primePowerNat space arithmetic p exponentIndex)
allPrimePowerSampleAgreesWithVonMangoldt
  space arithmetic mangoldt f p exponentIndex =
  cong₂
    (AllPrimeArithmetic._*S_ arithmetic)
    (≡-sym (lambdaAtPrimePower
      space arithmetic mangoldt p exponentIndex))
    refl

------------------------------------------------------------------------
-- Limit/tail bridge to the full explicit-formula prime term
------------------------------------------------------------------------

record PrimeExhaustionLimitBridge
  (space : WeilTestSpace)
  (formula : RiemannExplicitFormula space)
  (arithmetic : AllPrimeArithmetic space)
  (exhaustion : PrimeExhaustion space arithmetic) : Set₁ where
  open WeilTestSpace space
  open RiemannExplicitFormula formula
  field
    tail : Nat → Nat → Test → Scalar

    TailDefined : Nat → Nat → Test → Set
    JointTailConvergesToZero : Test → Set

    tailDefined :
      (primeStage exponentCutoff : Nat) →
      (f : Test) →
      admissible f →
      TailDefined primeStage exponentCutoff f

    jointTailConvergesToZero :
      (f : Test) →
      admissible f →
      JointTailConvergesToZero f

    primePowerTermDecomposition :
      (primeStage exponentCutoff : Nat) →
      (f : Test) →
      admissible f →
      primePowerTerm f
      ≡
      (primeExponentTruncation
        space arithmetic exhaustion primeStage exponentCutoff f
       +S tail primeStage exponentCutoff f)
