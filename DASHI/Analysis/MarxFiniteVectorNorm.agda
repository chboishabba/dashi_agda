module DASHI.Analysis.MarxFiniteVectorNorm where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Set₁)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong₂)

open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxPowerRuleNormalisation
open import DASHI.Analysis.MarxScalarFrechetBridge
open import DASHI.Analysis.MarxHigherCalculus
open import DASHI.Analysis.MarxFiniteVectorSpace

------------------------------------------------------------------------
-- Scalar laws sufficient for the finite l1 norm.

record L1NormScalarLaws
  (A : MarxAlgebra)
  (O : OrderedScalar A)
  : Set₁ where
  field
    absolute : Carrier A → Carrier A

    absoluteNonnegative :
      ∀ x → _≤S_ O (zero A) (absolute x)

    absoluteZero :
      absolute (zero A) ≡ zero A

    absoluteTriangle :
      ∀ x y →
      _≤S_ O
        (absolute (_+_ A x y))
        (_+_ A (absolute x) (absolute y))

    addNonnegative :
      ∀ {x y} →
      _≤S_ O (zero A) x →
      _≤S_ O (zero A) y →
      _≤S_ O (zero A) (_+_ A x y)

    l1TriangleStep :
      ∀ {a b c r s t} →
      _≤S_ O a (_+_ A b c) →
      _≤S_ O r (_+_ A s t) →
      _≤S_ O
        (_+_ A a r)
        (_+_ A (_+_ A b s) (_+_ A c t))

open L1NormScalarLaws public

l1Norm :
  {A : MarxAlgebra} →
  {O : OrderedScalar A} →
  L1NormScalarLaws A O →
  ∀ {n} →
  Vec (Carrier A) n → Carrier A
l1Norm L [] = zero _
l1Norm {A} L (x ∷ xs) =
  _+_ A (absolute L x) (l1Norm L xs)

l1NormNonnegative :
  {A : MarxAlgebra} →
  {O : OrderedScalar A} →
  (L : L1NormScalarLaws A O) →
  ∀ {n} (v : Vec (Carrier A) n) →
  _≤S_ O (zero A) (l1Norm L v)
l1NormNonnegative {A} {O} L [] =
  OrderedScalar.leRefl O (zero A)
l1NormNonnegative L (x ∷ xs) =
  addNonnegative L
    (absoluteNonnegative L x)
    (l1NormNonnegative L xs)

l1NormZero :
  {A : MarxAlgebra} →
  {O : OrderedScalar A} →
  (moduleLaws : MarxScalarModuleLaws A) →
  (L : L1NormScalarLaws A O) →
  ∀ n →
  l1Norm L (zeroVector {A} n) ≡ zero A
l1NormZero moduleLaws L zero = refl
l1NormZero {A} moduleLaws L (suc n) =
  trans
    (cong₂ (_+_ A)
      (absoluteZero L)
      (l1NormZero moduleLaws L n))
    (MarxPowerAlgebraLaws.addZeroLeftLaw
      (MarxScalarModuleLaws.powerLaws moduleLaws)
      (zero A))

l1NormTriangle :
  {A : MarxAlgebra} →
  {O : OrderedScalar A} →
  (L : L1NormScalarLaws A O) →
  ∀ {n}
    (u v : Vec (Carrier A) n) →
  _≤S_ O
    (l1Norm L (addVector u v))
    (_+_ A (l1Norm L u) (l1Norm L v))
l1NormTriangle L [] [] =
  OrderedScalar.leRefl _ _
l1NormTriangle L (x ∷ xs) (y ∷ ys) =
  l1TriangleStep L
    (absoluteTriangle L x y)
    (l1NormTriangle L xs ys)

finiteL1NormedModule :
  {A : MarxAlgebra} →
  {O : OrderedScalar A} →
  (moduleLaws : MarxScalarModuleLaws A) →
  (normLaws : L1NormScalarLaws A O) →
  (n : Nat) →
  NormedModule A O (finiteVectorModule moduleLaws n)
finiteL1NormedModule moduleLaws normLaws n =
  record
    { norm = l1Norm normLaws
    ; normNonnegative = l1NormNonnegative normLaws
    ; normZero = l1NormZero moduleLaws normLaws n
    ; normTriangle = l1NormTriangle normLaws
    }
