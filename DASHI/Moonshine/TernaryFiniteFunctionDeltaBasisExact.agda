module DASHI.Moonshine.TernaryFiniteFunctionDeltaBasisExact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as L
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as V
import DASHI.Moonshine.Monster3BFiniteSchrodingerBooleanDeltaExact as Delta
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H

------------------------------------------------------------------------
-- GENERIC TERNARY FINITE-FUNCTION DELTA BASIS
--
-- Keep the finite carrier as T^n rather than flattening it to Fin (3^n).
-- A finite linear combination syntax enumerates the three head values
-- recursively.  The exact decomposition theorem is therefore proved once for
-- every ternary depth n and later instantiated at n = 6.
------------------------------------------------------------------------

data TritCube : Nat → Set where
  cube0 : TritCube 0
  cubeS : ∀ {n} → Trit → TritCube n → TritCube (suc n)

cubeEqual : ∀ {n} → TritCube n → TritCube n → Bool
cubeEqual cube0 cube0 = true
cubeEqual (cubeS t ts) (cubeS u us) =
  V._and_ (V.tritEqual t u) (cubeEqual ts us)

addZeroLeft : (a : C3.Cyclotomic3) → V.addC3 C3.zero a ≡ a
addZeroLeft (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext (solve (a ∷ [])) (solve (b ∷ []))

addZeroRight : (a : C3.Cyclotomic3) → V.addC3 a C3.zero ≡ a
addZeroRight (C3.cyclotomic3 a b) =
  C3.cyclotomic3Ext (solve (a ∷ [])) (solve (b ∷ []))

multiplyRightOne : (a : C3.Cyclotomic3) → C3.multiply a C3.one ≡ a
multiplyRightOne a = trans (L.multiplyCommutative a C3.one) (L.oneActsLeft a)

multiplyRightZero : (a : C3.Cyclotomic3) → C3.multiply a C3.zero ≡ C3.zero
multiplyRightZero a = trans (L.multiplyCommutative a C3.zero) (L.zeroActsLeft a)

pointMass :
  ∀ {n} → TritCube n → C3.Cyclotomic3 → TritCube n → C3.Cyclotomic3
pointMass selected coefficient x with cubeEqual selected x
... | true = coefficient
... | false = C3.zero

data DeltaCombination (n : Nat) : Set where
  deltaTerm : TritCube n → C3.Cyclotomic3 → DeltaCombination n
  combine : DeltaCombination n → DeltaCombination n → DeltaCombination n

interpret : ∀ {n} → DeltaCombination n → TritCube n → C3.Cyclotomic3
interpret (deltaTerm selected coefficient) x = pointMass selected coefficient x
interpret (combine left right) x = V.addC3 (interpret left x) (interpret right x)

liftHead :
  ∀ {n} → Trit → DeltaCombination n → DeltaCombination (suc n)
liftHead head (deltaTerm selected coefficient) =
  deltaTerm (cubeS head selected) coefficient
liftHead head (combine left right) =
  combine (liftHead head left) (liftHead head right)

gate : Bool → C3.Cyclotomic3 → C3.Cyclotomic3
gate false value = C3.zero
gate true value = value

gateAdd :
  (b : Bool) (left right : C3.Cyclotomic3) →
  V.addC3 (gate b left) (gate b right)
  ≡ gate b (V.addC3 left right)
gateAdd false left right = addZeroLeft C3.zero
gateAdd true left right = refl

interpretLiftHead :
  ∀ {n} (head observed : Trit)
    (combination : DeltaCombination n)
    (tail : TritCube n) →
  interpret (liftHead head combination) (cubeS observed tail)
  ≡ gate (V.tritEqual head observed) (interpret combination tail)
interpretLiftHead head observed (deltaTerm selected coefficient) tail
  with V.tritEqual head observed | cubeEqual selected tail
... | false | false = refl
... | false | true = refl
... | true | false = refl
... | true | true = refl
interpretLiftHead head observed (combine left right) tail =
  trans
    (cong₂ V.addC3
      (interpretLiftHead head observed left tail)
      (interpretLiftHead head observed right tail))
    (gateAdd (V.tritEqual head observed)
      (interpret left tail)
      (interpret right tail))
  where
  cong₂ :
    ∀ {A B C : Set}
      (f : A → B → C) {a a' : A} {b b' : B} →
      a ≡ a' → b ≡ b' → f a b ≡ f a' b'
  cong₂ f refl refl = refl

decompose :
  ∀ {n} → (TritCube n → C3.Cyclotomic3) → DeltaCombination n
decompose {0} f = deltaTerm cube0 (f cube0)
decompose {suc n} f =
  combine
    (liftHead neg (decompose (λ tail → f (cubeS neg tail))))
    (combine
      (liftHead zer (decompose (λ tail → f (cubeS zer tail))))
      (liftHead pos (decompose (λ tail → f (cubeS pos tail)))))

decomposeExact :
  ∀ {n}
    (f : TritCube n → C3.Cyclotomic3)
    (x : TritCube n) →
  interpret (decompose f) x ≡ f x
decomposeExact {0} f cube0 = refl
decomposeExact {suc n} f (cubeS neg tail)
  rewrite interpretLiftHead neg neg (decompose (λ t → f (cubeS neg t))) tail
        | interpretLiftHead zer neg (decompose (λ t → f (cubeS zer t))) tail
        | interpretLiftHead pos neg (decompose (λ t → f (cubeS pos t))) tail
        | decomposeExact (λ t → f (cubeS neg t)) tail
        | addZeroLeft C3.zero
        | addZeroRight (f (cubeS neg tail)) = refl
decomposeExact {suc n} f (cubeS zer tail)
  rewrite interpretLiftHead neg zer (decompose (λ t → f (cubeS neg t))) tail
        | interpretLiftHead zer zer (decompose (λ t → f (cubeS zer t))) tail
        | interpretLiftHead pos zer (decompose (λ t → f (cubeS pos t))) tail
        | decomposeExact (λ t → f (cubeS zer t)) tail
        | addZeroRight (f (cubeS zer tail))
        | addZeroLeft (f (cubeS zer tail)) = refl
decomposeExact {suc n} f (cubeS pos tail)
  rewrite interpretLiftHead neg pos (decompose (λ t → f (cubeS neg t))) tail
        | interpretLiftHead zer pos (decompose (λ t → f (cubeS zer t))) tail
        | interpretLiftHead pos pos (decompose (λ t → f (cubeS pos t))) tail
        | decomposeExact (λ t → f (cubeS pos t)) tail
        | addZeroLeft (f (cubeS pos tail))
        | addZeroLeft (f (cubeS pos tail)) = refl

Cube6 : Set
Cube6 = TritCube 6

toX6 : Cube6 → H.X6
toX6
  (cubeS a0
    (cubeS a1
      (cubeS a2
        (cubeS a3
          (cubeS a4
            (cubeS a5 cube0)))))) =
  H.x6 a0 a1 a2 a3 a4 a5

fromX6 : H.X6 → Cube6
fromX6 (H.x6 a0 a1 a2 a3 a4 a5) =
  cubeS a0
    (cubeS a1
      (cubeS a2
        (cubeS a3
          (cubeS a4
            (cubeS a5 cube0)))))

toFromX6 : (x : H.X6) → toX6 (fromX6 x) ≡ x
toFromX6 (H.x6 a0 a1 a2 a3 a4 a5) = refl

fromToX6 : (x : Cube6) → fromX6 (toX6 x) ≡ x
fromToX6
  (cubeS a0
    (cubeS a1
      (cubeS a2
        (cubeS a3
          (cubeS a4
            (cubeS a5 cube0)))))) = refl

andRightTrue : (b : Bool) → V._and_ b true ≡ b
andRightTrue false = refl
andRightTrue true = refl

cubeEqualFromX6 :
  (left right : H.X6) →
  cubeEqual (fromX6 left) (fromX6 right) ≡ V.x6Equal left right
cubeEqualFromX6
  (H.x6 l0 l1 l2 l3 l4 l5)
  (H.x6 r0 r1 r2 r3 r4 r5)
  rewrite andRightTrue (V.tritEqual l5 r5) = refl

scaledBooleanDeltaIsPointMass :
  (selected : H.X6) (coefficient : C3.Cyclotomic3) (x : H.X6) →
  V.cyclotomicScaleFunction coefficient (Delta.booleanDelta selected) x
  ≡ pointMass (fromX6 selected) coefficient (fromX6 x)
scaledBooleanDeltaIsPointMass selected coefficient x
  rewrite cubeEqualFromX6 selected x
  with V.x6Equal selected x
... | true = multiplyRightOne coefficient
... | false = multiplyRightZero coefficient

combinationFunction : DeltaCombination 6 → V.SchrodingerFunction
combinationFunction combination x = interpret combination (fromX6 x)

termFunctionPointwise :
  (selected : Cube6) (coefficient : C3.Cyclotomic3) →
  V.PointwiseEqual
    (V.cyclotomicScaleFunction coefficient (Delta.booleanDelta (toX6 selected)))
    (combinationFunction (deltaTerm selected coefficient))
termFunctionPointwise selected coefficient x =
  trans
    (scaledBooleanDeltaIsPointMass (toX6 selected) coefficient x)
    (cong (λ point → pointMass point coefficient (fromX6 x))
      (fromToX6 selected))

combinationMember :
  ∀ {Member}
    (inv : V.HeisenbergInvariantSubspace Member) →
    ((x : H.X6) → Member (Delta.booleanDelta x)) →
    (combination : DeltaCombination 6) →
    Member (combinationFunction combination)
combinationMember inv allDelta (deltaTerm selected coefficient) =
  V.closedUnderPointwiseEquality inv
    (V.cyclotomicScaleFunction coefficient (Delta.booleanDelta (toX6 selected)))
    (combinationFunction (deltaTerm selected coefficient))
    (V.closedUnderCyclotomicScaling inv
      coefficient
      (Delta.booleanDelta (toX6 selected))
      (allDelta (toX6 selected)))
    (termFunctionPointwise selected coefficient)
combinationMember inv allDelta (combine left right) =
  V.closedUnderAddition inv
    (combinationFunction left)
    (combinationFunction right)
    (combinationMember inv allDelta left)
    (combinationMember inv allDelta right)

allDeltaLinesSpanEverySchrodingerFunction :
  ∀ {Member}
    (inv : V.HeisenbergInvariantSubspace Member) →
    ((x : H.X6) → Member (Delta.booleanDelta x)) →
    (f : V.SchrodingerFunction) →
    Member f
allDeltaLinesSpanEverySchrodingerFunction inv allDelta f =
  let
    cubeFunction : Cube6 → C3.Cyclotomic3
    cubeFunction point = f (toX6 point)

    combination : DeltaCombination 6
    combination = decompose cubeFunction
  in
  V.closedUnderPointwiseEquality inv
    (combinationFunction combination)
    f
    (combinationMember inv allDelta combination)
    (λ x →
      trans
        (decomposeExact cubeFunction (fromX6 x))
        (cong f (toFromX6 x)))

record TernaryFiniteFunctionDeltaBasisBoundary : Set where
  constructor ternary-finite-function-delta-basis-boundary
  field
    carrierKeptAsTritPower : Bool
    recursiveFiniteCombinationConstructed : Bool
    decompositionExactAtEveryTernaryDepth : Bool
    cube6BridgedExactlyToX6 : Bool
    pointMassIdentifiedWithScaledBooleanDelta : Bool
    all729DeltasSpanEverySchrodingerFunction : Bool
    MonsterRepresentationIdentifiedByThisAlone : Bool

canonicalTernaryFiniteFunctionDeltaBasisBoundary :
  TernaryFiniteFunctionDeltaBasisBoundary
canonicalTernaryFiniteFunctionDeltaBasisBoundary =
  ternary-finite-function-delta-basis-boundary
    true true true true true true false
