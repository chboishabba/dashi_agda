module DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceVectorCenteringExact where

------------------------------------------------------------------------
-- S2b2d1b2 / COMPLETE-GRAPH VECTOR COVARIANCE IDENTITY
--
-- For a finite family A_i : C^3 with scalar rates r_i, define
--
--   V = sum_{i<j} (r_i-r_j) (A_i-A_j).
--
-- The scalar coherent-covariance owner already proves the corresponding
-- complete-graph identity coordinatewise.  This owner lifts that identity to
-- the literal rational Complex3 carrier:
--
--   V
--     = n * sum_i r_i A_i
--       - (sum_i r_i) * (sum_i A_i).
--
-- This is exact finite algebra BEFORE norms.  In particular it avoids the
-- lossy pairwise Young step which repeats ||M||^2 once per unordered pair.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputPairDifferenceDebtExact as Coord

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Vector finite sums.
------------------------------------------------------------------------

weightedVectorSum :
  ∀ {A : Set} →
  (A → ℚ) →
  (A → C3.Complex3 F) →
  List A → C3.Complex3 F
weightedVectorSum rate value [] = C3.complex3Zero F
weightedVectorSum rate value (x ∷ xs) =
  C3.complex3Add
    (R291.realScale (rate x) (value x))
    (weightedVectorSum rate value xs)

vectorSum :
  ∀ {A : Set} →
  (A → C3.Complex3 F) →
  List A → C3.Complex3 F
vectorSum value [] = C3.complex3Zero F
vectorSum value (x ∷ xs) =
  C3.complex3Add (value x) (vectorSum value xs)

pairVectorTerm :
  ∀ {A : Set} →
  (A → ℚ) →
  (A → C3.Complex3 F) →
  A → A → C3.Complex3 F
pairVectorTerm rate value left right =
  R291.realScale
    (rate left - rate right)
    (C3.complex3Subtract (value left) (value right))

pairVectorAgainstHead :
  ∀ {A : Set} →
  (A → ℚ) →
  (A → C3.Complex3 F) →
  A → List A → C3.Complex3 F
pairVectorAgainstHead rate value head [] = C3.complex3Zero F
pairVectorAgainstHead rate value head (x ∷ xs) =
  C3.complex3Add
    (pairVectorTerm rate value head x)
    (pairVectorAgainstHead rate value head xs)

pairVectorDifferenceSum :
  ∀ {A : Set} →
  (A → ℚ) →
  (A → C3.Complex3 F) →
  List A → C3.Complex3 F
pairVectorDifferenceSum rate value [] = C3.complex3Zero F
pairVectorDifferenceSum rate value (x ∷ xs) =
  C3.complex3Add
    (pairVectorAgainstHead rate value x xs)
    (pairVectorDifferenceSum rate value xs)

closedFormVector :
  ∀ {A : Set} →
  (A → ℚ) →
  (A → C3.Complex3 F) →
  List A → C3.Complex3 F
closedFormVector rate value items =
  C3.complex3Subtract
    (R291.realScale
      (Pair.natAsRational (length items))
      (weightedVectorSum rate value items))
    (R291.realScale
      (Pair.rateSum rate items)
      (vectorSum value items))

------------------------------------------------------------------------
-- Six-coordinate linearity for the literal rational C^3 operations.
------------------------------------------------------------------------

xRealScale :
  (s : ℚ) (v : C3.Complex3 F) →
  Coord.xReal (R291.realScale s v) ≡ s * Coord.xReal v
xRealScale s
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (s ∷ xr ∷ xi ∷ [])

xImagScale :
  (s : ℚ) (v : C3.Complex3 F) →
  Coord.xImag (R291.realScale s v) ≡ s * Coord.xImag v
xImagScale s
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (s ∷ xr ∷ xi ∷ [])

yRealScale :
  (s : ℚ) (v : C3.Complex3 F) →
  Coord.yReal (R291.realScale s v) ≡ s * Coord.yReal v
yRealScale s
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (s ∷ yr ∷ yi ∷ [])

yImagScale :
  (s : ℚ) (v : C3.Complex3 F) →
  Coord.yImag (R291.realScale s v) ≡ s * Coord.yImag v
yImagScale s
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (s ∷ yr ∷ yi ∷ [])

zRealScale :
  (s : ℚ) (v : C3.Complex3 F) →
  Coord.zReal (R291.realScale s v) ≡ s * Coord.zReal v
zRealScale s
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (s ∷ zr ∷ zi ∷ [])

zImagScale :
  (s : ℚ) (v : C3.Complex3 F) →
  Coord.zImag (R291.realScale s v) ≡ s * Coord.zImag v
zImagScale s
    (C3.complex3
      (C3.complex xr xi) (C3.complex yr yi) (C3.complex zr zi)) =
  solve (s ∷ zr ∷ zi ∷ [])

xRealAdd : (u v : C3.Complex3 F) →
  Coord.xReal (C3.complex3Add u v) ≡ Coord.xReal u + Coord.xReal v
xRealAdd
    (C3.complex3 (C3.complex ur ui) uy uz)
    (C3.complex3 (C3.complex vr vi) vy vz) =
  solve (ur ∷ vr ∷ [])

xImagAdd : (u v : C3.Complex3 F) →
  Coord.xImag (C3.complex3Add u v) ≡ Coord.xImag u + Coord.xImag v
xImagAdd
    (C3.complex3 (C3.complex ur ui) uy uz)
    (C3.complex3 (C3.complex vr vi) vy vz) =
  solve (ui ∷ vi ∷ [])

yRealAdd : (u v : C3.Complex3 F) →
  Coord.yReal (C3.complex3Add u v) ≡ Coord.yReal u + Coord.yReal v
yRealAdd
    (C3.complex3 ux (C3.complex ur ui) uz)
    (C3.complex3 vx (C3.complex vr vi) vz) =
  solve (ur ∷ vr ∷ [])

yImagAdd : (u v : C3.Complex3 F) →
  Coord.yImag (C3.complex3Add u v) ≡ Coord.yImag u + Coord.yImag v
yImagAdd
    (C3.complex3 ux (C3.complex ur ui) uz)
    (C3.complex3 vx (C3.complex vr vi) vz) =
  solve (ui ∷ vi ∷ [])

zRealAdd : (u v : C3.Complex3 F) →
  Coord.zReal (C3.complex3Add u v) ≡ Coord.zReal u + Coord.zReal v
zRealAdd
    (C3.complex3 ux uy (C3.complex ur ui))
    (C3.complex3 vx vy (C3.complex vr vi)) =
  solve (ur ∷ vr ∷ [])

zImagAdd : (u v : C3.Complex3 F) →
  Coord.zImag (C3.complex3Add u v) ≡ Coord.zImag u + Coord.zImag v
zImagAdd
    (C3.complex3 ux uy (C3.complex ur ui))
    (C3.complex3 vx vy (C3.complex vr vi)) =
  solve (ui ∷ vi ∷ [])

xRealSubtract : (u v : C3.Complex3 F) →
  Coord.xReal (C3.complex3Subtract u v) ≡ Coord.xReal u - Coord.xReal v
xRealSubtract
    (C3.complex3 (C3.complex ur ui) uy uz)
    (C3.complex3 (C3.complex vr vi) vy vz) =
  solve (ur ∷ vr ∷ [])

xImagSubtract : (u v : C3.Complex3 F) →
  Coord.xImag (C3.complex3Subtract u v) ≡ Coord.xImag u - Coord.xImag v
xImagSubtract
    (C3.complex3 (C3.complex ur ui) uy uz)
    (C3.complex3 (C3.complex vr vi) vy vz) =
  solve (ui ∷ vi ∷ [])

yRealSubtract : (u v : C3.Complex3 F) →
  Coord.yReal (C3.complex3Subtract u v) ≡ Coord.yReal u - Coord.yReal v
yRealSubtract
    (C3.complex3 ux (C3.complex ur ui) uz)
    (C3.complex3 vx (C3.complex vr vi) vz) =
  solve (ur ∷ vr ∷ [])

yImagSubtract : (u v : C3.Complex3 F) →
  Coord.yImag (C3.complex3Subtract u v) ≡ Coord.yImag u - Coord.yImag v
yImagSubtract
    (C3.complex3 ux (C3.complex ur ui) uz)
    (C3.complex3 vx (C3.complex vr vi) vz) =
  solve (ui ∷ vi ∷ [])

zRealSubtract : (u v : C3.Complex3 F) →
  Coord.zReal (C3.complex3Subtract u v) ≡ Coord.zReal u - Coord.zReal v
zRealSubtract
    (C3.complex3 ux uy (C3.complex ur ui))
    (C3.complex3 vx vy (C3.complex vr vi)) =
  solve (ur ∷ vr ∷ [])

zImagSubtract : (u v : C3.Complex3 F) →
  Coord.zImag (C3.complex3Subtract u v) ≡ Coord.zImag u - Coord.zImag v
zImagSubtract
    (C3.complex3 ux uy (C3.complex ur ui))
    (C3.complex3 vx vy (C3.complex vr vi)) =
  solve (ui ∷ vi ∷ [])

------------------------------------------------------------------------
-- Coordinate projections of the finite vector sums.
------------------------------------------------------------------------

weightedXReal :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.xReal (weightedVectorSum rate value items)
  ≡ Pair.weightedWorkSum rate (λ x → Coord.xReal (value x)) items
weightedXReal rate value [] = refl
weightedXReal rate value (x ∷ xs)
  rewrite xRealAdd (R291.realScale (rate x) (value x))
            (weightedVectorSum rate value xs)
        | xRealScale (rate x) (value x)
        | weightedXReal rate value xs = refl

weightedXImag :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.xImag (weightedVectorSum rate value items)
  ≡ Pair.weightedWorkSum rate (λ x → Coord.xImag (value x)) items
weightedXImag rate value [] = refl
weightedXImag rate value (x ∷ xs)
  rewrite xImagAdd (R291.realScale (rate x) (value x))
            (weightedVectorSum rate value xs)
        | xImagScale (rate x) (value x)
        | weightedXImag rate value xs = refl

weightedYReal :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.yReal (weightedVectorSum rate value items)
  ≡ Pair.weightedWorkSum rate (λ x → Coord.yReal (value x)) items
weightedYReal rate value [] = refl
weightedYReal rate value (x ∷ xs)
  rewrite yRealAdd (R291.realScale (rate x) (value x))
            (weightedVectorSum rate value xs)
        | yRealScale (rate x) (value x)
        | weightedYReal rate value xs = refl

weightedYImag :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.yImag (weightedVectorSum rate value items)
  ≡ Pair.weightedWorkSum rate (λ x → Coord.yImag (value x)) items
weightedYImag rate value [] = refl
weightedYImag rate value (x ∷ xs)
  rewrite yImagAdd (R291.realScale (rate x) (value x))
            (weightedVectorSum rate value xs)
        | yImagScale (rate x) (value x)
        | weightedYImag rate value xs = refl

weightedZReal :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.zReal (weightedVectorSum rate value items)
  ≡ Pair.weightedWorkSum rate (λ x → Coord.zReal (value x)) items
weightedZReal rate value [] = refl
weightedZReal rate value (x ∷ xs)
  rewrite zRealAdd (R291.realScale (rate x) (value x))
            (weightedVectorSum rate value xs)
        | zRealScale (rate x) (value x)
        | weightedZReal rate value xs = refl

weightedZImag :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.zImag (weightedVectorSum rate value items)
  ≡ Pair.weightedWorkSum rate (λ x → Coord.zImag (value x)) items
weightedZImag rate value [] = refl
weightedZImag rate value (x ∷ xs)
  rewrite zImagAdd (R291.realScale (rate x) (value x))
            (weightedVectorSum rate value xs)
        | zImagScale (rate x) (value x)
        | weightedZImag rate value xs = refl

sumXReal :
  ∀ {A : Set} (value : A → C3.Complex3 F) items →
  Coord.xReal (vectorSum value items)
  ≡ Pair.workSum (λ x → Coord.xReal (value x)) items
sumXReal value [] = refl
sumXReal value (x ∷ xs)
  rewrite xRealAdd (value x) (vectorSum value xs)
        | sumXReal value xs = refl

sumXImag :
  ∀ {A : Set} (value : A → C3.Complex3 F) items →
  Coord.xImag (vectorSum value items)
  ≡ Pair.workSum (λ x → Coord.xImag (value x)) items
sumXImag value [] = refl
sumXImag value (x ∷ xs)
  rewrite xImagAdd (value x) (vectorSum value xs)
        | sumXImag value xs = refl

sumYReal :
  ∀ {A : Set} (value : A → C3.Complex3 F) items →
  Coord.yReal (vectorSum value items)
  ≡ Pair.workSum (λ x → Coord.yReal (value x)) items
sumYReal value [] = refl
sumYReal value (x ∷ xs)
  rewrite yRealAdd (value x) (vectorSum value xs)
        | sumYReal value xs = refl

sumYImag :
  ∀ {A : Set} (value : A → C3.Complex3 F) items →
  Coord.yImag (vectorSum value items)
  ≡ Pair.workSum (λ x → Coord.yImag (value x)) items
sumYImag value [] = refl
sumYImag value (x ∷ xs)
  rewrite yImagAdd (value x) (vectorSum value xs)
        | sumYImag value xs = refl

sumZReal :
  ∀ {A : Set} (value : A → C3.Complex3 F) items →
  Coord.zReal (vectorSum value items)
  ≡ Pair.workSum (λ x → Coord.zReal (value x)) items
sumZReal value [] = refl
sumZReal value (x ∷ xs)
  rewrite zRealAdd (value x) (vectorSum value xs)
        | sumZReal value xs = refl

sumZImag :
  ∀ {A : Set} (value : A → C3.Complex3 F) items →
  Coord.zImag (vectorSum value items)
  ≡ Pair.workSum (λ x → Coord.zImag (value x)) items
sumZImag value [] = refl
sumZImag value (x ∷ xs)
  rewrite zImagAdd (value x) (vectorSum value xs)
        | sumZImag value xs = refl

------------------------------------------------------------------------
-- Pair-vector projections coincide with the existing scalar pair graph.
------------------------------------------------------------------------

pairTermXReal :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) left right →
  Coord.xReal (pairVectorTerm rate value left right)
  ≡ (rate left - rate right)
      * (Coord.xReal (value left) - Coord.xReal (value right))
pairTermXReal rate value left right
  rewrite xRealScale (rate left - rate right)
            (C3.complex3Subtract (value left) (value right))
        | xRealSubtract (value left) (value right) = refl

pairTermXImag :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) left right →
  Coord.xImag (pairVectorTerm rate value left right)
  ≡ (rate left - rate right)
      * (Coord.xImag (value left) - Coord.xImag (value right))
pairTermXImag rate value left right
  rewrite xImagScale (rate left - rate right)
            (C3.complex3Subtract (value left) (value right))
        | xImagSubtract (value left) (value right) = refl

pairTermYReal :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) left right →
  Coord.yReal (pairVectorTerm rate value left right)
  ≡ (rate left - rate right)
      * (Coord.yReal (value left) - Coord.yReal (value right))
pairTermYReal rate value left right
  rewrite yRealScale (rate left - rate right)
            (C3.complex3Subtract (value left) (value right))
        | yRealSubtract (value left) (value right) = refl

pairTermYImag :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) left right →
  Coord.yImag (pairVectorTerm rate value left right)
  ≡ (rate left - rate right)
      * (Coord.yImag (value left) - Coord.yImag (value right))
pairTermYImag rate value left right
  rewrite yImagScale (rate left - rate right)
            (C3.complex3Subtract (value left) (value right))
        | yImagSubtract (value left) (value right) = refl

pairTermZReal :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) left right →
  Coord.zReal (pairVectorTerm rate value left right)
  ≡ (rate left - rate right)
      * (Coord.zReal (value left) - Coord.zReal (value right))
pairTermZReal rate value left right
  rewrite zRealScale (rate left - rate right)
            (C3.complex3Subtract (value left) (value right))
        | zRealSubtract (value left) (value right) = refl

pairTermZImag :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) left right →
  Coord.zImag (pairVectorTerm rate value left right)
  ≡ (rate left - rate right)
      * (Coord.zImag (value left) - Coord.zImag (value right))
pairTermZImag rate value left right
  rewrite zImagScale (rate left - rate right)
            (C3.complex3Subtract (value left) (value right))
        | zImagSubtract (value left) (value right) = refl

pairAgainstXReal :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) head rest →
  Coord.xReal (pairVectorAgainstHead rate value head rest)
  ≡ Pair.pairAgainstHead rate (λ x → Coord.xReal (value x)) head rest
pairAgainstXReal rate value head [] = refl
pairAgainstXReal rate value head (x ∷ xs)
  rewrite xRealAdd (pairVectorTerm rate value head x)
            (pairVectorAgainstHead rate value head xs)
        | pairTermXReal rate value head x
        | pairAgainstXReal rate value head xs = refl

pairAgainstXImag :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) head rest →
  Coord.xImag (pairVectorAgainstHead rate value head rest)
  ≡ Pair.pairAgainstHead rate (λ x → Coord.xImag (value x)) head rest
pairAgainstXImag rate value head [] = refl
pairAgainstXImag rate value head (x ∷ xs)
  rewrite xImagAdd (pairVectorTerm rate value head x)
            (pairVectorAgainstHead rate value head xs)
        | pairTermXImag rate value head x
        | pairAgainstXImag rate value head xs = refl

pairAgainstYReal :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) head rest →
  Coord.yReal (pairVectorAgainstHead rate value head rest)
  ≡ Pair.pairAgainstHead rate (λ x → Coord.yReal (value x)) head rest
pairAgainstYReal rate value head [] = refl
pairAgainstYReal rate value head (x ∷ xs)
  rewrite yRealAdd (pairVectorTerm rate value head x)
            (pairVectorAgainstHead rate value head xs)
        | pairTermYReal rate value head x
        | pairAgainstYReal rate value head xs = refl

pairAgainstYImag :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) head rest →
  Coord.yImag (pairVectorAgainstHead rate value head rest)
  ≡ Pair.pairAgainstHead rate (λ x → Coord.yImag (value x)) head rest
pairAgainstYImag rate value head [] = refl
pairAgainstYImag rate value head (x ∷ xs)
  rewrite yImagAdd (pairVectorTerm rate value head x)
            (pairVectorAgainstHead rate value head xs)
        | pairTermYImag rate value head x
        | pairAgainstYImag rate value head xs = refl

pairAgainstZReal :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) head rest →
  Coord.zReal (pairVectorAgainstHead rate value head rest)
  ≡ Pair.pairAgainstHead rate (λ x → Coord.zReal (value x)) head rest
pairAgainstZReal rate value head [] = refl
pairAgainstZReal rate value head (x ∷ xs)
  rewrite zRealAdd (pairVectorTerm rate value head x)
            (pairVectorAgainstHead rate value head xs)
        | pairTermZReal rate value head x
        | pairAgainstZReal rate value head xs = refl

pairAgainstZImag :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) head rest →
  Coord.zImag (pairVectorAgainstHead rate value head rest)
  ≡ Pair.pairAgainstHead rate (λ x → Coord.zImag (value x)) head rest
pairAgainstZImag rate value head [] = refl
pairAgainstZImag rate value head (x ∷ xs)
  rewrite zImagAdd (pairVectorTerm rate value head x)
            (pairVectorAgainstHead rate value head xs)
        | pairTermZImag rate value head x
        | pairAgainstZImag rate value head xs = refl

pairXReal :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.xReal (pairVectorDifferenceSum rate value items)
  ≡ Pair.pairDifferenceWorkSum rate (λ x → Coord.xReal (value x)) items
pairXReal rate value [] = refl
pairXReal rate value (x ∷ xs)
  rewrite xRealAdd (pairVectorAgainstHead rate value x xs)
            (pairVectorDifferenceSum rate value xs)
        | pairAgainstXReal rate value x xs
        | pairXReal rate value xs = refl

pairXImag :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.xImag (pairVectorDifferenceSum rate value items)
  ≡ Pair.pairDifferenceWorkSum rate (λ x → Coord.xImag (value x)) items
pairXImag rate value [] = refl
pairXImag rate value (x ∷ xs)
  rewrite xImagAdd (pairVectorAgainstHead rate value x xs)
            (pairVectorDifferenceSum rate value xs)
        | pairAgainstXImag rate value x xs
        | pairXImag rate value xs = refl

pairYReal :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.yReal (pairVectorDifferenceSum rate value items)
  ≡ Pair.pairDifferenceWorkSum rate (λ x → Coord.yReal (value x)) items
pairYReal rate value [] = refl
pairYReal rate value (x ∷ xs)
  rewrite yRealAdd (pairVectorAgainstHead rate value x xs)
            (pairVectorDifferenceSum rate value xs)
        | pairAgainstYReal rate value x xs
        | pairYReal rate value xs = refl

pairYImag :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.yImag (pairVectorDifferenceSum rate value items)
  ≡ Pair.pairDifferenceWorkSum rate (λ x → Coord.yImag (value x)) items
pairYImag rate value [] = refl
pairYImag rate value (x ∷ xs)
  rewrite yImagAdd (pairVectorAgainstHead rate value x xs)
            (pairVectorDifferenceSum rate value xs)
        | pairAgainstYImag rate value x xs
        | pairYImag rate value xs = refl

pairZReal :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.zReal (pairVectorDifferenceSum rate value items)
  ≡ Pair.pairDifferenceWorkSum rate (λ x → Coord.zReal (value x)) items
pairZReal rate value [] = refl
pairZReal rate value (x ∷ xs)
  rewrite zRealAdd (pairVectorAgainstHead rate value x xs)
            (pairVectorDifferenceSum rate value xs)
        | pairAgainstZReal rate value x xs
        | pairZReal rate value xs = refl

pairZImag :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.zImag (pairVectorDifferenceSum rate value items)
  ≡ Pair.pairDifferenceWorkSum rate (λ x → Coord.zImag (value x)) items
pairZImag rate value [] = refl
pairZImag rate value (x ∷ xs)
  rewrite zImagAdd (pairVectorAgainstHead rate value x xs)
            (pairVectorDifferenceSum rate value xs)
        | pairAgainstZImag rate value x xs
        | pairZImag rate value xs = refl

------------------------------------------------------------------------
-- Closed form on each coordinate, then extensional reconstruction.
------------------------------------------------------------------------

xRealClosed :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.xReal (pairVectorDifferenceSum rate value items)
  ≡ Coord.xReal (closedFormVector rate value items)
xRealClosed rate value items
  rewrite pairXReal rate value items
        | Pair.pairDifferenceClosedForm
            rate (λ x → Coord.xReal (value x)) items
        | xRealSubtract
            (R291.realScale (Pair.natAsRational (length items))
              (weightedVectorSum rate value items))
            (R291.realScale (Pair.rateSum rate items)
              (vectorSum value items))
        | xRealScale (Pair.natAsRational (length items))
            (weightedVectorSum rate value items)
        | xRealScale (Pair.rateSum rate items)
            (vectorSum value items)
        | weightedXReal rate value items
        | sumXReal value items = refl

xImagClosed :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.xImag (pairVectorDifferenceSum rate value items)
  ≡ Coord.xImag (closedFormVector rate value items)
xImagClosed rate value items
  rewrite pairXImag rate value items
        | Pair.pairDifferenceClosedForm
            rate (λ x → Coord.xImag (value x)) items
        | xImagSubtract
            (R291.realScale (Pair.natAsRational (length items))
              (weightedVectorSum rate value items))
            (R291.realScale (Pair.rateSum rate items)
              (vectorSum value items))
        | xImagScale (Pair.natAsRational (length items))
            (weightedVectorSum rate value items)
        | xImagScale (Pair.rateSum rate items)
            (vectorSum value items)
        | weightedXImag rate value items
        | sumXImag value items = refl

yRealClosed :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.yReal (pairVectorDifferenceSum rate value items)
  ≡ Coord.yReal (closedFormVector rate value items)
yRealClosed rate value items
  rewrite pairYReal rate value items
        | Pair.pairDifferenceClosedForm
            rate (λ x → Coord.yReal (value x)) items
        | yRealSubtract
            (R291.realScale (Pair.natAsRational (length items))
              (weightedVectorSum rate value items))
            (R291.realScale (Pair.rateSum rate items)
              (vectorSum value items))
        | yRealScale (Pair.natAsRational (length items))
            (weightedVectorSum rate value items)
        | yRealScale (Pair.rateSum rate items)
            (vectorSum value items)
        | weightedYReal rate value items
        | sumYReal value items = refl

yImagClosed :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.yImag (pairVectorDifferenceSum rate value items)
  ≡ Coord.yImag (closedFormVector rate value items)
yImagClosed rate value items
  rewrite pairYImag rate value items
        | Pair.pairDifferenceClosedForm
            rate (λ x → Coord.yImag (value x)) items
        | yImagSubtract
            (R291.realScale (Pair.natAsRational (length items))
              (weightedVectorSum rate value items))
            (R291.realScale (Pair.rateSum rate items)
              (vectorSum value items))
        | yImagScale (Pair.natAsRational (length items))
            (weightedVectorSum rate value items)
        | yImagScale (Pair.rateSum rate items)
            (vectorSum value items)
        | weightedYImag rate value items
        | sumYImag value items = refl

zRealClosed :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.zReal (pairVectorDifferenceSum rate value items)
  ≡ Coord.zReal (closedFormVector rate value items)
zRealClosed rate value items
  rewrite pairZReal rate value items
        | Pair.pairDifferenceClosedForm
            rate (λ x → Coord.zReal (value x)) items
        | zRealSubtract
            (R291.realScale (Pair.natAsRational (length items))
              (weightedVectorSum rate value items))
            (R291.realScale (Pair.rateSum rate items)
              (vectorSum value items))
        | zRealScale (Pair.natAsRational (length items))
            (weightedVectorSum rate value items)
        | zRealScale (Pair.rateSum rate items)
            (vectorSum value items)
        | weightedZReal rate value items
        | sumZReal value items = refl

zImagClosed :
  ∀ {A : Set} (rate : A → ℚ) (value : A → C3.Complex3 F) items →
  Coord.zImag (pairVectorDifferenceSum rate value items)
  ≡ Coord.zImag (closedFormVector rate value items)
zImagClosed rate value items
  rewrite pairZImag rate value items
        | Pair.pairDifferenceClosedForm
            rate (λ x → Coord.zImag (value x)) items
        | zImagSubtract
            (R291.realScale (Pair.natAsRational (length items))
              (weightedVectorSum rate value items))
            (R291.realScale (Pair.rateSum rate items)
              (vectorSum value items))
        | zImagScale (Pair.natAsRational (length items))
            (weightedVectorSum rate value items)
        | zImagScale (Pair.rateSum rate items)
            (vectorSum value items)
        | weightedZImag rate value items
        | sumZImag value items = refl

completeGraphVectorCovarianceIdentity :
  ∀ {A : Set} →
  (rate : A → ℚ) →
  (value : A → C3.Complex3 F) →
  (items : List A) →
  pairVectorDifferenceSum rate value items
  ≡ closedFormVector rate value items
completeGraphVectorCovarianceIdentity rate value items =
  Algebra.complex3Ext
    (Algebra.complexExt
      (xRealClosed rate value items)
      (xImagClosed rate value items))
    (Algebra.complexExt
      (yRealClosed rate value items)
      (yImagClosed rate value items))
    (Algebra.complexExt
      (zRealClosed rate value items)
      (zImagClosed rate value items))

completeGraphVectorCovarianceIdentityClosed : Bool
completeGraphVectorCovarianceIdentityClosed = true

completeGraphVectorCovarianceIdentityIntroducesNorm : Bool
completeGraphVectorCovarianceIdentityIntroducesNorm = false

completeGraphVectorCovarianceIdentityIntroducesCardinalityTax : Bool
completeGraphVectorCovarianceIdentityIntroducesCardinalityTax = false

clayPromotion : Bool
clayPromotion = false

completeGraphVectorCovarianceIdentityClosedIsTrue :
  completeGraphVectorCovarianceIdentityClosed ≡ true
completeGraphVectorCovarianceIdentityClosedIsTrue = refl
