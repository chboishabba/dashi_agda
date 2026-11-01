module DASHI.Foundations.FiniteLinear.AntiDiagonalKernel where

open import Agda.Builtin.Equality using (_≡_; refl)

open import Base369 using
  ( TriTruth ; tri-low ; tri-mid ; tri-high )
import DASHI.Foundations.Base369TriTruthField as F3
import DASHI.Foundations.FiniteLinear.F3Subspace as Linear

------------------------------------------------------------------------
-- A second, non-code consumer of the finite-subspace API.
--
-- The sum-zero line in F3² is exactly the image of t ↦ (t,-t).  This is the
-- elementary finite-linear pattern underneath diagonal/off-diagonal channel
-- decompositions, kernel/image reasoning and small Gram calculations.
------------------------------------------------------------------------

record Vec2 : Set where
  constructor vec2
  field
    x0 x1 : TriTruth

open Vec2 public

zeroVec2 : Vec2
zeroVec2 = vec2 F3.triZero F3.triZero

addVec2 : Vec2 → Vec2 → Vec2
addVec2 left right =
  vec2
    (F3.triAdd (x0 left) (x0 right))
    (F3.triAdd (x1 left) (x1 right))

scaleVec2 : TriTruth → Vec2 → Vec2
scaleVec2 a value =
  vec2
    (F3.triMul a (x0 value))
    (F3.triMul a (x1 value))

scaleVec2Zero : (a : TriTruth) → scaleVec2 a zeroVec2 ≡ zeroVec2
scaleVec2Zero tri-low = refl
scaleVec2Zero tri-mid = refl
scaleVec2Zero tri-high = refl

vec2Space : Linear.F3Space
vec2Space = record
  { Carrier = Vec2
  ; zero = zeroVec2
  ; add = addVec2
  ; scale = scaleVec2
  ; addZeroZero = refl
  ; scaleZero = scaleVec2Zero
  }

scalarSpace : Linear.F3Space
scalarSpace = record
  { Carrier = TriTruth
  ; zero = F3.triZero
  ; add = F3.triAdd
  ; scale = F3.triMul
  ; addZeroZero = refl
  ; scaleZero = F3.triMul-zeroʳ
  }

sumCoordinates : Vec2 → TriTruth
sumCoordinates value = F3.triAdd (x0 value) (x1 value)

sumMap : Linear.F3LinearMap vec2Space scalarSpace
sumMap = record
  { apply = sumCoordinates
  ; preservesZero = refl
  ; preservesAdd = λ left right →
      Linear.addInterchange
        (x0 left) (x0 right)
        (x1 left) (x1 right)
  ; preservesScale = λ a value →
      Linear.sym (F3.triDistribˡ a (x0 value) (x1 value))
  }

sumZeroLine : Linear.F3Subspace vec2Space
sumZeroLine = Linear.kernel sumMap

negAdd :
  (x y : TriTruth) →
  F3.triNeg (F3.triAdd x y)
  ≡ F3.triAdd (F3.triNeg x) (F3.triNeg y)
negAdd tri-low tri-low = refl
negAdd tri-low tri-mid = refl
negAdd tri-low tri-high = refl
negAdd tri-mid tri-low = refl
negAdd tri-mid tri-mid = refl
negAdd tri-mid tri-high = refl
negAdd tri-high tri-low = refl
negAdd tri-high tri-mid = refl
negAdd tri-high tri-high = refl

negScale :
  (a x : TriTruth) →
  F3.triNeg (F3.triMul a x)
  ≡ F3.triMul a (F3.triNeg x)
negScale tri-low tri-low = refl
negScale tri-low tri-mid = refl
negScale tri-low tri-high = refl
negScale tri-mid tri-low = refl
negScale tri-mid tri-mid = refl
negScale tri-mid tri-high = refl
negScale tri-high tri-low = refl
negScale tri-high tri-mid = refl
negScale tri-high tri-high = refl

antiDiagonal : TriTruth → Vec2
antiDiagonal t = vec2 t (F3.triNeg t)

antiDiagonalMap : Linear.F3LinearMap scalarSpace vec2Space
antiDiagonalMap = record
  { apply = antiDiagonal
  ; preservesZero = refl
  ; preservesAdd = λ left right →
      Linear.cong₂ vec2
        refl
        (negAdd left right)
  ; preservesScale = λ a value →
      Linear.cong₂ vec2
        refl
        (negScale a value)
  }

antiDiagonalLine : Linear.F3Subspace vec2Space
antiDiagonalLine = Linear.imageSubspace antiDiagonalMap

solveAddLeftZero :
  (a b : TriTruth) →
  F3.triAdd a b ≡ F3.triZero →
  b ≡ F3.triNeg a
solveAddLeftZero a b equality =
  Linear.trans
    (Linear.sym (F3.triAdd-identityˡ b))
    (Linear.trans
      (Linear.cong (λ value → F3.triAdd value b)
        (Linear.sym (F3.triAdd-inverseˡ a)))
      (Linear.trans
        (Linear.sym (F3.triAdd-assoc (F3.triNeg a) a b))
        (Linear.trans
          (Linear.cong (F3.triAdd (F3.triNeg a)) equality)
          (F3.triAdd-identityʳ (F3.triNeg a)))))

sumZeroToAntiDiagonal : sumZeroLine Linear.⊆ antiDiagonalLine
sumZeroToAntiDiagonal {vec2 left right} sumZero =
  Linear.imageMember
    left
    (Linear.cong₂ vec2
      refl
      (Linear.sym (solveAddLeftZero left right sumZero)))

antiDiagonalToSumZero : antiDiagonalLine Linear.⊆ sumZeroLine
antiDiagonalToSumZero
  (Linear.imageMember value refl) =
  F3.triAdd-inverseʳ value

sumZeroIsAntiDiagonal : sumZeroLine Linear.≈ₛ antiDiagonalLine
sumZeroIsAntiDiagonal =
  Linear.subspaceEquality
    sumZeroToAntiDiagonal
    antiDiagonalToSumZero

antiDiagonalLow : antiDiagonal tri-low ≡ vec2 tri-low tri-low
antiDiagonalLow = refl

antiDiagonalMid : antiDiagonal tri-mid ≡ vec2 tri-mid tri-high
antiDiagonalMid = refl

antiDiagonalHigh : antiDiagonal tri-high ≡ vec2 tri-high tri-mid
antiDiagonalHigh = refl
