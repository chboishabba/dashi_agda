module DASHI.Moonshine.Y443FutureResidualConsumerExact where

-- Literal source-node reflection observer, not the 80-relator quotient.
-- The classical Coxeter geometric representation is evaluated on the
-- selected twelve-root lattice. JMD source-word attribution unchanged.
-- Exact Python reference: check_y443_residual_observability_20261125.py.
-- Source-written Agda, pending local kernel acceptance.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer using (ℤ; +_; _+_; _-_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Core.ConsumerIndexedResidualRefinementExact as R

z : ℤ
z = + 0

record Vec12 : Set where
  constructor vec
  field
    a b1 c1 d1 e1 b2 c2 d2 e2 b3 c3 d3 : ℤ

open Vec12 public

zeroVec positiveE1 negativeE1 : Vec12
zeroVec = vec z z z z z z z z z z z z
positiveE1 = vec z z z z (+ 1) z z z z z z z
negativeE1 = vec z z z z (z - (+ 1)) z z z z z z z

-- Each row is the original signed simply-laced reflection:
-- v_i -> -v_i + sum_{j adjacent i} v_j.
reflect : Y.Node → Vec12 → Vec12
reflect Y.a (vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3) = vec (z - va + vb1 + vb2 + vb3) vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3
reflect Y.b1 (vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3) = vec va (z - vb1 + va + vc1) vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3
reflect Y.c1 (vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3) = vec va vb1 (z - vc1 + vb1 + vd1) vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3
reflect Y.d1 (vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3) = vec va vb1 vc1 (z - vd1 + vc1 + ve1) ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3
reflect Y.e1 (vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3) = vec va vb1 vc1 vd1 (z - ve1 + vd1) vb2 vc2 vd2 ve2 vb3 vc3 vd3
reflect Y.b2 (vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3) = vec va vb1 vc1 vd1 ve1 (z - vb2 + va + vc2) vc2 vd2 ve2 vb3 vc3 vd3
reflect Y.c2 (vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3) = vec va vb1 vc1 vd1 ve1 vb2 (z - vc2 + vb2 + vd2) vd2 ve2 vb3 vc3 vd3
reflect Y.d2 (vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3) = vec va vb1 vc1 vd1 ve1 vb2 vc2 (z - vd2 + vc2 + ve2) ve2 vb3 vc3 vd3
reflect Y.e2 (vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3) = vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 (z - ve2 + vd2) vb3 vc3 vd3
reflect Y.b3 (vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3) = vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 (z - vb3 + va + vc3) vc3 vd3
reflect Y.c3 (vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3) = vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 (z - vc3 + vb3 + vd3) vd3
reflect Y.d3 (vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3) = vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 (z - vd3 + vc3)

evaluate : Y.Word → Vec12 → Vec12
evaluate [] v = v
evaluate (x ∷ xs) v = reflect x (evaluate xs v)

subtract : Vec12 → Vec12 → Vec12
subtract (vec va vb1 vc1 vd1 ve1 vb2 vc2 vd2 ve2 vb3 vc3 vd3) (vec wa wb1 wc1 wd1 we1 wb2 wc2 wd2 we2 wb3 wc3 wd3) =
  vec (va - wa) (vb1 - wb1) (vc1 - wc1) (vd1 - wd1) (ve1 - we1) (vb2 - wb2) (vc2 - wc2) (vd2 - wd2) (ve2 - we2) (vb3 - wb3) (vc3 - wc3) (vd3 - wd3)

defect : Y.Word → Vec12 → Vec12
defect w v = subtract (evaluate w v) v

jointNow : Vec12 → Vec12 × Vec12
jointNow v = defect Y.spiderRelator v , defect Y.centralInvolutionRelator v

future : Vec12 → ℤ
future v = a (defect Y.spiderRelator (reflect Y.d1 v))

nowZero : jointNow zeroVec ≡ (zeroVec , zeroVec)
nowZero = refl

nowPositive : jointNow positiveE1 ≡ (zeroVec , zeroVec)
nowPositive = refl

nowNegative : jointNow negativeE1 ≡ (zeroVec , zeroVec)
nowNegative = refl

futureZero : future zeroVec ≡ (+ 0)
futureZero = refl

futurePositive : future positiveE1 ≡ (+ 48)
futurePositive = refl

futureNegative : future negativeE1 ≡ (z - (+ 48))
futureNegative = refl

zeroCollision : R.ConsumerRelevantCollision jointNow future
zeroCollision = record
  { left = zeroVec
  ; right = positiveE1
  ; sameSurface = refl
  ; differentOutcome = λ ()
  }

signedCollision : R.ConsumerRelevantCollision jointNow future
signedCollision = record
  { left = positiveE1
  ; right = negativeE1
  ; sameSurface = refl
  ; differentOutcome = λ ()
  }

jointNowInsufficient : R.ConsumerSufficient jointNow future → ⊥
jointNowInsufficient = R.coarseCollisionBlocksSufficiency zeroCollision

everyRepairRetainsSign :
  ∀ {Fine : Set} (observe : Vec12 → Fine) →
  R.ConsumerSufficient observe future →
  observe positiveE1 ≡ observe negativeE1 → ⊥
everyRepairRetainsSign observe sufficient =
  R.everySufficientObserverSeparatesRelevantCollision signedCollision sufficient

-- The full rational/integral future-observation closure and modular radical
-- remain exact external computations; this module proves the concrete
-- depth-zero consumer collision in the original literal word evaluator.
-- No claim of kernel receipt, Monster action, or H07 global geometry.
