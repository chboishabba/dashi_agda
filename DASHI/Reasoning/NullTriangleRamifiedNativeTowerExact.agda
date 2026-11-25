module DASHI.Reasoning.NullTriangleRamifiedNativeTowerExact where

-- Integral coefficient tower for the already-derived Q3(i,rho) chart.
-- The base is the ORIGINAL compatible Z/3^n tower, not a replacement.
-- These operations do not yet certify ring/field laws or completeness.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Product using (_,_)
open import Data.Vec using ([]; _∷_; Vec)
import DASHI.Algebra.Trit as T
import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope as E
import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteMultiplicationCompatibleExact as A
import DASHI.Reasoning.NullTriangleOrderedUltrametricCubeExact as P
import DASHI.Reasoning.NullTriangleNativePairedRefinementExact as Pair
import DASHI.Reasoning.NullTriangleNativeH05ObserverExact as H

Z3 : Set
Z3 = Q.TriadicInverseLimitPoint

toSourceTrit : T.Trit → E.Trit
toSourceTrit T.neg = E.neg
toSourceTrit T.zer = E.zer
toSourceTrit T.pos = E.pos

digit : T.Trit → Z3
digit t = Q.streamToInverseLimit (λ { zero → toSourceTrit t ; (suc _) → E.zer })

zero3 : Z3
zero3 = digit T.zer

-- Multiplication by three is the literal low-order zero prepend.
times3 : Z3 → Z3
times3 x = Q.triadic-limit-point
  (λ { zero → E.[] ; (suc n) → E.zer E.∷ Q.coordinate x n })
  (λ { zero → refl ; (suc n) → cong (E.zer E.∷_) (Q.compatible x n) })

record Gaussian : Set where
  constructor gaussian
  field re im : Z3
open Gaussian public

zeroG : Gaussian
zeroG = gaussian zero3 zero3

addG : Gaussian → Gaussian → Gaussian
addG (gaussian a b) (gaussian c d) =
  gaussian (A.addLimit a c) (A.addLimit b d)

negG : Gaussian → Gaussian
negG (gaussian a b) = gaussian (A.negateLimit a) (A.negateLimit b)

subG : Gaussian → Gaussian → Gaussian
subG a b = addG a (negG b)

mulG : Gaussian → Gaussian → Gaussian
mulG (gaussian a b) (gaussian c d) =
  gaussian
    (A.addLimit (A.multiplyLimit a c) (A.negateLimit (A.multiplyLimit b d)))
    (A.addLimit (A.multiplyLimit a d) (A.multiplyLimit b c))

threeG : Gaussian → Gaussian
threeG (gaussian a b) = gaussian (times3 a) (times3 b)

digitG : P.Point → Gaussian
digitG (a ∷ b ∷ []) = gaussian (digit a) (digit b)

record Ramified : Set where
  constructor coefficients
  field constant linear : Gaussian
open Ramified public

zeroK : Ramified
zeroK = coefficients zeroG zeroG

addK : Ramified → Ramified → Ramified
addK (coefficients a b) (coefficients c d) =
  coefficients (addG a c) (addG b d)

negK : Ramified → Ramified
negK (coefficients a b) = coefficients (negG a) (negG b)

-- pi^2=-3-3*pi, so (a+b*pi)(c+d*pi)
-- = (ac-3bd)+(ad+bc-3bd)*pi.
mulK : Ramified → Ramified → Ramified
mulK (coefficients a b) (coefficients c d) =
  let bd3 = threeG (mulG b d)
  in coefficients
    (subG (mulG a c) bd3)
    (subG (addG (mulG a d) (mulG b c)) bd3)

-- Direct pi multiplication and low-digit Horner step on the source tower.
piStep : Ramified → Ramified
piStep (coefficients a b) =
  coefficients (negG (threeG b)) (subG a (threeG b))

prepend : P.Point → Ramified → Ramified
prepend r (coefficients a b) =
  coefficients (subG (digitG r) (threeG b)) (subG a (threeG b))

decodeEven : ∀ {n} → Vec P.Point n → Ramified
decodeEven [] = zeroK
decodeEven (r ∷ rs) = prepend r (decodeEven rs)

decodeOdd : ∀ {n} → Vec P.Point n → T.Trit → Ramified
decodeOdd [] t = coefficients (digitG (t ∷ T.zer ∷ [])) zeroG
decodeOdd (r ∷ rs) t = prepend r (decodeOdd rs t)

observerCoordinate : H.Observer → Ramified
observerCoordinate o with Pair.observerPairs o
... | ds , t = decodeOdd ds t

-- The native paired-prefix theorem compiles directly to an integral
-- coefficient tower Horner step, retaining the ninth trit.
decodePairedPrefix : ∀ {n} (a b : T.Trit) (ds : Vec P.Point n) (t : T.Trit) →
  decodeOdd ((a ∷ b ∷ []) ∷ ds) t ≡ prepend (a ∷ b ∷ []) (decodeOdd ds t)
decodePairedPrefix a b ds t = refl

-- Compare towers by all original finite coordinates, not by equality of
-- proof-bearing functions. Zero/infinite valuation is not a Nat sentinel.
SameZ3 : Z3 → Z3 → Set
SameZ3 x y = (n : Nat) → Q.coordinate x n ≡ Q.coordinate y n

-- Further obligations: the ordinary integer interpretation of finite mul,
-- ring laws; the nonzero/unit and ramified valuation lemmas, completion,
-- inverse and actual pi-digit tail/carry equality in the source setoid.
