module DASHI.Mathematics.Complexity.PNPSignedCharacterTailExact where

-- Classical C3 character algebra and Cauchy--Schwarz. Reuse the existing
-- actual rational finite Gram theorem, not the abstract CS input record.
-- Source-written; native elaboration pending.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_)
import Data.Rational.Properties as Q
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as CS

record Hist : Set where
  constructor hist
  field h0 h1 h2 : ℚ
open Hist public

conv : Hist → Hist → Hist
conv (hist a b c) (hist d e f) =
  hist (a * d + b * f + c * e)
       (a * e + b * d + c * f)
       (a * f + b * e + c * d)

histEq : ∀ {a b c d e f} → a ≡ d → b ≡ e → c ≡ f →
  hist a b c ≡ hist d e f
histEq refl refl refl = refl

assoc : ∀ a b c → conv (conv a b) c ≡ conv a (conv b c)
assoc (hist a b c) (hist d e f) (hist g h i) =
  histEq (solve vars) (solve vars) (solve vars)
  where vars = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ []

Nonneg : Hist → Set
Nonneg (hist a b c) = (0ℚ ≤ a) × (0ℚ ≤ b) × (0ℚ ≤ c)

Below : Hist → Hist → Set
Below (hist a b c) (hist d e f) = (a ≤ d) × (b ≤ e) × (c ≤ f)

mono : ∀ {a b c d} → Nonneg a → Nonneg b → Nonneg c → Nonneg d →
  Below a c → Below b d → Below (conv a b) (conv c d)
mono {hist a b c} {hist d e f} {hist g h i} {hist j k l} (a0 , a1 , a2) (b0 , b1 , b2) (c0 , c1 , c2) (d0 , d1 , d2)
     (ac0 , ac1 , ac2) (bd0 , bd1 , bd2) =
  Q.+-mono-≤ (Q.+-mono-≤
    (CS.nonnegativeProductMonotone a0 b0 c0 d0 ac0 bd0)
    (CS.nonnegativeProductMonotone a1 b2 c1 d2 ac1 bd2))
    (CS.nonnegativeProductMonotone a2 b1 c2 d1 ac2 bd1) ,
  Q.+-mono-≤ (Q.+-mono-≤
    (CS.nonnegativeProductMonotone a0 b1 c0 d1 ac0 bd1)
    (CS.nonnegativeProductMonotone a1 b0 c1 d0 ac1 bd0))
    (CS.nonnegativeProductMonotone a2 b2 c2 d2 ac2 bd2) ,
  Q.+-mono-≤ (Q.+-mono-≤
    (CS.nonnegativeProductMonotone a0 b2 c0 d2 ac0 bd2)
    (CS.nonnegativeProductMonotone a1 b1 c1 d1 ac1 bd1))
    (CS.nonnegativeProductMonotone a2 b0 c2 d0 ac2 bd0)

-- Signed coefficient basis a+b omega, omega^2=-1-omega.
ca cb : Hist → ℚ
ca (hist a b c) = a - c
cb (hist a b c) = b - c

energy : Hist → ℚ
energy h = ca h * ca h - ca h * cb h + cb h * cb h

characterA : ∀ h k → ca (conv h k) ≡ ca h * ca k - cb h * cb k
characterA (hist a b c) (hist d e f) =
  solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])

characterB : ∀ h k → cb (conv h k) ≡ ca h * cb k + cb h * ca k - cb h * cb k
characterB (hist a b c) (hist d e f) =
  solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])

energyProduct : ∀ h k → energy (conv h k) ≡ energy h * energy k
energyProduct (hist a b c) (hist d e f) =
  solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])

u v : Hist → ℚ
u (hist a b c) = a + a - b - c
v = cb

norm4 : Hist → ℚ
norm4 h = CS.square (u h) + CS.square (v h) + CS.square (v h) + CS.square (v h)

norm4Exact : ∀ h → norm4 h ≡ energy h + energy h + energy h + energy h
norm4Exact (hist a b c) = solve (a ∷ b ∷ c ∷ [])

-- 2 * unweighted directional contrast of the product.
-- Rotate one input histogram BEFORE this fold for other boundary phases.
pairProjection : Hist → Hist → ℚ
pairProjection h k = u h * u k - (v h * v k + v h * v k + v h * v k)

projectionExact : ∀ h k →
  pairProjection h k ≡ u (conv h k) + u (conv h k)
projectionExact (hist a b c) (hist d e f) =
  solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])

-- Flatten real and three repeated imaginary coordinates (sqrt(3) avoided).
-- The omitted boundary list is finite and indexed; no arbitrary missing
-- labels are claimed to have small energy.
flatten : List (Hist × Hist) → List CS.Pair
flatten [] = []
flatten ((h , k) ∷ xs) =
  (u h , u k) ∷ (v h , - v k) ∷ (v h , - v k) ∷ (v h , - v k) ∷ flatten xs

projectionSum : List (Hist × Hist) → ℚ
projectionSum [] = 0ℚ
projectionSum ((h , k) ∷ xs) = pairProjection h k + projectionSum xs

leftEnergy4 rightEnergy4 : List (Hist × Hist) → ℚ
leftEnergy4 [] = 0ℚ
leftEnergy4 ((h , k) ∷ xs) = norm4 h + leftEnergy4 xs
rightEnergy4 [] = 0ℚ
rightEnergy4 ((h , k) ∷ xs) = norm4 k + rightEnergy4 xs

dotExact : ∀ xs → CS.pairDot (flatten xs) ≡ projectionSum xs
dotExact [] = refl
dotExact ((h , k) ∷ xs) rewrite dotExact xs =
  solve (u h ∷ u k ∷ v h ∷ v k ∷ projectionSum xs ∷ [])

leftExact : ∀ xs → CS.leftNormSquared (flatten xs) ≡ leftEnergy4 xs
leftExact [] = refl
leftExact ((h , k) ∷ xs) rewrite leftExact xs =
  solve (u h ∷ v h ∷ leftEnergy4 xs ∷ [])

rightExact : ∀ xs → CS.rightNormSquared (flatten xs) ≡ rightEnergy4 xs
rightExact [] = refl
rightExact ((h , k) ∷ xs) rewrite rightExact xs =
  solve (u k ∷ v k ∷ rightEnergy4 xs ∷ [])

-- (2 sum contrast)^2 <= (4 sum left energy)(4 sum right energy).
-- This is exactly the directional squared Cauchy tail certificate,
-- with no square roots or assumed complex field.
boundaryTailSquared : ∀ xs →
  CS.square (projectionSum xs) ≤ leftEnergy4 xs * rightEnergy4 xs
boundaryTailSquared xs =
  subst (λ r → CS.square (projectionSum xs) ≤ leftEnergy4 xs * r) (rightExact xs)
    (subst (λ l → CS.square (projectionSum xs) ≤ l * CS.rightNormSquared (flatten xs)) (leftExact xs)
      (subst (λ p → CS.square p ≤ CS.leftNormSquared (flatten xs) * CS.rightNormSquared (flatten xs))
        (dotExact xs) (CS.finiteCauchySchwarzSquared (flatten xs))))

pairSwap : ∀ sign x y → (- sign) * (y - x) ≡ sign * (x - y)
pairSwap sign x y = solve (sign ∷ x ∷ y ∷ [])

-- A concrete involution, not merely equality of its scalar observation.
open import Data.Rational.Properties using (+-inverseˡ)
open import Algebra.Properties.Group as Group
module AddGroup = Group Q.+-0-group

OrientedPair : Set
OrientedPair = ℚ × (ℚ × ℚ)

swapPair : OrientedPair → OrientedPair
swapPair (s , x , y) = (- s , y , x)

swapInvolutive : ∀ p → swapPair (swapPair p) ≡ p
swapInvolutive (s , x , y) = cong (λ t → t , x , y) (AddGroup.⁻¹-involutive s)

observe : OrientedPair → ℚ
observe (s , x , y) = s * (x - y)

swapPreserves : ∀ p → observe (swapPair p) ≡ observe p
swapPreserves (s , x , y) = pairSwap s x y
