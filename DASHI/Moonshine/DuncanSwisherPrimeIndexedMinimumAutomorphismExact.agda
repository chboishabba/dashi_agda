module DASHI.Moonshine.DuncanSwisherPrimeIndexedMinimumAutomorphismExact where

------------------------------------------------------------------------
-- GENUINE PRIME-INDEXED MINIMUM AUTOMORPHISM WITNESS
--
-- PRIMARY SOURCE
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- CROSS-CHECK / AUTOMORPHISM SOURCE
-- John Voight, "Quaternion Algebras", GTM 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
-- Chapter 42 DOI: 10.1007/978-3-030-56694-4_42.
--
-- PROOF-STRENGTH REPAIR
--
-- The older `Deligne.MinimumAutomorphismWitness` only selected one of the
-- finite automorphism TYPES and recorded its order.  It did not quantify over
-- the actual supersingular locus, so its name overstated the theorem carried.
--
-- The record below is the canonical replacement.  A genuine minimum contains
-- an actual prime-indexed point, attainment, and a lower-bound theorem over
-- EVERY point of that declared locus.
--
-- We instantiate it on the existing same-object p=11, p=37 and p=43 geometric
-- carriers.  For p=5,7,13 we also retain the source-shaped singleton control
-- loci used by Duncan--Swisher Theorem 1.2.  No reciprocal stack-sheet count is
-- used as an elliptic automorphism order.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_; z≤n; s≤s)

import DASHI.Moonshine.DuncanSwisherDeligneAutomorphismDepthBridgeExact as Deligne
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as P11
import DASHI.Moonshine.P37SageSupersingularFrobeniusExact as P37
import DASHI.Moonshine.P43NonOggFullLevel2DeuringControlExact as P43

record SupersingularMinimumAutWitness
    (Point : Set)
    (autOrder : Point → Nat) : Set where
  constructor supersingular-minimum-aut-witness
  field
    attainer : Point
    minimumOrder : Nat
    attains : autOrder attainer ≡ minimumOrder
    lowerBound : (x : Point) → minimumOrder ≤ autOrder x

open SupersingularMinimumAutWitness public

minimumIsActuallyAttained :
  ∀ {Point : Set} {autOrder : Point → Nat} →
  (W : SupersingularMinimumAutWitness Point autOrder) →
  autOrder (attainer W) ≡ minimumOrder W
minimumIsActuallyAttained = attains

minimumBoundsEveryPoint :
  ∀ {Point : Set} {autOrder : Point → Nat} →
  (W : SupersingularMinimumAutWitness Point autOrder) →
  (x : Point) → minimumOrder W ≤ autOrder x
minimumBoundsEveryPoint = lowerBound

------------------------------------------------------------------------
-- Standard p>3 full elliptic automorphism order from j-type.
------------------------------------------------------------------------

fullAutFromType : Deligne.SupersingularAutomorphismType → Nat
fullAutFromType = Deligne.fullAutomorphismOrder

depthFromType : Deligne.SupersingularAutomorphismType → Nat
depthFromType = Deligne.deligneFirstPoleDepth

minimumDepth :
  ∀ {Point : Set}
    (autType : Point → Deligne.SupersingularAutomorphismType) →
    SupersingularMinimumAutWitness Point (λ x → fullAutFromType (autType x)) →
    Nat
minimumDepth autType W = depthFromType (autType (attainer W))

minimumDepthDoublesToMinimumAut :
  ∀ {Point : Set}
    (autType : Point → Deligne.SupersingularAutomorphismType) →
    (W : SupersingularMinimumAutWitness Point
      (λ x → fullAutFromType (autType x))) →
    2 * minimumDepth autType W ≡ minimumOrder W
minimumDepthDoublesToMinimumAut autType W =
  trans
    (Deligne.firstPoleDepthDoublesToFullAutomorphismOrder
      (autType (attainer W)))
    (attains W)

------------------------------------------------------------------------
-- p=11: actual geometric j={0,1728} locus.
------------------------------------------------------------------------

p11AutType : P11.P11SupersingularJ → Deligne.SupersingularAutomorphismType
p11AutType P11.jZeroSS = Deligne.jZeroExceptional
p11AutType P11.j1728SS = Deligne.j1728Exceptional

p11FullAutOrder : P11.P11SupersingularJ → Nat
p11FullAutOrder j = fullAutFromType (p11AutType j)

p11Minimum : SupersingularMinimumAutWitness P11.P11SupersingularJ p11FullAutOrder
p11Minimum = supersingular-minimum-aut-witness
  P11.j1728SS 4 refl lower
  where
  lower : (j : P11.P11SupersingularJ) → 4 ≤ p11FullAutOrder j
  lower P11.jZeroSS = s≤s (s≤s (s≤s (s≤s z≤n)))
  lower P11.j1728SS = s≤s (s≤s (s≤s (s≤s z≤n)))

p11MinimumOrderIsFour : minimumOrder p11Minimum ≡ 4
p11MinimumOrderIsFour = refl

p11MinimumDepthIsTwo : minimumDepth p11AutType p11Minimum ≡ 2
p11MinimumDepthIsTwo = refl

------------------------------------------------------------------------
-- p=37: actual Sage-labelled locus.  None of 8,27a+23,10a+20 is j=0 or
-- j=1728=26 mod 37, so every point has generic full automorphism order 2.
------------------------------------------------------------------------

p37AutType : P37.P37SupersingularJ → Deligne.SupersingularAutomorphismType
p37AutType P37.j8 = Deligne.ordinaryType
p37AutType P37.j27aPlus23 = Deligne.ordinaryType
p37AutType P37.j10aPlus20 = Deligne.ordinaryType

p37FullAutOrder : P37.P37SupersingularJ → Nat
p37FullAutOrder j = fullAutFromType (p37AutType j)

p37Minimum : SupersingularMinimumAutWitness P37.P37SupersingularJ p37FullAutOrder
p37Minimum = supersingular-minimum-aut-witness
  P37.j8 2 refl lower
  where
  lower : (j : P37.P37SupersingularJ) → 2 ≤ p37FullAutOrder j
  lower P37.j8 = s≤s (s≤s z≤n)
  lower P37.j27aPlus23 = s≤s (s≤s z≤n)
  lower P37.j10aPlus20 = s≤s (s≤s z≤n)

p37MinimumOrderIsTwo : minimumOrder p37Minimum ≡ 2
p37MinimumOrderIsTwo = refl

p37MinimumDepthIsOne : minimumDepth p37AutType p37Minimum ≡ 1
p37MinimumDepthIsOne = refl

------------------------------------------------------------------------
-- p=43: actual Deuring/Legendre coarse locus.  j1728 is exceptional order 4;
-- j41 and the quadratic pair are generic order 2, so the minimum is genuinely
-- attained by an actual point and bounded over the whole four-point locus.
------------------------------------------------------------------------

p43AutType : P43.P43GeometricJ → Deligne.SupersingularAutomorphismType
p43AutType P43.j1728 = Deligne.j1728Exceptional
p43AutType P43.j41 = Deligne.ordinaryType
p43AutType P43.jQuadratic0 = Deligne.ordinaryType
p43AutType P43.jQuadratic1 = Deligne.ordinaryType

p43FullAutOrder : P43.P43GeometricJ → Nat
p43FullAutOrder j = fullAutFromType (p43AutType j)

p43Minimum : SupersingularMinimumAutWitness P43.P43GeometricJ p43FullAutOrder
p43Minimum = supersingular-minimum-aut-witness
  P43.j41 2 refl lower
  where
  lower : (j : P43.P43GeometricJ) → 2 ≤ p43FullAutOrder j
  lower P43.j1728 = s≤s (s≤s z≤n)
  lower P43.j41 = s≤s (s≤s z≤n)
  lower P43.jQuadratic0 = s≤s (s≤s z≤n)
  lower P43.jQuadratic1 = s≤s (s≤s z≤n)

p43MinimumOrderIsTwo : minimumOrder p43Minimum ≡ 2
p43MinimumOrderIsTwo = refl

p43MinimumDepthIsOne : minimumDepth p43AutType p43Minimum ≡ 1
p43MinimumDepthIsOne = refl

------------------------------------------------------------------------
-- Source-shaped singleton controls p=5,7,13.  These are explicit loci, so the
-- minimum proof is exhaustive rather than a bare selected automorphism type.
------------------------------------------------------------------------

data P5SupersingularPoint : Set where p5jZero : P5SupersingularPoint
data P7SupersingularPoint : Set where p7j1728 : P7SupersingularPoint
data P13SupersingularPoint : Set where p13Generic : P13SupersingularPoint

p5AutType : P5SupersingularPoint → Deligne.SupersingularAutomorphismType
p5AutType p5jZero = Deligne.jZeroExceptional
p7AutType : P7SupersingularPoint → Deligne.SupersingularAutomorphismType
p7AutType p7j1728 = Deligne.j1728Exceptional
p13AutType : P13SupersingularPoint → Deligne.SupersingularAutomorphismType
p13AutType p13Generic = Deligne.ordinaryType

p5Minimum : SupersingularMinimumAutWitness P5SupersingularPoint
  (λ x → fullAutFromType (p5AutType x))
p5Minimum = supersingular-minimum-aut-witness p5jZero 6 refl
  (λ { p5jZero → s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) })

p7Minimum : SupersingularMinimumAutWitness P7SupersingularPoint
  (λ x → fullAutFromType (p7AutType x))
p7Minimum = supersingular-minimum-aut-witness p7j1728 4 refl
  (λ { p7j1728 → s≤s (s≤s (s≤s (s≤s z≤n))) })

p13Minimum : SupersingularMinimumAutWitness P13SupersingularPoint
  (λ x → fullAutFromType (p13AutType x))
p13Minimum = supersingular-minimum-aut-witness p13Generic 2 refl
  (λ { p13Generic → s≤s (s≤s z≤n) })

p5MinimumDepthIsThree : minimumDepth p5AutType p5Minimum ≡ 3
p5MinimumDepthIsThree = refl
p7MinimumDepthIsTwo : minimumDepth p7AutType p7Minimum ≡ 2
p7MinimumDepthIsTwo = refl
p13MinimumDepthIsOne : minimumDepth p13AutType p13Minimum ≡ 1
p13MinimumDepthIsOne = refl

record DuncanSwisherPrimeIndexedMinimumBoundary : Set where
  field
    minimumQuantifiesOverDeclaredLocus : Bool
    attainmentCarried : Bool
    lowerBoundOverEveryPointCarried : Bool
    p11ActualCarrierMinimumConstructed : Bool
    p37ActualCarrierMinimumConstructed : Bool
    p43ActualCarrierMinimumConstructed : Bool
    p5p7p13SingletonMinimaExhaustive : Bool
    reciprocalStackSheetUsedAsAutOrder : Bool
    oldTypeOnlyWitnessRemainsCanonical : Bool

canonicalDuncanSwisherPrimeIndexedMinimumBoundary :
  DuncanSwisherPrimeIndexedMinimumBoundary
canonicalDuncanSwisherPrimeIndexedMinimumBoundary = record
  { minimumQuantifiesOverDeclaredLocus = true
  ; attainmentCarried = true
  ; lowerBoundOverEveryPointCarried = true
  ; p11ActualCarrierMinimumConstructed = true
  ; p37ActualCarrierMinimumConstructed = true
  ; p43ActualCarrierMinimumConstructed = true
  ; p5p7p13SingletonMinimaExhaustive = true
  ; reciprocalStackSheetUsedAsAutOrder = false
  ; oldTypeOnlyWitnessRemainsCanonical = false
  }
