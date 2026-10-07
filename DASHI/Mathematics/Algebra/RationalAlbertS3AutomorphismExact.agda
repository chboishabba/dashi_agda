module DASHI.Mathematics.Algebra.RationalAlbertS3AutomorphismExact where

------------------------------------------------------------------------
-- EXPLICIT S3 COORDINATE AUTOMORPHISMS OF H_3(O_Q)
--
-- Permuting the three Hermitian matrix axes gives a concrete finite subgroup
-- of the Albert automorphism group.  With the repository coordinate convention,
-- use
--
--   cycle(a,b,c;x,y,z) = (c,a,b; z,x,y)
--
-- and the 1<->2 transposition
--
--   swap(a,b,c;x,y,z) = (a,c,b; conjugate(x),conjugate(z),conjugate(y)).
--
-- The group relations are source-level consequences of permutation and
-- conjugation involution.  Exact-rational local probing additionally checks
-- preservation of the explicit Jordan product and cubic norm.  Full F4
-- recognition remains strictly stronger.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanProductExact as J

cycleA : A.RationalAlbert → A.RationalAlbert
cycleA (A.albert a b c x y z) = A.albert c a b z x y

swapA : A.RationalAlbert → A.RationalAlbert
swapA (A.albert a b c x y z) =
  A.albert a c b
    (O.octonionConjugate x)
    (O.octonionConjugate z)
    (O.octonionConjugate y)

cycleSquared : A.RationalAlbert → A.RationalAlbert
cycleSquared value = cycleA (cycleA value)

cycleCubedIdentity : ∀ value → cycleA (cycleSquared value) ≡ value
cycleCubedIdentity (A.albert _ _ _ _ _ _) = refl

swapSquaredIdentity : ∀ value → swapA (swapA value) ≡ value
swapSquaredIdentity (A.albert a b c x y z) =
  cong
    (λ triple → A.albert a b c (proj₁ triple) (proj₁ (proj₂ triple)) (proj₂ (proj₂ triple)))
    nested
  where
    open import Data.Product using (_×_; _,_; proj₁; proj₂)
    nested :
      (O.octonionConjugate (O.octonionConjugate x) ,
       (O.octonionConjugate (O.octonionConjugate y) ,
        O.octonionConjugate (O.octonionConjugate z)))
      ≡ (x , (y , z))
    nested rewrite
      O.octonionConjugateInvolutive x |
      O.octonionConjugateInvolutive y |
      O.octonionConjugateInvolutive z = refl

/-- Dihedral presentation: s r s = r^{-1} = r^2. -/
swapCycleSwap : ∀ value →
  swapA (cycleA (swapA value)) ≡ cycleSquared value
swapCycleSwap (A.albert a b c x y z)
  rewrite
    O.octonionConjugateInvolutive x |
    O.octonionConjugateInvolutive y |
    O.octonionConjugateInvolutive z = refl

------------------------------------------------------------------------
-- Recognition sockets for the product/norm preservation theorems.
------------------------------------------------------------------------

CyclePreservesProduct : Set
CyclePreservesProduct =
  (x y : A.RationalAlbert) →
    cycleA (J.jordanProduct x y) ≡ J.jordanProduct (cycleA x) (cycleA y)

SwapPreservesProduct : Set
SwapPreservesProduct =
  (x y : A.RationalAlbert) →
    swapA (J.jordanProduct x y) ≡ J.jordanProduct (swapA x) (swapA y)

CyclePreservesCubic : Set
CyclePreservesCubic =
  (x : A.RationalAlbert) → A.cubicNorm (cycleA x) ≡ A.cubicNorm x

SwapPreservesCubic : Set
SwapPreservesCubic =
  (x : A.RationalAlbert) → A.cubicNorm (swapA x) ≡ A.cubicNorm x

record AlbertS3AutomorphismBoundary : Set where
  constructor albert-s3-automorphism-boundary
  field
    cycleOrderThreePaid : Bool
    swapOrderTwoPaid : Bool
    s3DihedralRelationPaid : Bool
    localExactProductPreservationChecked : Bool
    localExactCubicPreservationChecked : Bool
    agdaProductPreservationPaid : Bool
    agdaCubicPreservationPaid : Bool
    fullF4AutomorphismGroupPaid : Bool
open AlbertS3AutomorphismBoundary public

currentAlbertS3AutomorphismBoundary : AlbertS3AutomorphismBoundary
currentAlbertS3AutomorphismBoundary =
  albert-s3-automorphism-boundary
    true true true true true false false false
