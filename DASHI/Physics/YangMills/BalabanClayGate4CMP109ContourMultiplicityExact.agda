module DASHI.Physics.YangMills.BalabanClayGate4CMP109ContourMultiplicityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ShortestContourEnumerationExact as Contours

------------------------------------------------------------------------
-- Exact contour-family multiplicity for every four-dimensional displacement.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- G(y,x) contains every ordering of the nonzero coordinate segments.  Therefore
-- its size is s!, where s is the number of active coordinate directions.  It is
-- 24 only in the four-active case.  Since s <= 4, the complete theorem is an
-- executable sixteen-case computation over the zero/nonzero status of the four
-- signed coordinate counts.
------------------------------------------------------------------------

factorial : Nat → Nat
factorial zero = suc zero
factorial (suc value) = suc value * factorial value

isActive : Contours.SignedCount → Nat
isActive (Contours.signedCount direction zero) = zero
isActive (Contours.signedCount direction (suc count)) = suc zero

activeDirectionCount : Contours.Displacement4 → Nat
activeDirectionCount displacement =
  isActive (Contours.coordinate0 displacement) +
  (isActive (Contours.coordinate1 displacement) +
  (isActive (Contours.coordinate2 displacement) +
   isActive (Contours.coordinate3 displacement)))

cmp109ContourFamilyCardinality : ∀ displacement →
  Contours.listLength
    (Contours.cmp109ShortestContourOrders displacement)
  ≡ factorial (activeDirectionCount displacement)
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 zero)
    (Contours.signedCount d1 zero)
    (Contours.signedCount d2 zero)
    (Contours.signedCount d3 zero)) = refl
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 (suc n0))
    (Contours.signedCount d1 zero)
    (Contours.signedCount d2 zero)
    (Contours.signedCount d3 zero)) = refl
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 zero)
    (Contours.signedCount d1 (suc n1))
    (Contours.signedCount d2 zero)
    (Contours.signedCount d3 zero)) = refl
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 zero)
    (Contours.signedCount d1 zero)
    (Contours.signedCount d2 (suc n2))
    (Contours.signedCount d3 zero)) = refl
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 zero)
    (Contours.signedCount d1 zero)
    (Contours.signedCount d2 zero)
    (Contours.signedCount d3 (suc n3))) = refl
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 (suc n0))
    (Contours.signedCount d1 (suc n1))
    (Contours.signedCount d2 zero)
    (Contours.signedCount d3 zero)) = refl
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 (suc n0))
    (Contours.signedCount d1 zero)
    (Contours.signedCount d2 (suc n2))
    (Contours.signedCount d3 zero)) = refl
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 (suc n0))
    (Contours.signedCount d1 zero)
    (Contours.signedCount d2 zero)
    (Contours.signedCount d3 (suc n3))) = refl
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 zero)
    (Contours.signedCount d1 (suc n1))
    (Contours.signedCount d2 (suc n2))
    (Contours.signedCount d3 zero)) = refl
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 zero)
    (Contours.signedCount d1 (suc n1))
    (Contours.signedCount d2 zero)
    (Contours.signedCount d3 (suc n3))) = refl
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 zero)
    (Contours.signedCount d1 zero)
    (Contours.signedCount d2 (suc n2))
    (Contours.signedCount d3 (suc n3))) = refl
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 (suc n0))
    (Contours.signedCount d1 (suc n1))
    (Contours.signedCount d2 (suc n2))
    (Contours.signedCount d3 zero)) = refl
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 (suc n0))
    (Contours.signedCount d1 (suc n1))
    (Contours.signedCount d2 zero)
    (Contours.signedCount d3 (suc n3))) = refl
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 (suc n0))
    (Contours.signedCount d1 zero)
    (Contours.signedCount d2 (suc n2))
    (Contours.signedCount d3 (suc n3))) = refl
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 zero)
    (Contours.signedCount d1 (suc n1))
    (Contours.signedCount d2 (suc n2))
    (Contours.signedCount d3 (suc n3))) = refl
cmp109ContourFamilyCardinality
  (Contours.displacement4
    (Contours.signedCount d0 (suc n0))
    (Contours.signedCount d1 (suc n1))
    (Contours.signedCount d2 (suc n2))
    (Contours.signedCount d3 (suc n3))) = refl

zeroActiveContourCount :
  factorial zero ≡ 1
zeroActiveContourCount = refl

oneActiveContourCount :
  factorial 1 ≡ 1
oneActiveContourCount = refl

twoActiveContourCount :
  factorial 2 ≡ 2
twoActiveContourCount = refl

threeActiveContourCount :
  factorial 3 ≡ 6
threeActiveContourCount = refl

fourActiveContourCount :
  factorial 4 ≡ 24
fourActiveContourCount = refl

cmp109ActiveAxisFactorialMultiplicityLevel : ProofLevel
cmp109ActiveAxisFactorialMultiplicityLevel = computed

cmp109ContourWeightNotUniform24Level : ProofLevel
cmp109ContourWeightNotUniform24Level = machineChecked
