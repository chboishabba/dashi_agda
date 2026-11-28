module DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Prove the full finite periodic lattice Hodge identity on the literal
-- side-four four-torus, directly over exact rationals:
--
--   sum_{x,mu,nu} |d_nu h_mu|^2
--     = sum_{x,mu<nu} |d_mu h_nu-d_nu h_mu|^2
--       + sum_x |sum_mu delta_mu h_mu|^2.
--
-- The proof constructs cyclic shifts, proves finite reindexing, derives
-- summation by parts, proves mixed differences commute pointwise, and closes
-- the six cross terms.  No function extensionality or opaque equality between
-- fields is assumed.  The scalar theorem is then summed over the three literal
-- su(2) coordinates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (_∷_; [])
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier public using
  (CyclicIndex; Axis4; Product; pair; four; zeroᵢ; sucᵢ)
open import DASHI.Physics.YangMills.BalabanPath4PhysicalFibreMatchExact using
  (index0; index1; index2; index3)


------------------------------------------------------------------------
-- Explicit ring-solver helpers.  These avoid tactic application syntax that
-- is not accepted by the current Agda 2.9 ring-solver macro.
------------------------------------------------------------------------

sumSitesSubtractNeg : ∀ a b → a + (- b) ≡ a - b
sumSitesSubtractNeg a b =
  ℚRing.solve (a ∷ b ∷ [])

multiplyCommutative : ∀ a b → a * b ≡ b * a
multiplyCommutative a b =
  ℚRing.solve (a ∷ b ∷ [])

forwardMinusTest : ∀ a b c → (a - b) * c ≡ a * c - b * c
forwardMinusTest a b c =
  ℚRing.solve (a ∷ b ∷ c ∷ [])

subtractIsNeg : ∀ a b → a - b ≡ - (b - a)
subtractIsNeg a b =
  ℚRing.solve (a ∷ b ∷ [])

backwardMinusTest : ∀ a b c → a * b - a * c ≡ a * (b - c)
backwardMinusTest a b c =
  ℚRing.solve (a ∷ b ∷ c ∷ [])

negSubToAddNeg : ∀ a b → - (a - b) ≡ b + (- a)
negSubToAddNeg a b =
  ℚRing.solve (a ∷ b ∷ [])

subtractSubtract : ∀ p q r s →
  (p - q) - (r - s) ≡ (p - r) - (q - s)
subtractSubtract p q r s =
  ℚRing.solve (p ∷ q ∷ r ∷ s ∷ [])

normDiffSiteHelper : ∀ a b →
  (a - b) * (a - b) ≡ (a * a + b * b) + (- ((+ 2 / 1) * (a * b)))
normDiffSiteHelper a b =
  ℚRing.solve (a ∷ b ∷ [])

addNegToSub : ∀ a b c → (a + b) + (- c) ≡ a + b - c
addNegToSub a b c =
  ℚRing.solve (a ∷ b ∷ c ∷ [])

norm4SiteHelper : ∀ a b c d →
  (a + (b + (c + d))) * (a + (b + (c + d)))
  ≡ ((a * a + b * b) + (c * c + d * d))
    + ((+ 2 / 1) * (a * b + (a * c + (a * d + (b * c + (b * d + c * d))))))
norm4SiteHelper a b c d =
  ℚRing.solve (a ∷ b ∷ c ∷ d ∷ [])

assoc4Zero : ∀ a b c d → a + (b + (c + (d + 0ℚ))) ≡ ((a + b) + c) + d
assoc4Zero a b c d =
  ℚRing.solve (a ∷ b ∷ c ∷ d ∷ [])

crossAssoc3 : ∀ a b c → a + (b + c) ≡ (a + b) + c
crossAssoc3 a b c =
  ℚRing.solve (a ∷ b ∷ c ∷ [])

crossAssoc4 : ∀ a b c d → a + ((b + c) + d) ≡ ((a + b) + c) + d
crossAssoc4 a b c d =
  ℚRing.solve (a ∷ b ∷ c ∷ d ∷ [])

crossAssoc5 : ∀ a b c d e → a + (((b + c) + d) + e) ≡ (((a + b) + c) + d) + e
crossAssoc5 a b c d e =
  ℚRing.solve (a ∷ b ∷ c ∷ d ∷ e ∷ [])

crossAssoc6 : ∀ a b c d e f →
  a + ((((b + c) + d) + e) + f) ≡ (((((a + b) + c) + d) + e) + f)
crossAssoc6 a b c d e f =
  ℚRing.solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ [])

norm4Combine : ∀ s1 s2 s3 s4 c12 c13 c14 c23 c24 c34 →
  (s1 + s2 + s3 + s4)
    + ((+ 2 / 1) * (c12 + c13 + c14 + c23 + c24 + c34))
  ≡ (((s1 + s2) + s3) + s4)
    + ((+ 2 / 1) * (((((c12 + c13) + c14) + c23) + c24) + c34))
norm4Combine s1 s2 s3 s4 c12 c13 c14 c23 c24 c34 =
  ℚRing.solve
    (s1 ∷ s2 ∷ s3 ∷ s4 ∷ c12 ∷ c13 ∷ c14 ∷ c23 ∷ c24 ∷ c34 ∷ [])

hodgeFinal16 : ∀
  g00 g10 g20 g30 g01 g11 g21 g31 g02 g12 g22 g32 g03 g13 g23 g33
  c01 c02 c03 c12 c13 c23 →
  g00 + g10 + g20 + g30 + g01 + g11 + g21 + g31
    + g02 + g12 + g22 + g32 + g03 + g13 + g23 + g33
  ≡
    ((g01 + g10 - (+ 2 / 1) * c01)
      + (g02 + g20 - (+ 2 / 1) * c02)
      + (g03 + g30 - (+ 2 / 1) * c03)
      + (g12 + g21 - (+ 2 / 1) * c12)
      + (g13 + g31 - (+ 2 / 1) * c13)
      + (g23 + g32 - (+ 2 / 1) * c23))
    + (g00 + g11 + g22 + g33
        + (+ 2 / 1) * (c01 + c02 + c03 + c12 + c13 + c23))
hodgeFinal16
  g00 g10 g20 g30 g01 g11 g21 g31 g02 g12 g22 g32 g03 g13 g23 g33
  c01 c02 c03 c12 c13 c23 =
  ℚRing.solve
    (g00 ∷ g10 ∷ g20 ∷ g30 ∷ g01 ∷ g11 ∷ g21 ∷ g31 ∷
     g02 ∷ g12 ∷ g22 ∷ g32 ∷ g03 ∷ g13 ∷ g23 ∷ g33 ∷
     c01 ∷ c02 ∷ c03 ∷ c12 ∷ c13 ∷ c23 ∷ [])

physicalCombine : ∀ cx cy cz dx dy dz →
  (cx + dx) + (cy + dy) + (cz + dz) ≡ (cx + cy + cz) + (dx + dy + dz)
physicalCombine cx cy cz dx dy dz =
  ℚRing.solve (cx ∷ cy ∷ cz ∷ dx ∷ dy ∷ dz ∷ [])


sumIndex4Next4 : ∀ a b c d →
  b + (c + (d + (a + 0ℚ))) ≡ a + (b + (c + (d + 0ℚ)))
sumIndex4Next4 a b c d =
  ℚRing.solve (a ∷ b ∷ c ∷ d ∷ [])

sumIndex4Previous4 : ∀ a b c d →
  d + (a + (b + (c + 0ℚ))) ≡ a + (b + (c + (d + 0ℚ)))
sumIndex4Previous4 a b c d =
  ℚRing.solve (a ∷ b ∷ c ∷ d ∷ [])

sumIndex4Add8 : ∀ a b c d e f g h →
  (a + e) + ((b + f) + ((c + g) + ((d + h) + 0ℚ)))
  ≡ (a + (b + (c + (d + 0ℚ)))) + (e + (f + (g + (h + 0ℚ))))
sumIndex4Add8 a b c d e f g h =
  ℚRing.solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ [])

sumIndex4Neg4 : ∀ a b c d →
  (- a) + ((- b) + ((- c) + ((- d) + 0ℚ)))
  ≡ - (a + (b + (c + (d + 0ℚ))))
sumIndex4Neg4 a b c d =
  ℚRing.solve (a ∷ b ∷ c ∷ d ∷ [])

sumIndex4Scale5 : ∀ scalar a b c d →
  scalar * a + (scalar * b + (scalar * c + (scalar * d + 0ℚ)))
  ≡ scalar * (a + (b + (c + (d + 0ℚ))))
sumIndex4Scale5 scalar a b c d =
  ℚRing.solve (scalar ∷ a ∷ b ∷ c ∷ d ∷ [])

------------------------------------------------------------------------
-- Literal side-four cyclic shifts.
------------------------------------------------------------------------

Index4 : Set
Index4 = CyclicIndex four

Site4 : Set
Site4 = Product (Product Index4 Index4) (Product Index4 Index4)

axis0 axis1 axis2 axis3 : Axis4
axis0 = index0
axis1 = index1
axis2 = index2
axis3 = index3

next4 : Index4 → Index4
next4 zeroᵢ = sucᵢ zeroᵢ
next4 (sucᵢ zeroᵢ) = sucᵢ (sucᵢ zeroᵢ)
next4 (sucᵢ (sucᵢ zeroᵢ)) = sucᵢ (sucᵢ (sucᵢ zeroᵢ))
next4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = zeroᵢ

previous4 : Index4 → Index4
previous4 zeroᵢ = sucᵢ (sucᵢ (sucᵢ zeroᵢ))
previous4 (sucᵢ zeroᵢ) = zeroᵢ
previous4 (sucᵢ (sucᵢ zeroᵢ)) = sucᵢ zeroᵢ
previous4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = sucᵢ (sucᵢ zeroᵢ)

nextPrevious4 : ∀ index → next4 (previous4 index) ≡ index
nextPrevious4 zeroᵢ = refl
nextPrevious4 (sucᵢ zeroᵢ) = refl
nextPrevious4 (sucᵢ (sucᵢ zeroᵢ)) = refl
nextPrevious4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl

previousNext4 : ∀ index → previous4 (next4 index) ≡ index
previousNext4 zeroᵢ = refl
previousNext4 (sucᵢ zeroᵢ) = refl
previousNext4 (sucᵢ (sucᵢ zeroᵢ)) = refl
previousNext4 (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) = refl

shiftForward : Axis4 → Site4 → Site4
shiftForward zeroᵢ (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair (next4 x0) x1) (pair x2 x3)
shiftForward (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 (next4 x1)) (pair x2 x3)
shiftForward (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair (next4 x2) x3)
shiftForward (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair x2 (next4 x3))

shiftBackward : Axis4 → Site4 → Site4
shiftBackward zeroᵢ (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair (previous4 x0) x1) (pair x2 x3)
shiftBackward (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 (previous4 x1)) (pair x2 x3)
shiftBackward (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair (previous4 x2) x3)
shiftBackward (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair x2 (previous4 x3))

shiftBackwardForward : ∀ axis site →
  shiftBackward axis (shiftForward axis site) ≡ site
shiftBackwardForward zeroᵢ (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x0 = refl
shiftBackwardForward (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x1 = refl
shiftBackwardForward (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x2 = refl
shiftBackwardForward (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x3 = refl

shiftForwardBackward : ∀ axis site →
  shiftForward axis (shiftBackward axis site) ≡ site
shiftForwardBackward zeroᵢ (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x0 = refl
shiftForwardBackward (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x1 = refl
shiftForwardBackward (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x2 = refl
shiftForwardBackward (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x3 = refl

forwardShiftsCommute : ∀ left right site →
  shiftForward left (shiftForward right site)
  ≡ shiftForward right (shiftForward left site)
forwardShiftsCommute zeroᵢ zeroᵢ site = refl
forwardShiftsCommute zeroᵢ (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute (sucᵢ zeroᵢ) zeroᵢ (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute (sucᵢ zeroᵢ) (sucᵢ zeroᵢ) site = refl
forwardShiftsCommute (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute (sucᵢ zeroᵢ) (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ zeroᵢ)) site = refl
forwardShiftsCommute (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site = refl

backwardForwardShiftsCommute : ∀ left right site →
  shiftBackward left (shiftForward right site)
  ≡ shiftForward right (shiftBackward left site)
backwardForwardShiftsCommute zeroᵢ zeroᵢ site =
  trans (shiftBackwardForward axis0 site)
    (sym (shiftForwardBackward axis0 site))
backwardForwardShiftsCommute zeroᵢ (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute zeroᵢ (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute zeroᵢ (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute (sucᵢ zeroᵢ) zeroᵢ (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute (sucᵢ zeroᵢ) (sucᵢ zeroᵢ) site =
  trans (shiftBackwardForward axis1 site)
    (sym (shiftForwardBackward axis1 site))
backwardForwardShiftsCommute (sucᵢ zeroᵢ) (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute (sucᵢ zeroᵢ) (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute (sucᵢ (sucᵢ zeroᵢ)) zeroᵢ (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ zeroᵢ)) site =
  trans (shiftBackwardForward axis2 site)
    (sym (shiftForwardBackward axis2 site))
backwardForwardShiftsCommute (sucᵢ (sucᵢ zeroᵢ)) (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) zeroᵢ (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  trans (shiftBackwardForward axis3 site)
    (sym (shiftForwardBackward axis3 site))

------------------------------------------------------------------------
-- Explicit nested finite sums and reindexing.
------------------------------------------------------------------------

sumIndex4 : (Index4 → ℚ) → ℚ
sumIndex4 term =
  term index0 + (term index1 + (term index2 + (term index3 + 0ℚ)))

sumIndex4Cong : ∀ left right →
  (∀ index → left index ≡ right index) →
  sumIndex4 left ≡ sumIndex4 right
sumIndex4Cong left right pointwise
  rewrite pointwise index0 | pointwise index1
        | pointwise index2 | pointwise index3 = refl

sumIndex4Next : ∀ term →
  sumIndex4 (λ index → term (next4 index)) ≡ sumIndex4 term
sumIndex4Next term =
  sumIndex4Next4
    (term index0) (term index1) (term index2) (term index3)

sumIndex4Previous : ∀ term →
  sumIndex4 (λ index → term (previous4 index)) ≡ sumIndex4 term
sumIndex4Previous term =
  sumIndex4Previous4
    (term index0) (term index1) (term index2) (term index3)

sumIndex4Add : ∀ left right →
  sumIndex4 (λ index → left index + right index)
  ≡ sumIndex4 left + sumIndex4 right
sumIndex4Add left right =
  sumIndex4Add8
    (left index0) (left index1) (left index2) (left index3)
    (right index0) (right index1) (right index2) (right index3)

sumIndex4Neg : ∀ term →
  sumIndex4 (λ index → - term index) ≡ - sumIndex4 term
sumIndex4Neg term =
  sumIndex4Neg4 (term index0) (term index1) (term index2) (term index3)

sumIndex4Scale : ∀ scalar term →
  sumIndex4 (λ index → scalar * term index)
  ≡ scalar * sumIndex4 term
sumIndex4Scale scalar term =
  sumIndex4Scale5 scalar
    (term index0) (term index1) (term index2) (term index3)

sumSites : (Site4 → ℚ) → ℚ
sumSites term =
  sumIndex4 (λ x0 →
    sumIndex4 (λ x1 →
      sumIndex4 (λ x2 →
        sumIndex4 (λ x3 →
          term (pair (pair x0 x1) (pair x2 x3))))))

sumSitesCong : ∀ left right →
  (∀ site → left site ≡ right site) →
  sumSites left ≡ sumSites right
sumSitesCong left right pointwise =
  sumIndex4Cong _ _ (λ x0 →
    sumIndex4Cong _ _ (λ x1 →
      sumIndex4Cong _ _ (λ x2 →
        sumIndex4Cong _ _ (λ x3 →
          pointwise (pair (pair x0 x1) (pair x2 x3))))))

sumSitesForwardInvariant : ∀ term axis →
  sumSites (λ site → term (shiftForward axis site)) ≡ sumSites term
sumSitesForwardInvariant term zeroᵢ =
  sumIndex4Next
    (λ x0 → sumIndex4 (λ x1 → sumIndex4 (λ x2 → sumIndex4
      (λ x3 → term (pair (pair x0 x1) (pair x2 x3))))))
sumSitesForwardInvariant term (sucᵢ zeroᵢ) =
  sumIndex4Cong _ _ (λ x0 →
    sumIndex4Next
      (λ x1 → sumIndex4 (λ x2 → sumIndex4
        (λ x3 → term (pair (pair x0 x1) (pair x2 x3))))))
sumSitesForwardInvariant term (sucᵢ (sucᵢ zeroᵢ)) =
  sumIndex4Cong _ _ (λ x0 →
    sumIndex4Cong _ _ (λ x1 →
      sumIndex4Next
        (λ x2 → sumIndex4
          (λ x3 → term (pair (pair x0 x1) (pair x2 x3))))))
sumSitesForwardInvariant term (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) =
  sumIndex4Cong _ _ (λ x0 →
    sumIndex4Cong _ _ (λ x1 →
      sumIndex4Cong _ _ (λ x2 →
        sumIndex4Next
          (λ x3 → term (pair (pair x0 x1) (pair x2 x3))))))

sumSitesBackwardInvariant : ∀ term axis →
  sumSites (λ site → term (shiftBackward axis site)) ≡ sumSites term
sumSitesBackwardInvariant term axis =
  let
    forwardApplied =
      sumSitesForwardInvariant
        (λ site → term (shiftBackward axis site)) axis
    leftExact :
      sumSites
        (λ site → term (shiftBackward axis (shiftForward axis site)))
      ≡ sumSites term
    leftExact =
      sumSitesCong _ _ (λ site →
        cong term (shiftBackwardForward axis site))
  in
  trans
    (sym forwardApplied)
    leftExact

sumSitesAdd : ∀ left right →
  sumSites (λ site → left site + right site)
  ≡ sumSites left + sumSites right
sumSitesAdd left right =
  trans
    (sumIndex4Cong _ _ (λ x0 →
      trans
        (sumIndex4Cong _ _ (λ x1 →
          trans
            (sumIndex4Cong _ _ (λ x2 →
              sumIndex4Add
                (λ x3 → left (pair (pair x0 x1) (pair x2 x3)))
                (λ x3 → right (pair (pair x0 x1) (pair x2 x3)))))
            (sumIndex4Add
              (λ x2 → sumIndex4 (λ x3 →
                left (pair (pair x0 x1) (pair x2 x3))))
              (λ x2 → sumIndex4 (λ x3 →
                right (pair (pair x0 x1) (pair x2 x3)))))))
        (sumIndex4Add
          (λ x1 → sumIndex4 (λ x2 → sumIndex4 (λ x3 →
            left (pair (pair x0 x1) (pair x2 x3)))))
          (λ x1 → sumIndex4 (λ x2 → sumIndex4 (λ x3 →
            right (pair (pair x0 x1) (pair x2 x3))))))))
    (sumIndex4Add
      (λ x0 → sumIndex4 (λ x1 → sumIndex4 (λ x2 → sumIndex4
        (λ x3 → left (pair (pair x0 x1) (pair x2 x3))))))
      (λ x0 → sumIndex4 (λ x1 → sumIndex4 (λ x2 → sumIndex4
        (λ x3 → right (pair (pair x0 x1) (pair x2 x3)))))))

sumSitesNeg : ∀ term →
  sumSites (λ site → - term site) ≡ - sumSites term
sumSitesNeg term =
  trans
    (sumIndex4Cong _ _ (λ x0 →
      trans
        (sumIndex4Cong _ _ (λ x1 →
          trans
            (sumIndex4Cong _ _ (λ x2 →
              sumIndex4Neg
                (λ x3 → term (pair (pair x0 x1) (pair x2 x3)))))
            (sumIndex4Neg
              (λ x2 → sumIndex4 (λ x3 →
                term (pair (pair x0 x1) (pair x2 x3)))))))
        (sumIndex4Neg
          (λ x1 → sumIndex4 (λ x2 → sumIndex4 (λ x3 →
            term (pair (pair x0 x1) (pair x2 x3))))))))
    (sumIndex4Neg
      (λ x0 → sumIndex4 (λ x1 → sumIndex4 (λ x2 → sumIndex4
        (λ x3 → term (pair (pair x0 x1) (pair x2 x3)))))))

sumSitesScale : ∀ scalar term →
  sumSites (λ site → scalar * term site)
  ≡ scalar * sumSites term
sumSitesScale scalar term =
  trans
    (sumIndex4Cong _ _ (λ x0 →
      trans
        (sumIndex4Cong _ _ (λ x1 →
          trans
            (sumIndex4Cong _ _ (λ x2 →
              sumIndex4Scale scalar
                (λ x3 → term (pair (pair x0 x1) (pair x2 x3)))))
            (sumIndex4Scale scalar
              (λ x2 → sumIndex4 (λ x3 →
                term (pair (pair x0 x1) (pair x2 x3)))))))
        (sumIndex4Scale scalar
          (λ x1 → sumIndex4 (λ x2 → sumIndex4 (λ x3 →
            term (pair (pair x0 x1) (pair x2 x3))))))))
    (sumIndex4Scale scalar
      (λ x0 → sumIndex4 (λ x1 → sumIndex4 (λ x2 → sumIndex4
        (λ x3 → term (pair (pair x0 x1) (pair x2 x3)))))))

sumSitesSubtract : ∀ left right →
  sumSites (λ site → left site - right site)
  ≡ sumSites left - sumSites right
sumSitesSubtract left right =
  trans
    (sumSitesAdd left (λ site → - right site))
    (trans
      (cong (λ value → sumSites left + value) (sumSitesNeg right))
      (sumSitesSubtractNeg (sumSites left) (sumSites right)))

------------------------------------------------------------------------
-- Difference calculus and summation by parts.
------------------------------------------------------------------------

ScalarField : Set
ScalarField = Site4 → ℚ

BondField4 : Set
BondField4 = Axis4 → ScalarField

forwardDifference : Axis4 → ScalarField → ScalarField
forwardDifference axis fieldValue site =
  fieldValue (shiftForward axis site) - fieldValue site

backwardDifference : Axis4 → ScalarField → ScalarField
backwardDifference axis fieldValue site =
  fieldValue site - fieldValue (shiftBackward axis site)

fieldSubtract : ScalarField → ScalarField → ScalarField
fieldSubtract left right site = left site - right site

fieldInner : ScalarField → ScalarField → ℚ
fieldInner left right = sumSites (λ site → left site * right site)

fieldNormSq : ScalarField → ℚ
fieldNormSq fieldValue = fieldInner fieldValue fieldValue

fieldInnerSymmetric : ∀ left right →
  fieldInner left right ≡ fieldInner right left
fieldInnerSymmetric left right =
  sumSitesCong _ _ (λ site →
    multiplyCommutative (left site) (right site))

fieldInnerCongRight : ∀ left right replacement →
  (∀ site → right site ≡ replacement site) →
  fieldInner left right ≡ fieldInner left replacement
fieldInnerCongRight left right replacement pointwise =
  sumSitesCong _ _ (λ site →
    cong (λ value → left site * value) (pointwise site))

shiftedProductReindex : ∀ left right axis →
  sumSites
    (λ site → left (shiftForward axis site) * right site)
  ≡ sumSites
      (λ site → left site * right (shiftBackward axis site))
shiftedProductReindex left right axis =
  let
    term : Site4 → ℚ
    term site = left site * right (shiftBackward axis site)

    shiftedExact :
      sumSites (λ site → term (shiftForward axis site))
      ≡ sumSites
          (λ site → left (shiftForward axis site) * right site)
    shiftedExact =
      sumSitesCong _ _ (λ site →
        cong (λ value → left (shiftForward axis site) * value)
          (cong right (shiftBackwardForward axis site)))
  in
  trans
    (sym shiftedExact)
    (sumSitesForwardInvariant term axis)

summationByParts : ∀ axis fieldValue test →
  fieldInner (forwardDifference axis fieldValue) test
  ≡ - fieldInner fieldValue (backwardDifference axis test)
summationByParts axis fieldValue test =
  let
    expandedLeft :
      fieldInner (forwardDifference axis fieldValue) test
      ≡ sumSites
          (λ site → fieldValue (shiftForward axis site) * test site)
        - fieldInner fieldValue test
    expandedLeft =
      trans
        (sumSitesCong _ _ (λ site →
          forwardMinusTest
            (fieldValue (shiftForward axis site))
            (fieldValue site) (test site)))
        (sumSitesSubtract
          (λ site → fieldValue (shiftForward axis site) * test site)
          (λ site → fieldValue site * test site))

    reindexed = shiftedProductReindex fieldValue test axis
  in
  trans expandedLeft
    (trans
      (cong (_- fieldInner fieldValue test) reindexed)
      (trans
        (subtractIsNeg
          (sumSites
            (λ site → fieldValue site * test (shiftBackward axis site)))
          (fieldInner fieldValue test))
        (let
          inner' :
            fieldInner fieldValue (backwardDifference axis test)
            ≡ fieldInner fieldValue test
              - sumSites
                  (λ site → fieldValue site * test (shiftBackward axis site))
          inner' =
            trans
              (sym (sumSitesCong _ _ (λ site →
                backwardMinusTest
                  (fieldValue site) (test site)
                  (test (shiftBackward axis site)))))
              (sumSitesSubtract
                (λ site → fieldValue site * test site)
                (λ site →
                  fieldValue site * test (shiftBackward axis site)))
        in cong -_ (sym inner'))))

backwardForwardDifferenceCommute : ∀ backwardAxis forwardAxis fieldValue site →
  backwardDifference backwardAxis
    (forwardDifference forwardAxis fieldValue) site
  ≡ forwardDifference forwardAxis
      (backwardDifference backwardAxis fieldValue) site
backwardForwardDifferenceCommute backwardAxis forwardAxis fieldValue site
  rewrite backwardForwardShiftsCommute backwardAxis forwardAxis site =
  subtractSubtract
    (fieldValue (shiftForward forwardAxis site))
    (fieldValue site)
    (fieldValue (shiftForward forwardAxis (shiftBackward backwardAxis site)))
    (fieldValue (shiftBackward backwardAxis site))

forwardBackwardNormExact : ∀ axis fieldValue →
  fieldNormSq (forwardDifference axis fieldValue)
  ≡ fieldNormSq (backwardDifference axis fieldValue)
forwardBackwardNormExact axis fieldValue =
  let
    backwardAsShiftedForward : ∀ site →
      backwardDifference axis fieldValue site
      ≡ forwardDifference axis fieldValue (shiftBackward axis site)
    backwardAsShiftedForward site =
      cong (_- fieldValue (shiftBackward axis site))
        (cong fieldValue (sym (shiftForwardBackward axis site)))

    backwardNormAsShift :
      fieldNormSq (backwardDifference axis fieldValue)
      ≡ sumSites
          (λ site →
            forwardDifference axis fieldValue (shiftBackward axis site)
            * forwardDifference axis fieldValue (shiftBackward axis site))
    backwardNormAsShift =
      sumSitesCong _ _ (λ site →
        cong₂ _*_
          (backwardAsShiftedForward site)
          (backwardAsShiftedForward site))
  in
  trans
    (sym (sumSitesBackwardInvariant
      (λ site →
        forwardDifference axis fieldValue site
        * forwardDifference axis fieldValue site) axis))
    (sym backwardNormAsShift)

mixedCrossIdentity : ∀ leftAxis rightAxis fieldValue →
  fieldInner
    (forwardDifference leftAxis (fieldValue rightAxis))
    (forwardDifference rightAxis (fieldValue leftAxis))
  ≡ fieldInner
      (backwardDifference leftAxis (fieldValue leftAxis))
      (backwardDifference rightAxis (fieldValue rightAxis))
mixedCrossIdentity leftAxis rightAxis fieldValue =
  let
    B = backwardDifference leftAxis (fieldValue leftAxis)
    forwardB = forwardDifference rightAxis B

    first = summationByParts leftAxis
      (fieldValue rightAxis)
      (forwardDifference rightAxis (fieldValue leftAxis))

    commuteInside :
      fieldInner (fieldValue rightAxis)
        (backwardDifference leftAxis
          (forwardDifference rightAxis (fieldValue leftAxis)))
      ≡ fieldInner (fieldValue rightAxis) forwardB
    commuteInside =
      fieldInnerCongRight
        (fieldValue rightAxis)
        (backwardDifference leftAxis
          (forwardDifference rightAxis (fieldValue leftAxis)))
        forwardB
        (backwardForwardDifferenceCommute
          leftAxis rightAxis (fieldValue leftAxis))

    second = summationByParts rightAxis B (fieldValue rightAxis)
  in
  trans first
    (trans
      (cong -_ commuteInside)
      (trans
        (cong -_ (fieldInnerSymmetric (fieldValue rightAxis) forwardB))
        (trans
          (cong -_ second)
          refl)))

backwardNormIsForward : ∀ axis fieldValue →
  fieldNormSq (backwardDifference axis fieldValue)
  ≡ fieldNormSq (forwardDifference axis fieldValue)
backwardNormIsForward axis fieldValue = sym (forwardBackwardNormExact axis fieldValue)

backwardCrossIsForward : ∀ leftAxis rightAxis fieldValue →
  fieldInner
    (backwardDifference leftAxis (fieldValue leftAxis))
    (backwardDifference rightAxis (fieldValue rightAxis))
  ≡ fieldInner
    (forwardDifference leftAxis (fieldValue rightAxis))
    (forwardDifference rightAxis (fieldValue leftAxis))
backwardCrossIsForward leftAxis rightAxis fieldValue =
  sym (mixedCrossIdentity leftAxis rightAxis fieldValue)

------------------------------------------------------------------------
-- Energy expansions.
------------------------------------------------------------------------

normDifferenceExpansion : ∀ left right →
  fieldNormSq (fieldSubtract left right)
  ≡ fieldNormSq left + fieldNormSq right
    - (+ 2 / 1) * fieldInner left right
normDifferenceExpansion left right =
  trans
    (sumSitesCong _ _ (λ site →
      normDiffSiteHelper (left site) (right site)))
    (trans
      (sumSitesAdd
        (λ site → left site * left site + right site * right site)
        (λ site → - ((+ 2 / 1) * (left site * right site))))
      (trans
        (cong₂ _+_
          (sumSitesAdd
            (λ site → left site * left site)
            (λ site → right site * right site))
          (trans
            (sumSitesNeg
              (λ site → (+ 2 / 1) * (left site * right site)))
            (cong -_
              (sumSitesScale (+ 2 / 1)
                (λ site → left site * right site)))))
        refl))

fieldSum4 : ScalarField → ScalarField → ScalarField → ScalarField → ScalarField
fieldSum4 first second third fourth site =
  first site + (second site + (third site + fourth site))

normSum4Expansion : ∀ first second third fourth →
  fieldNormSq (fieldSum4 first second third fourth)
  ≡ fieldNormSq first + fieldNormSq second
    + fieldNormSq third + fieldNormSq fourth
    + (+ 2 / 1) * (fieldInner first second
      + fieldInner first third + fieldInner first fourth
      + fieldInner second third + fieldInner second fourth
      + fieldInner third fourth)
normSum4Expansion first second third fourth =
  let
    squares : ScalarField
    squares site =
      (first site * first site + second site * second site)
      + (third site * third site + fourth site * fourth site)

    crosses : ScalarField
    crosses site =
      first site * second site
      + (first site * third site
        + (first site * fourth site
          + (second site * third site
            + (second site * fourth site + third site * fourth site))))
  in
  trans
    (sumSitesCong _ _ (λ site →
      norm4SiteHelper
        (first site) (second site) (third site) (fourth site)))
    (trans
      (sumSitesAdd squares
        (λ site → (+ 2 / 1) * crosses site))
      (trans
        (cong₂ _+_ refl
          (sumSitesScale (+ 2 / 1) crosses))
        (let
          squareExpansion :
            sumSites squares
            ≡ fieldNormSq first + fieldNormSq second
              + fieldNormSq third + fieldNormSq fourth
          squareExpansion =
            trans
              (sumSitesAdd
                (λ site → first site * first site
                  + second site * second site)
                (λ site → third site * third site
                  + fourth site * fourth site))
              (trans
                (cong₂ _+_
                  (sumSitesAdd
                    (λ site → first site * first site)
                    (λ site → second site * second site))
                  (sumSitesAdd
                    (λ site → third site * third site)
                    (λ site → fourth site * fourth site)))
                (crossAssoc3
                  (fieldNormSq first + fieldNormSq second)
                  (fieldNormSq third) (fieldNormSq fourth)))

          crossExpansion :
            sumSites crosses
            ≡ fieldInner first second
              + fieldInner first third + fieldInner first fourth
              + fieldInner second third + fieldInner second fourth
              + fieldInner third fourth
          crossExpansion =
            trans
              (sumSitesAdd
                (λ site → first site * second site)
                (λ site →
                  first site * third site
                  + (first site * fourth site
                    + (second site * third site
                      + (second site * fourth site + third site * fourth site)))))
              (trans
                (cong (λ value → fieldInner first second + value)
                  (trans
                    (sumSitesAdd
                      (λ site → first site * third site)
                      (λ site →
                        first site * fourth site
                        + (second site * third site
                          + (second site * fourth site
                            + third site * fourth site))))
                    (trans
                      (cong (λ value → fieldInner first third + value)
                        (trans
                          (sumSitesAdd
                            (λ site → first site * fourth site)
                            (λ site →
                              second site * third site
                              + (second site * fourth site
                                + third site * fourth site)))
                          (trans
                            (cong (λ value → fieldInner first fourth + value)
                              (trans
                                (sumSitesAdd
                                  (λ site → second site * third site)
                                  (λ site →
                                    second site * fourth site
                                    + third site * fourth site))
                                (trans
                                  (cong (λ value → fieldInner second third + value)
                                    (sumSitesAdd
                                      (λ site → second site * fourth site)
                                      (λ site → third site * fourth site)))
                                  (crossAssoc3
                                    (fieldInner second third)
                                    (fieldInner second fourth)
                                    (fieldInner third fourth)))))
                            (crossAssoc4
                              (fieldInner first fourth)
                              (fieldInner second third)
                              (fieldInner second fourth)
                              (fieldInner third fourth)))))
                      (crossAssoc5
                        (fieldInner first third)
                        (fieldInner first fourth)
                        (fieldInner second third)
                        (fieldInner second fourth)
                        (fieldInner third fourth)))))
                (crossAssoc6
                  (fieldInner first second)
                  (fieldInner first third)
                  (fieldInner first fourth)
                  (fieldInner second third)
                  (fieldInner second fourth)
                  (fieldInner third fourth)))
         in
         trans
          (cong₂ _+_
            squareExpansion
            (cong (λ value → (+ 2 / 1) * value) crossExpansion))
          (norm4Combine
            (fieldNormSq first) (fieldNormSq second)
            (fieldNormSq third) (fieldNormSq fourth)
            (fieldInner first second) (fieldInner first third)
            (fieldInner first fourth) (fieldInner second third)
            (fieldInner second fourth) (fieldInner third fourth)))))

periodicGradientEnergy : BondField4 → ℚ
periodicGradientEnergy fieldValue =
  fieldNormSq (forwardDifference axis0 (fieldValue axis0))
  + fieldNormSq (forwardDifference axis1 (fieldValue axis0))
  + fieldNormSq (forwardDifference axis2 (fieldValue axis0))
  + fieldNormSq (forwardDifference axis3 (fieldValue axis0))
  + fieldNormSq (forwardDifference axis0 (fieldValue axis1))
  + fieldNormSq (forwardDifference axis1 (fieldValue axis1))
  + fieldNormSq (forwardDifference axis2 (fieldValue axis1))
  + fieldNormSq (forwardDifference axis3 (fieldValue axis1))
  + fieldNormSq (forwardDifference axis0 (fieldValue axis2))
  + fieldNormSq (forwardDifference axis1 (fieldValue axis2))
  + fieldNormSq (forwardDifference axis2 (fieldValue axis2))
  + fieldNormSq (forwardDifference axis3 (fieldValue axis2))
  + fieldNormSq (forwardDifference axis0 (fieldValue axis3))
  + fieldNormSq (forwardDifference axis1 (fieldValue axis3))
  + fieldNormSq (forwardDifference axis2 (fieldValue axis3))
  + fieldNormSq (forwardDifference axis3 (fieldValue axis3))

curlComponent : Axis4 → Axis4 → BondField4 → ScalarField
curlComponent left right fieldValue =
  fieldSubtract
    (forwardDifference left (fieldValue right))
    (forwardDifference right (fieldValue left))

periodicCurlEnergy : BondField4 → ℚ
periodicCurlEnergy fieldValue =
  fieldNormSq (curlComponent axis0 axis1 fieldValue)
  + fieldNormSq (curlComponent axis0 axis2 fieldValue)
  + fieldNormSq (curlComponent axis0 axis3 fieldValue)
  + fieldNormSq (curlComponent axis1 axis2 fieldValue)
  + fieldNormSq (curlComponent axis1 axis3 fieldValue)
  + fieldNormSq (curlComponent axis2 axis3 fieldValue)

periodicDivergence : BondField4 → ScalarField
periodicDivergence fieldValue =
  fieldSum4
    (backwardDifference axis0 (fieldValue axis0))
    (backwardDifference axis1 (fieldValue axis1))
    (backwardDifference axis2 (fieldValue axis2))
    (backwardDifference axis3 (fieldValue axis3))

periodicDivergenceEnergy : BondField4 → ℚ
periodicDivergenceEnergy fieldValue = fieldNormSq (periodicDivergence fieldValue)

periodicCurlExpansion : ∀ fieldValue →
  periodicCurlEnergy fieldValue
  ≡
    (fieldNormSq (forwardDifference axis0 (fieldValue axis1))
      + fieldNormSq (forwardDifference axis1 (fieldValue axis0))
      - (+ 2 / 1) * fieldInner
          (forwardDifference axis0 (fieldValue axis1))
          (forwardDifference axis1 (fieldValue axis0)))
    + (fieldNormSq (forwardDifference axis0 (fieldValue axis2))
      + fieldNormSq (forwardDifference axis2 (fieldValue axis0))
      - (+ 2 / 1) * fieldInner
          (forwardDifference axis0 (fieldValue axis2))
          (forwardDifference axis2 (fieldValue axis0)))
    + (fieldNormSq (forwardDifference axis0 (fieldValue axis3))
      + fieldNormSq (forwardDifference axis3 (fieldValue axis0))
      - (+ 2 / 1) * fieldInner
          (forwardDifference axis0 (fieldValue axis3))
          (forwardDifference axis3 (fieldValue axis0)))
    + (fieldNormSq (forwardDifference axis1 (fieldValue axis2))
      + fieldNormSq (forwardDifference axis2 (fieldValue axis1))
      - (+ 2 / 1) * fieldInner
          (forwardDifference axis1 (fieldValue axis2))
          (forwardDifference axis2 (fieldValue axis1)))
    + (fieldNormSq (forwardDifference axis1 (fieldValue axis3))
      + fieldNormSq (forwardDifference axis3 (fieldValue axis1))
      - (+ 2 / 1) * fieldInner
          (forwardDifference axis1 (fieldValue axis3))
          (forwardDifference axis3 (fieldValue axis1)))
    + (fieldNormSq (forwardDifference axis2 (fieldValue axis3))
      + fieldNormSq (forwardDifference axis3 (fieldValue axis2))
      - (+ 2 / 1) * fieldInner
          (forwardDifference axis2 (fieldValue axis3))
          (forwardDifference axis3 (fieldValue axis2)))
periodicCurlExpansion fieldValue
  rewrite normDifferenceExpansion
    (forwardDifference axis0 (fieldValue axis1))
    (forwardDifference axis1 (fieldValue axis0))
  | normDifferenceExpansion
    (forwardDifference axis0 (fieldValue axis2))
    (forwardDifference axis2 (fieldValue axis0))
  | normDifferenceExpansion
    (forwardDifference axis0 (fieldValue axis3))
    (forwardDifference axis3 (fieldValue axis0))
  | normDifferenceExpansion
    (forwardDifference axis1 (fieldValue axis2))
    (forwardDifference axis2 (fieldValue axis1))
  | normDifferenceExpansion
    (forwardDifference axis1 (fieldValue axis3))
    (forwardDifference axis3 (fieldValue axis1))
  | normDifferenceExpansion
    (forwardDifference axis2 (fieldValue axis3))
    (forwardDifference axis3 (fieldValue axis2)) = refl

periodicDivergenceExpansion : ∀ fieldValue →
  periodicDivergenceEnergy fieldValue
  ≡
    fieldNormSq (backwardDifference axis0 (fieldValue axis0))
    + fieldNormSq (backwardDifference axis1 (fieldValue axis1))
    + fieldNormSq (backwardDifference axis2 (fieldValue axis2))
    + fieldNormSq (backwardDifference axis3 (fieldValue axis3))
    + (+ 2 / 1) *
      (fieldInner
        (backwardDifference axis0 (fieldValue axis0))
        (backwardDifference axis1 (fieldValue axis1))
      + fieldInner
        (backwardDifference axis0 (fieldValue axis0))
        (backwardDifference axis2 (fieldValue axis2))
      + fieldInner
        (backwardDifference axis0 (fieldValue axis0))
        (backwardDifference axis3 (fieldValue axis3))
      + fieldInner
        (backwardDifference axis1 (fieldValue axis1))
        (backwardDifference axis2 (fieldValue axis2))
      + fieldInner
        (backwardDifference axis1 (fieldValue axis1))
        (backwardDifference axis3 (fieldValue axis3))
      + fieldInner
        (backwardDifference axis2 (fieldValue axis2))
        (backwardDifference axis3 (fieldValue axis3)))
periodicDivergenceExpansion fieldValue =
  normSum4Expansion
    (backwardDifference axis0 (fieldValue axis0))
    (backwardDifference axis1 (fieldValue axis1))
    (backwardDifference axis2 (fieldValue axis2))
    (backwardDifference axis3 (fieldValue axis3))

periodicScalarHodgeIdentity : ∀ fieldValue →
  periodicGradientEnergy fieldValue
  ≡ periodicCurlEnergy fieldValue + periodicDivergenceEnergy fieldValue
periodicScalarHodgeIdentity fieldValue
  rewrite periodicCurlExpansion fieldValue
        | periodicDivergenceExpansion fieldValue
        | backwardNormIsForward axis0 (fieldValue axis0)
        | backwardNormIsForward axis1 (fieldValue axis1)
        | backwardNormIsForward axis2 (fieldValue axis2)
        | backwardNormIsForward axis3 (fieldValue axis3)
        | backwardCrossIsForward axis0 axis1 fieldValue
        | backwardCrossIsForward axis0 axis2 fieldValue
        | backwardCrossIsForward axis0 axis3 fieldValue
        | backwardCrossIsForward axis1 axis2 fieldValue
        | backwardCrossIsForward axis1 axis3 fieldValue
        | backwardCrossIsForward axis2 axis3 fieldValue =
  hodgeFinal16
    (fieldNormSq (forwardDifference axis0 (fieldValue axis0)))
    (fieldNormSq (forwardDifference axis1 (fieldValue axis0)))
    (fieldNormSq (forwardDifference axis2 (fieldValue axis0)))
    (fieldNormSq (forwardDifference axis3 (fieldValue axis0)))
    (fieldNormSq (forwardDifference axis0 (fieldValue axis1)))
    (fieldNormSq (forwardDifference axis1 (fieldValue axis1)))
    (fieldNormSq (forwardDifference axis2 (fieldValue axis1)))
    (fieldNormSq (forwardDifference axis3 (fieldValue axis1)))
    (fieldNormSq (forwardDifference axis0 (fieldValue axis2)))
    (fieldNormSq (forwardDifference axis1 (fieldValue axis2)))
    (fieldNormSq (forwardDifference axis2 (fieldValue axis2)))
    (fieldNormSq (forwardDifference axis3 (fieldValue axis2)))
    (fieldNormSq (forwardDifference axis0 (fieldValue axis3)))
    (fieldNormSq (forwardDifference axis1 (fieldValue axis3)))
    (fieldNormSq (forwardDifference axis2 (fieldValue axis3)))
    (fieldNormSq (forwardDifference axis3 (fieldValue axis3)))
    (fieldInner
      (forwardDifference axis0 (fieldValue axis1))
      (forwardDifference axis1 (fieldValue axis0)))
    (fieldInner
      (forwardDifference axis0 (fieldValue axis2))
      (forwardDifference axis2 (fieldValue axis0)))
    (fieldInner
      (forwardDifference axis0 (fieldValue axis3))
      (forwardDifference axis3 (fieldValue axis0)))
    (fieldInner
      (forwardDifference axis1 (fieldValue axis2))
      (forwardDifference axis2 (fieldValue axis1)))
    (fieldInner
      (forwardDifference axis1 (fieldValue axis3))
      (forwardDifference axis3 (fieldValue axis1)))
    (fieldInner
      (forwardDifference axis2 (fieldValue axis3))
      (forwardDifference axis3 (fieldValue axis2)))

------------------------------------------------------------------------
-- Three-component physical SU(2) lift.
------------------------------------------------------------------------

data LieCoordinate3 : Set where
  coordinateX : LieCoordinate3
  coordinateY : LieCoordinate3
  coordinateZ : LieCoordinate3

PhysicalBondField4 : Set
PhysicalBondField4 = LieCoordinate3 → BondField4

physicalPeriodicGradientEnergy : PhysicalBondField4 → ℚ
physicalPeriodicGradientEnergy fieldValue =
  periodicGradientEnergy (fieldValue coordinateX)
  + periodicGradientEnergy (fieldValue coordinateY)
  + periodicGradientEnergy (fieldValue coordinateZ)

physicalPeriodicCurlEnergy : PhysicalBondField4 → ℚ
physicalPeriodicCurlEnergy fieldValue =
  periodicCurlEnergy (fieldValue coordinateX)
  + periodicCurlEnergy (fieldValue coordinateY)
  + periodicCurlEnergy (fieldValue coordinateZ)

physicalPeriodicDivergenceEnergy : PhysicalBondField4 → ℚ
physicalPeriodicDivergenceEnergy fieldValue =
  periodicDivergenceEnergy (fieldValue coordinateX)
  + periodicDivergenceEnergy (fieldValue coordinateY)
  + periodicDivergenceEnergy (fieldValue coordinateZ)

physicalPeriodicHodgeIdentity : ∀ fieldValue →
  physicalPeriodicGradientEnergy fieldValue
  ≡ physicalPeriodicCurlEnergy fieldValue
    + physicalPeriodicDivergenceEnergy fieldValue
physicalPeriodicHodgeIdentity fieldValue
  rewrite periodicScalarHodgeIdentity (fieldValue coordinateX)
        | periodicScalarHodgeIdentity (fieldValue coordinateY)
        | periodicScalarHodgeIdentity (fieldValue coordinateZ) =
  physicalCombine
    (periodicCurlEnergy (fieldValue coordinateX))
    (periodicCurlEnergy (fieldValue coordinateY))
    (periodicCurlEnergy (fieldValue coordinateZ))
    (periodicDivergenceEnergy (fieldValue coordinateX))
    (periodicDivergenceEnergy (fieldValue coordinateY))
    (periodicDivergenceEnergy (fieldValue coordinateZ))

sideFourCyclicReindexLevel : ProofLevel
sideFourCyclicReindexLevel = machineChecked

periodicSummationByPartsLevel : ProofLevel
periodicSummationByPartsLevel = machineChecked

periodicMixedCrossIdentityLevel : ProofLevel
periodicMixedCrossIdentityLevel = machineChecked

periodicScalarHodgeIdentityLevel : ProofLevel
periodicScalarHodgeIdentityLevel = machineChecked

physicalPeriodicHodgeIdentityLevel : ProofLevel
physicalPeriodicHodgeIdentityLevel = machineChecked
