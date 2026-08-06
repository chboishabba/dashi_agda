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
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; -_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier public using
  (CyclicIndex; Axis4; Product; pair; four)
open import DASHI.Physics.YangMills.BalabanPath4PhysicalFibreMatchExact using
  (index0; index1; index2; index3)
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical

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
next4 index0 = index1
next4 index1 = index2
next4 index2 = index3
next4 index3 = index0

previous4 : Index4 → Index4
previous4 index0 = index3
previous4 index1 = index0
previous4 index2 = index1
previous4 index3 = index2

nextPrevious4 : ∀ index → next4 (previous4 index) ≡ index
nextPrevious4 index0 = refl
nextPrevious4 index1 = refl
nextPrevious4 index2 = refl
nextPrevious4 index3 = refl

previousNext4 : ∀ index → previous4 (next4 index) ≡ index
previousNext4 index0 = refl
previousNext4 index1 = refl
previousNext4 index2 = refl
previousNext4 index3 = refl

shiftForward : Axis4 → Site4 → Site4
shiftForward axis0 (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair (next4 x0) x1) (pair x2 x3)
shiftForward axis1 (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 (next4 x1)) (pair x2 x3)
shiftForward axis2 (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair (next4 x2) x3)
shiftForward axis3 (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair x2 (next4 x3))

shiftBackward : Axis4 → Site4 → Site4
shiftBackward axis0 (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair (previous4 x0) x1) (pair x2 x3)
shiftBackward axis1 (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 (previous4 x1)) (pair x2 x3)
shiftBackward axis2 (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair (previous4 x2) x3)
shiftBackward axis3 (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair x2 (previous4 x3))

shiftBackwardForward : ∀ axis site →
  shiftBackward axis (shiftForward axis site) ≡ site
shiftBackwardForward axis0 (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x0 = refl
shiftBackwardForward axis1 (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x1 = refl
shiftBackwardForward axis2 (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x2 = refl
shiftBackwardForward axis3 (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x3 = refl

shiftForwardBackward : ∀ axis site →
  shiftForward axis (shiftBackward axis site) ≡ site
shiftForwardBackward axis0 (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x0 = refl
shiftForwardBackward axis1 (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x1 = refl
shiftForwardBackward axis2 (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x2 = refl
shiftForwardBackward axis3 (pair (pair x0 x1) (pair x2 x3))
  rewrite nextPrevious4 x3 = refl

forwardShiftsCommute : ∀ left right site →
  shiftForward left (shiftForward right site)
  ≡ shiftForward right (shiftForward left site)
forwardShiftsCommute axis0 axis0 site = refl
forwardShiftsCommute axis0 axis1 (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute axis0 axis2 (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute axis0 axis3 (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute axis1 axis0 (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute axis1 axis1 site = refl
forwardShiftsCommute axis1 axis2 (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute axis1 axis3 (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute axis2 axis0 (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute axis2 axis1 (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute axis2 axis2 site = refl
forwardShiftsCommute axis2 axis3 (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute axis3 axis0 (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute axis3 axis1 (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute axis3 axis2 (pair (pair x0 x1) (pair x2 x3)) = refl
forwardShiftsCommute axis3 axis3 site = refl

backwardForwardShiftsCommute : ∀ left right site →
  shiftBackward left (shiftForward right site)
  ≡ shiftForward right (shiftBackward left site)
backwardForwardShiftsCommute axis0 axis0 site =
  trans (shiftBackwardForward axis0 site)
    (sym (shiftForwardBackward axis0 site))
backwardForwardShiftsCommute axis0 axis1 (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute axis0 axis2 (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute axis0 axis3 (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute axis1 axis0 (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute axis1 axis1 site =
  trans (shiftBackwardForward axis1 site)
    (sym (shiftForwardBackward axis1 site))
backwardForwardShiftsCommute axis1 axis2 (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute axis1 axis3 (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute axis2 axis0 (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute axis2 axis1 (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute axis2 axis2 site =
  trans (shiftBackwardForward axis2 site)
    (sym (shiftForwardBackward axis2 site))
backwardForwardShiftsCommute axis2 axis3 (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute axis3 axis0 (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute axis3 axis1 (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute axis3 axis2 (pair (pair x0 x1) (pair x2 x3)) = refl
backwardForwardShiftsCommute axis3 axis3 site =
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
  ℚRing.solve-∀
    (term index0) (term index1) (term index2) (term index3)

sumIndex4Previous : ∀ term →
  sumIndex4 (λ index → term (previous4 index)) ≡ sumIndex4 term
sumIndex4Previous term =
  ℚRing.solve-∀
    (term index0) (term index1) (term index2) (term index3)

sumIndex4Add : ∀ left right →
  sumIndex4 (λ index → left index + right index)
  ≡ sumIndex4 left + sumIndex4 right
sumIndex4Add left right =
  ℚRing.solve-∀
    (left index0) (left index1) (left index2) (left index3)
    (right index0) (right index1) (right index2) (right index3)

sumIndex4Neg : ∀ term →
  sumIndex4 (λ index → - term index) ≡ - sumIndex4 term
sumIndex4Neg term =
  ℚRing.solve-∀
    (term index0) (term index1) (term index2) (term index3)

sumIndex4Scale : ∀ scalar term →
  sumIndex4 (λ index → scalar * term index)
  ≡ scalar * sumIndex4 term
sumIndex4Scale scalar term =
  ℚRing.solve-∀ scalar
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
sumSitesForwardInvariant term axis0 =
  sumIndex4Next
    (λ x0 → sumIndex4 (λ x1 → sumIndex4 (λ x2 → sumIndex4
      (λ x3 → term (pair (pair x0 x1) (pair x2 x3))))))
sumSitesForwardInvariant term axis1 =
  sumIndex4Cong _ _ (λ x0 →
    sumIndex4Next
      (λ x1 → sumIndex4 (λ x2 → sumIndex4
        (λ x3 → term (pair (pair x0 x1) (pair x2 x3))))))
sumSitesForwardInvariant term axis2 =
  sumIndex4Cong _ _ (λ x0 →
    sumIndex4Cong _ _ (λ x1 →
      sumIndex4Next
        (λ x2 → sumIndex4
          (λ x3 → term (pair (pair x0 x1) (pair x2 x3))))))
sumSitesForwardInvariant term axis3 =
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
      (cong (sumSites left +_) (sumSitesNeg right))
      (ℚRing.solve-∀ (sumSites left) (sumSites right)))

------------------------------------------------------------------------
-- Difference calculus and summation by parts.
------------------------------------------------------------------------

ScalarField : Set
ScalarField = Site4 → ℚ

BondField4 : Set
BondField4 = Axis4 → ScalarField

forwardDifference : Axis4 → ScalarField → ScalarField
forwardDifference axis field site =
  field (shiftForward axis site) - field site

backwardDifference : Axis4 → ScalarField → ScalarField
backwardDifference axis field site =
  field site - field (shiftBackward axis site)

fieldSubtract : ScalarField → ScalarField → ScalarField
fieldSubtract left right site = left site - right site

fieldInner : ScalarField → ScalarField → ℚ
fieldInner left right = sumSites (λ site → left site * right site)

fieldNormSq : ScalarField → ℚ
fieldNormSq field = fieldInner field field

fieldInnerSymmetric : ∀ left right →
  fieldInner left right ≡ fieldInner right left
fieldInnerSymmetric left right =
  sumSitesCong _ _ (λ site →
    ℚRing.solve-∀ (left site) (right site))

fieldInnerCongRight : ∀ left right replacement →
  (∀ site → right site ≡ replacement site) →
  fieldInner left right ≡ fieldInner left replacement
fieldInnerCongRight left right replacement pointwise =
  sumSitesCong _ _ (λ site →
    cong (left site *_) (pointwise site))

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
        cong (left (shiftForward axis site) *_)
          (cong right (shiftBackwardForward axis site)))
  in
  trans
    (sym shiftedExact)
    (sumSitesForwardInvariant term axis)

summationByParts : ∀ axis field test →
  fieldInner (forwardDifference axis field) test
  ≡ - fieldInner field (backwardDifference axis test)
summationByParts axis field test =
  let
    expandedLeft :
      fieldInner (forwardDifference axis field) test
      ≡ sumSites
          (λ site → field (shiftForward axis site) * test site)
        - fieldInner field test
    expandedLeft =
      trans
        (sumSitesCong _ _ (λ site →
          ℚRing.solve-∀
            (field (shiftForward axis site))
            (field site) (test site)))
        (sumSitesSubtract
          (λ site → field (shiftForward axis site) * test site)
          (λ site → field site * test site))

    reindexed = shiftedProductReindex field test axis
  in
  trans expandedLeft
    (trans
      (cong (_- fieldInner field test) reindexed)
      (trans
        (ℚRing.solve-∀
          (fieldInner field test)
          (sumSites
            (λ site → field site * test (shiftBackward axis site))))
        (sym
          (trans
            (cong -_
              (trans
                (sumSitesCong _ _ (λ site →
                  ℚRing.solve-∀
                    (field site) (test site)
                    (test (shiftBackward axis site))))
                (sumSitesSubtract
                  (λ site → field site * test site)
                  (λ site →
                    field site * test (shiftBackward axis site)))))
            (ℚRing.solve-∀
              (fieldInner field test)
              (sumSites
                (λ site →
                  field site * test (shiftBackward axis site))))))))

backwardForwardDifferenceCommute : ∀ backwardAxis forwardAxis field site →
  backwardDifference backwardAxis
    (forwardDifference forwardAxis field) site
  ≡ forwardDifference forwardAxis
      (backwardDifference backwardAxis field) site
backwardForwardDifferenceCommute backwardAxis forwardAxis field site =
  subst
    (λ mixedSite →
      (field (shiftForward forwardAxis site) - field mixedSite)
      - (field site - field (shiftBackward backwardAxis site))
      ≡
      (field (shiftForward forwardAxis site)
        - field (shiftBackward backwardAxis
            (shiftForward forwardAxis site)))
      - (field site - field (shiftBackward backwardAxis site)))
    (sym (backwardForwardShiftsCommute
      backwardAxis forwardAxis site))
    (ℚRing.solve-∀
      (field (shiftForward forwardAxis site))
      (field (shiftBackward backwardAxis
        (shiftForward forwardAxis site)))
      (field site)
      (field (shiftBackward backwardAxis site)))

forwardBackwardNormExact : ∀ axis field →
  fieldNormSq (forwardDifference axis field)
  ≡ fieldNormSq (backwardDifference axis field)
forwardBackwardNormExact axis field =
  let
    backwardAsShiftedForward : ∀ site →
      backwardDifference axis field site
      ≡ forwardDifference axis field (shiftBackward axis site)
    backwardAsShiftedForward site =
      cong (_- field (shiftBackward axis site))
        (cong field (shiftForwardBackward axis site))

    backwardNormAsShift :
      fieldNormSq (backwardDifference axis field)
      ≡ sumSites
          (λ site →
            forwardDifference axis field (shiftBackward axis site)
            * forwardDifference axis field (shiftBackward axis site))
    backwardNormAsShift =
      sumSitesCong _ _ (λ site →
        cong₂ _*_
          (backwardAsShiftedForward site)
          (backwardAsShiftedForward site))
  in
  trans
    (sym (sumSitesBackwardInvariant
      (λ site →
        forwardDifference axis field site
        * forwardDifference axis field site) axis))
    (sym backwardNormAsShift)

mixedCrossIdentity : ∀ leftAxis rightAxis field →
  fieldInner
    (forwardDifference leftAxis (field rightAxis))
    (forwardDifference rightAxis (field leftAxis))
  ≡ fieldInner
      (backwardDifference leftAxis (field leftAxis))
      (backwardDifference rightAxis (field rightAxis))
mixedCrossIdentity leftAxis rightAxis field =
  let
    B = backwardDifference leftAxis (field leftAxis)
    forwardB = forwardDifference rightAxis B

    first = summationByParts leftAxis
      (field rightAxis)
      (forwardDifference rightAxis (field leftAxis))

    commuteInside :
      fieldInner (field rightAxis)
        (backwardDifference leftAxis
          (forwardDifference rightAxis (field leftAxis)))
      ≡ fieldInner (field rightAxis) forwardB
    commuteInside =
      fieldInnerCongRight
        (field rightAxis)
        (backwardDifference leftAxis
          (forwardDifference rightAxis (field leftAxis)))
        forwardB
        (backwardForwardDifferenceCommute
          leftAxis rightAxis (field leftAxis))

    second = summationByParts rightAxis B (field rightAxis)
  in
  trans first
    (trans
      (cong -_ commuteInside)
      (trans
        (cong -_ (fieldInnerSymmetric (field rightAxis) forwardB))
        (trans
          (cong -_ second)
          (ℚRing.solve-∀
            (fieldInner B
              (backwardDifference rightAxis (field rightAxis)))))))

backwardNormIsForward : ∀ axis field →
  fieldNormSq (backwardDifference axis field)
  ≡ fieldNormSq (forwardDifference axis field)
backwardNormIsForward axis field = sym (forwardBackwardNormExact axis field)

backwardCrossIsForward : ∀ leftAxis rightAxis field →
  fieldInner
    (backwardDifference leftAxis (field leftAxis))
    (backwardDifference rightAxis (field rightAxis))
  ≡ fieldInner
    (forwardDifference leftAxis (field rightAxis))
    (forwardDifference rightAxis (field leftAxis))
backwardCrossIsForward leftAxis rightAxis field =
  sym (mixedCrossIdentity leftAxis rightAxis field)

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
      ℚRing.solve-∀ (left site) (right site)))
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
        (ℚRing.solve-∀
          (fieldNormSq left) (fieldNormSq right)
          (fieldInner left right))))

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
      first site * first site
      + second site * second site
      + third site * third site
      + fourth site * fourth site

    crosses : ScalarField
    crosses site =
      first site * second site
      + first site * third site + first site * fourth site
      + second site * third site + second site * fourth site
      + third site * fourth site
  in
  trans
    (sumSitesCong _ _ (λ site →
      ℚRing.solve-∀
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
                (λ site → first site * first site)
                (λ site →
                  second site * second site
                  + third site * third site
                  + fourth site * fourth site))
              (trans
                (cong
                  (fieldNormSq first +_)
                  (trans
                    (sumSitesAdd
                      (λ site → second site * second site)
                      (λ site →
                        third site * third site
                        + fourth site * fourth site))
                    (cong (fieldNormSq second +_)
                      (sumSitesAdd
                        (λ site → third site * third site)
                        (λ site → fourth site * fourth site)))))
                (ℚRing.solve-∀
                  (fieldNormSq first) (fieldNormSq second)
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
                  first site * third site + first site * fourth site
                  + second site * third site + second site * fourth site
                  + third site * fourth site))
              (trans
                (cong (fieldInner first second +_)
                  (trans
                    (sumSitesAdd
                      (λ site → first site * third site)
                      (λ site →
                        first site * fourth site
                        + second site * third site
                        + second site * fourth site
                        + third site * fourth site))
                    (trans
                      (cong (fieldInner first third +_)
                        (trans
                          (sumSitesAdd
                            (λ site → first site * fourth site)
                            (λ site →
                              second site * third site
                              + second site * fourth site
                              + third site * fourth site))
                          (trans
                            (cong (fieldInner first fourth +_)
                              (trans
                                (sumSitesAdd
                                  (λ site → second site * third site)
                                  (λ site →
                                    second site * fourth site
                                    + third site * fourth site))
                                (trans
                                  (cong (fieldInner second third +_)
                                    (sumSitesAdd
                                      (λ site → second site * fourth site)
                                      (λ site → third site * fourth site)))
                                  (ℚRing.solve-∀
                                    (fieldInner second third)
                                    (fieldInner second fourth)
                                    (fieldInner third fourth)))))
                            (ℚRing.solve-∀
                              (fieldInner first fourth)
                              (fieldInner second third)
                              (fieldInner second fourth)
                              (fieldInner third fourth)))))
                      (ℚRing.solve-∀
                        (fieldInner first third)
                        (fieldInner first fourth)
                        (fieldInner second third)
                        (fieldInner second fourth)
                        (fieldInner third fourth)))))
                (ℚRing.solve-∀
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
            (cong ((+ 2 / 1) *_) crossExpansion))
          (ℚRing.solve-∀
            (fieldNormSq first) (fieldNormSq second)
            (fieldNormSq third) (fieldNormSq fourth)
            (fieldInner first second) (fieldInner first third)
            (fieldInner first fourth) (fieldInner second third)
            (fieldInner second fourth) (fieldInner third fourth)))))

periodicGradientEnergy : BondField4 → ℚ
periodicGradientEnergy field =
  fieldNormSq (forwardDifference axis0 (field axis0))
  + fieldNormSq (forwardDifference axis1 (field axis0))
  + fieldNormSq (forwardDifference axis2 (field axis0))
  + fieldNormSq (forwardDifference axis3 (field axis0))
  + fieldNormSq (forwardDifference axis0 (field axis1))
  + fieldNormSq (forwardDifference axis1 (field axis1))
  + fieldNormSq (forwardDifference axis2 (field axis1))
  + fieldNormSq (forwardDifference axis3 (field axis1))
  + fieldNormSq (forwardDifference axis0 (field axis2))
  + fieldNormSq (forwardDifference axis1 (field axis2))
  + fieldNormSq (forwardDifference axis2 (field axis2))
  + fieldNormSq (forwardDifference axis3 (field axis2))
  + fieldNormSq (forwardDifference axis0 (field axis3))
  + fieldNormSq (forwardDifference axis1 (field axis3))
  + fieldNormSq (forwardDifference axis2 (field axis3))
  + fieldNormSq (forwardDifference axis3 (field axis3))

curlComponent : Axis4 → Axis4 → BondField4 → ScalarField
curlComponent left right field =
  fieldSubtract
    (forwardDifference left (field right))
    (forwardDifference right (field left))

periodicCurlEnergy : BondField4 → ℚ
periodicCurlEnergy field =
  fieldNormSq (curlComponent axis0 axis1 field)
  + fieldNormSq (curlComponent axis0 axis2 field)
  + fieldNormSq (curlComponent axis0 axis3 field)
  + fieldNormSq (curlComponent axis1 axis2 field)
  + fieldNormSq (curlComponent axis1 axis3 field)
  + fieldNormSq (curlComponent axis2 axis3 field)

periodicDivergence : BondField4 → ScalarField
periodicDivergence field =
  fieldSum4
    (backwardDifference axis0 (field axis0))
    (backwardDifference axis1 (field axis1))
    (backwardDifference axis2 (field axis2))
    (backwardDifference axis3 (field axis3))

periodicDivergenceEnergy : BondField4 → ℚ
periodicDivergenceEnergy field = fieldNormSq (periodicDivergence field)

periodicCurlExpansion : ∀ field →
  periodicCurlEnergy field
  ≡
    (fieldNormSq (forwardDifference axis0 (field axis1))
      + fieldNormSq (forwardDifference axis1 (field axis0))
      - (+ 2 / 1) * fieldInner
          (forwardDifference axis0 (field axis1))
          (forwardDifference axis1 (field axis0)))
    + (fieldNormSq (forwardDifference axis0 (field axis2))
      + fieldNormSq (forwardDifference axis2 (field axis0))
      - (+ 2 / 1) * fieldInner
          (forwardDifference axis0 (field axis2))
          (forwardDifference axis2 (field axis0)))
    + (fieldNormSq (forwardDifference axis0 (field axis3))
      + fieldNormSq (forwardDifference axis3 (field axis0))
      - (+ 2 / 1) * fieldInner
          (forwardDifference axis0 (field axis3))
          (forwardDifference axis3 (field axis0)))
    + (fieldNormSq (forwardDifference axis1 (field axis2))
      + fieldNormSq (forwardDifference axis2 (field axis1))
      - (+ 2 / 1) * fieldInner
          (forwardDifference axis1 (field axis2))
          (forwardDifference axis2 (field axis1)))
    + (fieldNormSq (forwardDifference axis1 (field axis3))
      + fieldNormSq (forwardDifference axis3 (field axis1))
      - (+ 2 / 1) * fieldInner
          (forwardDifference axis1 (field axis3))
          (forwardDifference axis3 (field axis1)))
    + (fieldNormSq (forwardDifference axis2 (field axis3))
      + fieldNormSq (forwardDifference axis3 (field axis2))
      - (+ 2 / 1) * fieldInner
          (forwardDifference axis2 (field axis3))
          (forwardDifference axis3 (field axis2)))
periodicCurlExpansion field
  rewrite normDifferenceExpansion
    (forwardDifference axis0 (field axis1))
    (forwardDifference axis1 (field axis0))
  | normDifferenceExpansion
    (forwardDifference axis0 (field axis2))
    (forwardDifference axis2 (field axis0))
  | normDifferenceExpansion
    (forwardDifference axis0 (field axis3))
    (forwardDifference axis3 (field axis0))
  | normDifferenceExpansion
    (forwardDifference axis1 (field axis2))
    (forwardDifference axis2 (field axis1))
  | normDifferenceExpansion
    (forwardDifference axis1 (field axis3))
    (forwardDifference axis3 (field axis1))
  | normDifferenceExpansion
    (forwardDifference axis2 (field axis3))
    (forwardDifference axis3 (field axis2)) = refl

periodicDivergenceExpansion : ∀ field →
  periodicDivergenceEnergy field
  ≡
    fieldNormSq (backwardDifference axis0 (field axis0))
    + fieldNormSq (backwardDifference axis1 (field axis1))
    + fieldNormSq (backwardDifference axis2 (field axis2))
    + fieldNormSq (backwardDifference axis3 (field axis3))
    + (+ 2 / 1) *
      (fieldInner
        (backwardDifference axis0 (field axis0))
        (backwardDifference axis1 (field axis1))
      + fieldInner
        (backwardDifference axis0 (field axis0))
        (backwardDifference axis2 (field axis2))
      + fieldInner
        (backwardDifference axis0 (field axis0))
        (backwardDifference axis3 (field axis3))
      + fieldInner
        (backwardDifference axis1 (field axis1))
        (backwardDifference axis2 (field axis2))
      + fieldInner
        (backwardDifference axis1 (field axis1))
        (backwardDifference axis3 (field axis3))
      + fieldInner
        (backwardDifference axis2 (field axis2))
        (backwardDifference axis3 (field axis3)))
periodicDivergenceExpansion field =
  normSum4Expansion
    (backwardDifference axis0 (field axis0))
    (backwardDifference axis1 (field axis1))
    (backwardDifference axis2 (field axis2))
    (backwardDifference axis3 (field axis3))

periodicScalarHodgeIdentity : ∀ field →
  periodicGradientEnergy field
  ≡ periodicCurlEnergy field + periodicDivergenceEnergy field
periodicScalarHodgeIdentity field
  rewrite periodicCurlExpansion field
        | periodicDivergenceExpansion field
        | backwardNormIsForward axis0 (field axis0)
        | backwardNormIsForward axis1 (field axis1)
        | backwardNormIsForward axis2 (field axis2)
        | backwardNormIsForward axis3 (field axis3)
        | backwardCrossIsForward axis0 axis1 field
        | backwardCrossIsForward axis0 axis2 field
        | backwardCrossIsForward axis0 axis3 field
        | backwardCrossIsForward axis1 axis2 field
        | backwardCrossIsForward axis1 axis3 field
        | backwardCrossIsForward axis2 axis3 field =
  ℚRing.solve-∀
    (fieldNormSq (forwardDifference axis0 (field axis0)))
    (fieldNormSq (forwardDifference axis1 (field axis0)))
    (fieldNormSq (forwardDifference axis2 (field axis0)))
    (fieldNormSq (forwardDifference axis3 (field axis0)))
    (fieldNormSq (forwardDifference axis0 (field axis1)))
    (fieldNormSq (forwardDifference axis1 (field axis1)))
    (fieldNormSq (forwardDifference axis2 (field axis1)))
    (fieldNormSq (forwardDifference axis3 (field axis1)))
    (fieldNormSq (forwardDifference axis0 (field axis2)))
    (fieldNormSq (forwardDifference axis1 (field axis2)))
    (fieldNormSq (forwardDifference axis2 (field axis2)))
    (fieldNormSq (forwardDifference axis3 (field axis2)))
    (fieldNormSq (forwardDifference axis0 (field axis3)))
    (fieldNormSq (forwardDifference axis1 (field axis3)))
    (fieldNormSq (forwardDifference axis2 (field axis3)))
    (fieldNormSq (forwardDifference axis3 (field axis3)))
    (fieldInner
      (forwardDifference axis0 (field axis1))
      (forwardDifference axis1 (field axis0)))
    (fieldInner
      (forwardDifference axis0 (field axis2))
      (forwardDifference axis2 (field axis0)))
    (fieldInner
      (forwardDifference axis0 (field axis3))
      (forwardDifference axis3 (field axis0)))
    (fieldInner
      (forwardDifference axis1 (field axis2))
      (forwardDifference axis2 (field axis1)))
    (fieldInner
      (forwardDifference axis1 (field axis3))
      (forwardDifference axis3 (field axis1)))
    (fieldInner
      (forwardDifference axis2 (field axis3))
      (forwardDifference axis3 (field axis2)))

------------------------------------------------------------------------
-- Three-component physical SU(2) lift.
------------------------------------------------------------------------

PhysicalBondField4 : Set
PhysicalBondField4 = Physical.LieCoordinate3 → BondField4

physicalPeriodicGradientEnergy : PhysicalBondField4 → ℚ
physicalPeriodicGradientEnergy field =
  periodicGradientEnergy (field Physical.coordinateX)
  + periodicGradientEnergy (field Physical.coordinateY)
  + periodicGradientEnergy (field Physical.coordinateZ)

physicalPeriodicCurlEnergy : PhysicalBondField4 → ℚ
physicalPeriodicCurlEnergy field =
  periodicCurlEnergy (field Physical.coordinateX)
  + periodicCurlEnergy (field Physical.coordinateY)
  + periodicCurlEnergy (field Physical.coordinateZ)

physicalPeriodicDivergenceEnergy : PhysicalBondField4 → ℚ
physicalPeriodicDivergenceEnergy field =
  periodicDivergenceEnergy (field Physical.coordinateX)
  + periodicDivergenceEnergy (field Physical.coordinateY)
  + periodicDivergenceEnergy (field Physical.coordinateZ)

physicalPeriodicHodgeIdentity : ∀ field →
  physicalPeriodicGradientEnergy field
  ≡ physicalPeriodicCurlEnergy field
    + physicalPeriodicDivergenceEnergy field
physicalPeriodicHodgeIdentity field
  rewrite periodicScalarHodgeIdentity (field Physical.coordinateX)
        | periodicScalarHodgeIdentity (field Physical.coordinateY)
        | periodicScalarHodgeIdentity (field Physical.coordinateZ) =
  ℚRing.solve-∀
    (periodicCurlEnergy (field Physical.coordinateX))
    (periodicCurlEnergy (field Physical.coordinateY))
    (periodicCurlEnergy (field Physical.coordinateZ))
    (periodicDivergenceEnergy (field Physical.coordinateX))
    (periodicDivergenceEnergy (field Physical.coordinateY))
    (periodicDivergenceEnergy (field Physical.coordinateZ))

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
