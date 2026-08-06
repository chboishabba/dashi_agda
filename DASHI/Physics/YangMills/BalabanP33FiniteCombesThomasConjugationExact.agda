module DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasConjugationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- This module proves the exact finite algebra at the heart of the
-- Combes--Thomas argument.  For a finite kernel K and a nowhere-zero diagonal
-- weight D, define
--
--   K_D = D K D^{-1}.
--
-- The module proves, by literal finite-list induction over the matrix product,
--
--   (A B)_D = A_D B_D,
--
-- so a right inverse G of K is transported to the right inverse G_D of K_D.
-- It also proves:
--
--   * finite-range support is unchanged by the conjugation;
--   * the tilt defect K_D-K vanishes wherever K vanishes;
--   * the original Green entry is recovered exactly from the tilted entry;
--   * a uniform tilted-entry bound yields the geometric off-diagonal bound
--       |G(root,target)| <= M D(target)
--     when D(root)=1 and D is nonnegative.
--
-- No spectral gap or tilt-smallness premise is manufactured here.  Those are
-- the two physical inputs to the next module.  What is removed is the need for
-- a custom collar/partition-of-unity identity merely to obtain exponential
-- kernel extraction once the tilted resolvent is controlled.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal finite matrices and products.
------------------------------------------------------------------------

Matrix : Set → Set
Matrix Site = Site → Site → ℚ

sumRational : ∀ {Site : Set} → List Site → (Site → ℚ) → ℚ
sumRational [] value = 0ℚ
sumRational (site ∷ sites) value =
  value site + sumRational sites value

sumRationalCong :
  ∀ {Site : Set} (sites : List Site)
    (left right : Site → ℚ) →
  (∀ site → left site ≡ right site) →
  sumRational sites left ≡ sumRational sites right
sumRationalCong [] left right pointwise = refl
sumRationalCong (site ∷ sites) left right pointwise
  rewrite pointwise site
  | sumRationalCong sites left right pointwise = refl

composeMatrix :
  ∀ {Site : Set} →
  List Site → Matrix Site → Matrix Site → Matrix Site
composeMatrix sites left right row column =
  sumRational sites
    (λ middle → left row middle * right middle column)

------------------------------------------------------------------------
-- Diagonal conjugation.
------------------------------------------------------------------------

diagonalConjugate :
  ∀ {Site : Set} →
  (weight inverseWeight : Site → ℚ) →
  Matrix Site → Matrix Site
diagonalConjugate weight inverseWeight kernel left right =
  weight left * (kernel left right * inverseWeight right)

diagonalTiltDefect :
  ∀ {Site : Set} →
  (weight inverseWeight : Site → ℚ) →
  Matrix Site → Matrix Site
diagonalTiltDefect weight inverseWeight kernel left right =
  diagonalConjugate weight inverseWeight kernel left right
  - kernel left right

conjugatedProductTerm :
  ∀ {Site : Set}
    (weight inverseWeight : Site → ℚ)
    (left right : Matrix Site)
    (row middle column : Site) →
  inverseWeight middle * weight middle ≡ 1ℚ →
  diagonalConjugate weight inverseWeight left row middle
    * diagonalConjugate weight inverseWeight right middle column
  ≡ weight row
      * ((left row middle * right middle column)
        * inverseWeight column)
conjugatedProductTerm
    weight inverseWeight left right row middle column inverseLaw =
  let
    rearrange :
      diagonalConjugate weight inverseWeight left row middle
        * diagonalConjugate weight inverseWeight right middle column
      ≡ weight row
          * ((left row middle
              * (inverseWeight middle * weight middle)
              * right middle column)
            * inverseWeight column)
    rearrange = ℚRing.solve []

    collapse :
      weight row
        * ((left row middle
            * (inverseWeight middle * weight middle)
            * right middle column)
          * inverseWeight column)
      ≡ weight row
          * ((left row middle * right middle column)
            * inverseWeight column)
    collapse =
      subst
        (λ selected →
          weight row
            * ((left row middle * selected * right middle column)
              * inverseWeight column)
          ≡ weight row
              * ((left row middle * right middle column)
                * inverseWeight column))
        (sym inverseLaw)
        (ℚRing.solve [])
  in
  trans rearrange collapse

conjugateCommutesWithComposition :
  ∀ {Site : Set}
    (sites : List Site)
    (weight inverseWeight : Site → ℚ)
    (inverseLaw : ∀ site → inverseWeight site * weight site ≡ 1ℚ)
    (left right : Matrix Site)
    (row column : Site) →
  composeMatrix sites
    (diagonalConjugate weight inverseWeight left)
    (diagonalConjugate weight inverseWeight right)
    row column
  ≡ diagonalConjugate weight inverseWeight
      (composeMatrix sites left right)
      row column
conjugateCommutesWithComposition
    [] weight inverseWeight inverseLaw left right row column =
  ℚRing.solve []
conjugateCommutesWithComposition
    (middle ∷ middles)
    weight inverseWeight inverseLaw left right row column
  rewrite conjugatedProductTerm
    weight inverseWeight left right row middle column
    (inverseLaw middle)
  | conjugateCommutesWithComposition
      middles weight inverseWeight inverseLaw left right row column =
  ℚRing.solve []

------------------------------------------------------------------------
-- Inverse transport under the Combes--Thomas tilt.
------------------------------------------------------------------------

RightInverse :
  ∀ {Site : Set} →
  List Site → Matrix Site → Matrix Site → Matrix Site → Set
RightInverse sites identity operator inverse =
  ∀ row column →
  composeMatrix sites operator inverse row column
  ≡ identity row column

conjugatedRightInverse :
  ∀ {Site : Set}
    (sites : List Site)
    (identity operator inverse : Matrix Site)
    (weight inverseWeight : Site → ℚ)
    (inverseLaw : ∀ site → inverseWeight site * weight site ≡ 1ℚ) →
  RightInverse sites identity operator inverse →
  RightInverse sites
    (diagonalConjugate weight inverseWeight identity)
    (diagonalConjugate weight inverseWeight operator)
    (diagonalConjugate weight inverseWeight inverse)
conjugatedRightInverse
    sites identity operator inverse weight inverseWeight inverseLaw
    rightInverse row column =
  trans
    (conjugateCommutesWithComposition
      sites weight inverseWeight inverseLaw
      operator inverse row column)
    (cong
      (λ selected → weight row * (selected * inverseWeight column))
      (rightInverse row column))

conjugatedRightInverseWithStableIdentity :
  ∀ {Site : Set}
    (sites : List Site)
    (identity operator inverse : Matrix Site)
    (weight inverseWeight : Site → ℚ)
    (inverseLaw : ∀ site → inverseWeight site * weight site ≡ 1ℚ) →
  RightInverse sites identity operator inverse →
  (∀ row column →
    diagonalConjugate weight inverseWeight identity row column
    ≡ identity row column) →
  RightInverse sites identity
    (diagonalConjugate weight inverseWeight operator)
    (diagonalConjugate weight inverseWeight inverse)
conjugatedRightInverseWithStableIdentity
    sites identity operator inverse weight inverseWeight inverseLaw
    rightInverse identityStable row column =
  trans
    (conjugatedRightInverse
      sites identity operator inverse
      weight inverseWeight inverseLaw
      rightInverse row column)
    (identityStable row column)

------------------------------------------------------------------------
-- Locality is preserved exactly.
------------------------------------------------------------------------

conjugationPreservesZeroEntry :
  ∀ {Site : Set}
    (weight inverseWeight : Site → ℚ)
    (kernel : Matrix Site)
    (left right : Site) →
  kernel left right ≡ 0ℚ →
  diagonalConjugate weight inverseWeight kernel left right ≡ 0ℚ
conjugationPreservesZeroEntry
    weight inverseWeight kernel left right zeroEntry
  rewrite zeroEntry = ℚRing.solve []

tiltDefectVanishesOutsideOriginalSupport :
  ∀ {Site : Set}
    (weight inverseWeight : Site → ℚ)
    (kernel : Matrix Site)
    (left right : Site) →
  kernel left right ≡ 0ℚ →
  diagonalTiltDefect weight inverseWeight kernel left right ≡ 0ℚ
tiltDefectVanishesOutsideOriginalSupport
    weight inverseWeight kernel left right zeroEntry
  rewrite zeroEntry = ℚRing.solve []

------------------------------------------------------------------------
-- Untwisting and kernel-decay extraction.
------------------------------------------------------------------------

untwistConjugatedEntry :
  ∀ {Site : Set}
    (weight inverseWeight : Site → ℚ)
    (inverseLaw : ∀ site → inverseWeight site * weight site ≡ 1ℚ)
    (kernel : Matrix Site)
    (left right : Site) →
  inverseWeight left
    * (diagonalConjugate weight inverseWeight kernel left right
      * weight right)
  ≡ kernel left right
untwistConjugatedEntry
    weight inverseWeight inverseLaw kernel left right =
  let
    rearrange :
      inverseWeight left
        * (diagonalConjugate weight inverseWeight kernel left right
          * weight right)
      ≡ (inverseWeight left * weight left)
          * (kernel left right
            * (inverseWeight right * weight right))
    rearrange = ℚRing.solve []

    collapseRight :
      kernel left right * (inverseWeight right * weight right)
      ≡ kernel left right
    collapseRight =
      subst
        (λ selected → kernel left right * selected ≡ kernel left right)
        (sym (inverseLaw right))
        (ℚRing.solve [])

    afterRight :
      (inverseWeight left * weight left)
        * (kernel left right
          * (inverseWeight right * weight right))
      ≡ (inverseWeight left * weight left) * kernel left right
    afterRight =
      cong
        ((inverseWeight left * weight left) *_)
        collapseRight

    collapseLeft :
      (inverseWeight left * weight left) * kernel left right
      ≡ kernel left right
    collapseLeft =
      subst
        (λ selected → selected * kernel left right ≡ kernel left right)
        (sym (inverseLaw left))
        (ℚRing.solve [])
  in
  trans rearrange (trans afterRight collapseLeft)

rootUntwistConjugatedEntry :
  ∀ {Site : Set}
    (weight inverseWeight : Site → ℚ)
    (inverseLaw : ∀ site → inverseWeight site * weight site ≡ 1ℚ)
    (kernel : Matrix Site)
    (root target : Site) →
  inverseWeight root ≡ 1ℚ →
  diagonalConjugate weight inverseWeight kernel root target
    * weight target
  ≡ kernel root target
rootUntwistConjugatedEntry
    weight inverseWeight inverseLaw kernel root target rootInverseOne =
  let
    withOne :
      1ℚ
        * (diagonalConjugate weight inverseWeight kernel root target
          * weight target)
      ≡ kernel root target
    withOne =
      subst
        (λ selected →
          selected
            * (diagonalConjugate weight inverseWeight kernel root target
              * weight target)
          ≡ kernel root target)
        rootInverseOne
        (untwistConjugatedEntry
          weight inverseWeight inverseLaw kernel root target)
  in
  trans
    (ℚRing.solve-∀
      (diagonalConjugate weight inverseWeight kernel root target)
      (weight target))
    withOne

rootEntryAbsoluteUntwist :
  ∀ {Site : Set}
    (weight inverseWeight : Site → ℚ)
    (inverseLaw : ∀ site → inverseWeight site * weight site ≡ 1ℚ)
    (kernel : Matrix Site)
    (root target : Site) →
  inverseWeight root ≡ 1ℚ →
  ∣ weight target ∣ ≡ weight target →
  ∣ kernel root target ∣
  ≡ ∣ diagonalConjugate weight inverseWeight kernel root target ∣
      * weight target
rootEntryAbsoluteUntwist
    weight inverseWeight inverseLaw kernel root target
    rootInverseOne weightAbsolute =
  trans
    (cong ∣_∣
      (sym
        (rootUntwistConjugatedEntry
          weight inverseWeight inverseLaw kernel root target
          rootInverseOne)))
    (trans
      (ℚP.∣p*q∣≡∣p∣*∣q∣
        (diagonalConjugate weight inverseWeight kernel root target)
        (weight target))
      (cong
        (∣ diagonalConjugate weight inverseWeight kernel root target ∣ *_)
        weightAbsolute))

combesThomasKernelDecayFromTiltedEntry :
  ∀ {Site : Set}
    (weight inverseWeight : Site → ℚ)
    (inverseLaw : ∀ site → inverseWeight site * weight site ≡ 1ℚ)
    (green : Matrix Site)
    (root target : Site)
    (majorant : ℚ) →
  inverseWeight root ≡ 1ℚ →
  0ℚ ≤ weight target →
  ∣ weight target ∣ ≡ weight target →
  ∣ diagonalConjugate weight inverseWeight green root target ∣
    ≤ majorant →
  ∣ green root target ∣ ≤ majorant * weight target
combesThomasKernelDecayFromTiltedEntry
    weight inverseWeight inverseLaw green root target majorant
    rootInverseOne weightNonnegative weightAbsolute tiltedBound =
  let
    instance
      weightNN : NonNegative (weight target)
      weightNN = ℚ.nonNegative weightNonnegative

    scaled :
      ∣ diagonalConjugate weight inverseWeight green root target ∣
        * weight target
      ≤ majorant * weight target
    scaled = ℚP.*-monoʳ-≤-nonNeg (weight target) tiltedBound
  in
  subst
    (λ lower → lower ≤ majorant * weight target)
    (sym
      (rootEntryAbsoluteUntwist
        weight inverseWeight inverseLaw green root target
        rootInverseOne weightAbsolute))
    scaled

finiteCombesThomasConjugationLevel : ProofLevel
finiteCombesThomasConjugationLevel = machineChecked

finiteCombesThomasInverseTransportLevel : ProofLevel
finiteCombesThomasInverseTransportLevel = machineChecked

finiteCombesThomasKernelExtractionLevel : ProofLevel
finiteCombesThomasKernelExtractionLevel = machineChecked
