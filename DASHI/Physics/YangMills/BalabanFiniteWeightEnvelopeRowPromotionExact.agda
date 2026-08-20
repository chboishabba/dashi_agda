module DASHI.Physics.YangMills.BalabanFiniteWeightEnvelopeRowPromotionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrodinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- A finite bounded weight does not require a new spectral theorem merely to
-- promote an already-small absolute row kernel.  If
--
--   1 <= w(y) <= W,
--   sum_y |R(x,y)| <= q,
--
-- then
--
--   sum_y |R(x,y)| w(y)
--     <= W q
--     <= (W q) w(x).
--
-- This deliberately coarse promotion loses the geometry of w, but if W q<1
-- it is enough to establish a strict weighted Neumann contraction.  Sharper
-- Combes--Thomas decay remains available if later constants require it.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_; ∣_∣; NonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedRowSumContractionExact as Row
import DASHI.Physics.YangMills.BalabanReducedGhostNeumannRowContractionExact as Neumann

sumKernelMatchesRational :
  ∀ {Index : Set} (indices : List Index) value →
  Row.sumKernel indices value ≡ Sums.sumRational indices value
sumKernelMatchesRational [] value = refl
sumKernelMatchesRational (index ∷ indices) value
  rewrite sumKernelMatchesRational indices value = refl

weightedRowEnvelope :
  ∀ {Index : Set}
    (indices : List Index)
    (kernel : Index → Index → ℚ)
    (weight : Index → ℚ)
    W →
  0ℚ ≤ W →
  (∀ index → 0ℚ ≤ weight index) →
  (∀ index → weight index ≤ W) →
  ∀ left →
  Row.weightedRowSum indices kernel weight left
  ≤ W * Neumann.rowMass indices kernel left
weightedRowEnvelope indices kernel weight W WNonnegative weightNN weightBelow left =
  let
    pointwise : ∀ right →
      ∣ kernel left right ∣ * weight right
      ≤ ∣ kernel left right ∣ * W
    pointwise right =
      let
        instance
          entryNN : NonNegative ∣ kernel left right ∣
          entryNN = ℚP.∣-∣-nonNeg (kernel left right)
      in
      ℚP.*-monoˡ-≤-nonNeg ∣ kernel left right ∣ (weightBelow right)

    summed :
      Sums.sumRational indices
        (λ right → ∣ kernel left right ∣ * weight right)
      ≤ Sums.sumRational indices
        (λ right → ∣ kernel left right ∣ * W)
    summed = Schur.sumPointwiseBelow indices _ _ pointwise

    factored :
      Sums.sumRational indices
        (λ right → ∣ kernel left right ∣ * W)
      ≡ W * Neumann.rowMass indices kernel left
    factored =
      trans
        (Sums.sumRationalCong indices _ _
          (λ right → ℚP.*-comm ∣ kernel left right ∣ W))
        (Sums.sumRationalScale W indices
          (λ right → ∣ kernel left right ∣))
  in
  subst
    (λ lower → lower ≤ W * Neumann.rowMass indices kernel left)
    (sym (sumKernelMatchesRational indices
      (λ right → ∣ kernel left right ∣ * weight right)))
    (subst
      (λ upper →
        Sums.sumRational indices
          (λ right → ∣ kernel left right ∣ * weight right) ≤ upper)
      factored summed)

boundedWeightPromotesUniformRow :
  ∀ {Index : Set}
    (indices : List Index)
    (kernel : Index → Index → ℚ)
    (weight : Index → ℚ)
    W q →
  0ℚ ≤ W → 0ℚ ≤ q →
  (∀ index → 1ℚ ≤ weight index) →
  (∀ index → weight index ≤ W) →
  Neumann.UniformRowBound indices kernel q →
  ∀ left →
  Row.weightedRowSum indices kernel weight left
  ≤ (W * q) * weight left
boundedWeightPromotesUniformRow
    indices kernel weight W q WNN qNN weightAboveOne weightBelow rows left =
  let
    weightNN : ∀ index → 0ℚ ≤ weight index
    weightNN index = ℚP.≤-trans ℚP.0≤1 (weightAboveOne index)

    first = weightedRowEnvelope
      indices kernel weight W WNN weightNN weightBelow left

    scaledRow :
      W * Neumann.rowMass indices kernel left ≤ W * q
    scaledRow = Norm.scaleNonnegative W WNN (rows left)

    factorNN : 0ℚ ≤ W * q
    factorNN =
      let
        instance
          WNonnegative : NonNegative W
          WNonnegative = ℚ.nonNegative WNN
          qNonnegative : NonNegative q
          qNonnegative = ℚ.nonNegative qNN
      in ℚP.nonNegative⁻¹ (W * q)

    toWeight : W * q ≤ (W * q) * weight left
    toWeight =
      subst
        (λ lower → lower ≤ (W * q) * weight left)
        (ℚP.*-identityʳ (W * q))
        (Norm.scaleNonnegative (W * q) factorNN (weightAboveOne left))
  in
  ℚP.≤-trans first (ℚP.≤-trans scaledRow toWeight)

finiteWeightEnvelopeRowPromotionLevel : ProofLevel
finiteWeightEnvelopeRowPromotionLevel = machineChecked
