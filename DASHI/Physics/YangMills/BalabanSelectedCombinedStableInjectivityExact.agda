module DASHI.Physics.YangMills.BalabanSelectedCombinedStableInjectivityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Roger A. Horn; Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Turn the explicit selected-background floor
--
--   (29/1024) ||lambda||^2 <= ||L_A^* lambda||^2
--
-- on the background-stable 12 + 765 multiplier sector into a genuine kernel
-- statement.  If the literal 780-row transpose vanishes on such a multiplier,
-- then its multiplier norm is zero.  This is the exact finite injectivity fact
-- needed before constructing an inverse on a chosen reduced coordinate basis.
-- It is intentionally weaker than a claim that the raw 780-row rank is
-- background independent; the holonomy guard proves that stronger shortcut is
-- not available near the reducible identity background.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanSelectedCombinedStableMultiplierFloorExact as Stable

stableMultiplierNormSqNonnegative :
  ∀ selected → 0ℚ ≤ Stable.stableCombinedMultiplierNormSq selected
stableMultiplierNormSqNonnegative selected =
  ℚP.+-mono-≤
    (Stable.averageMultiplierNormSqNonnegative (Stable.average selected))
    (Stable.gaugeMultiplierNormSqNonnegative (Stable.gauge selected))

selectedCombinedStableFloorPositive :
  0ℚ < Stable.selectedCombinedStableFloor
selectedCombinedStableFloorPositive = toWitness _

selectedCombinedStableFloorNonnegative :
  0ℚ ≤ Stable.selectedCombinedStableFloor
selectedCombinedStableFloorNonnegative =
  ℚP.<⇒≤ selectedCombinedStableFloorPositive

selectedCombinedStableFloorReciprocal : ℚ
selectedCombinedStableFloorReciprocal = + 1024 / 29

selectedCombinedStableFloorReciprocalNonnegative :
  0ℚ ≤ selectedCombinedStableFloorReciprocal
selectedCombinedStableFloorReciprocalNonnegative = toWitness _

selectedCombinedStableFloorReciprocalExact :
  selectedCombinedStableFloorReciprocal
    * Stable.selectedCombinedStableFloor
  ≡ 1ℚ
selectedCombinedStableFloorReciprocalExact = ℚRing.solve []

record LiteralCombinedAdjointKernel
    (background : Stable.Physical.RationalSU2Background4)
    (selected : Stable.StableCombinedMultiplier) : Set where
  field
    pointwiseZero : ∀ coordinate →
      Stable.literalCombinedAdjoint background selected coordinate ≡ 0ℚ
open LiteralCombinedAdjointKernel public

literalCombinedAdjointKernelNormZero :
  ∀ background selected →
  LiteralCombinedAdjointKernel background selected →
  KKT.stateNormSq (Stable.literalCombinedAdjoint background selected) ≡ 0ℚ
literalCombinedAdjointKernelNormZero background selected kernel =
  KKT.stateNormPointwiseCong (pointwiseZero kernel)

selectedCombinedStableAdjointKernelNormZero :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ selected →
  LiteralCombinedAdjointKernel background selected →
  Stable.stableCombinedMultiplierNormSq selected ≡ 0ℚ
selectedCombinedStableAdjointKernelNormZero background radius selected kernel =
  let
    floorBound =
      Stable.selectedBackgroundCombinedStableMultiplierFloor
        background radius selected

    adjointNormZero =
      literalCombinedAdjointKernelNormZero background selected kernel

    floorTimesNormBelowZero :
      Stable.selectedCombinedStableFloor
        * Stable.stableCombinedMultiplierNormSq selected
      ≤ 0ℚ
    floorTimesNormBelowZero =
      subst
        (λ upper →
          Stable.selectedCombinedStableFloor
            * Stable.stableCombinedMultiplierNormSq selected
          ≤ upper)
        adjointNormZero
        floorBound

    scaled :
      selectedCombinedStableFloorReciprocal
        * (Stable.selectedCombinedStableFloor
          * Stable.stableCombinedMultiplierNormSq selected)
      ≤ selectedCombinedStableFloorReciprocal * 0ℚ
    scaled =
      Norm.scaleNonnegative
        selectedCombinedStableFloorReciprocal
        selectedCombinedStableFloorReciprocalNonnegative
        floorTimesNormBelowZero

    normBelowZero :
      Stable.stableCombinedMultiplierNormSq selected ≤ 0ℚ
    normBelowZero =
      subst
        (λ lower → lower ≤ 0ℚ)
        (ℚRing.solve-∀
          selectedCombinedStableFloorReciprocal
          Stable.selectedCombinedStableFloor
          (Stable.stableCombinedMultiplierNormSq selected))
        (subst
          (λ upper →
            selectedCombinedStableFloorReciprocal
              * (Stable.selectedCombinedStableFloor
                * Stable.stableCombinedMultiplierNormSq selected)
            ≤ upper)
          (ℚRing.solve-∀ selectedCombinedStableFloorReciprocal)
          scaled)
  in
  ℚP.≤-antisym normBelowZero
    (stableMultiplierNormSqNonnegative selected)

selectedCombinedStableInjectivityLevel : ProofLevel
selectedCombinedStableInjectivityLevel = machineChecked
