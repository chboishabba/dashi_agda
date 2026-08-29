{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteInfluenceNonnegativePowersExact where

------------------------------------------------------------------------
-- ROW C FORWARD PRODUCER: NONNEGATIVE INFLUENCE MATRIX -> NONNEGATIVE POWERS
--
-- `BalabanFiniteInfluenceRowMassPowerExact` deliberately left positivity of
-- matrix powers as a separate carrier input.  For the finite rational influence
-- matrices used by the YM finite-speed lane this is not physical analysis: it
-- follows by induction from nonnegative entries and finite sums of nonnegative
-- products.
--
-- Closing this seam means the physical spatial-influence producer only has to
-- build ONE nonnegative finite majorant with a cutoff-uniform row-mass bound.
-- All positivity of Dyson/matrix powers is then theorem-owned.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums

mulNN : ∀ {left right : ℚ} → 0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
mulNN {left} {right} leftNN rightNN =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = ℚ.nonNegative leftNN
      rightNonnegative : NonNegative right
      rightNonnegative = ℚ.nonNegative rightNN
  in
  ℚP.nonNegative⁻¹ (left * right)

sumRationalNonnegative :
  ∀ {A : Set} (values : List A) (term : A → ℚ) →
  (∀ value → 0ℚ ≤ term value) →
  0ℚ ≤ Sums.sumRational values term
sumRationalNonnegative [] term termNN = ℚP.≤-refl
sumRationalNonnegative (value ∷ values) term termNN =
  ℚP.+-mono-≤
    (termNN value)
    (sumRationalNonnegative values term termNN)

matrixComposeNonnegative :
  ∀ {Site : Set}
    (dataSet : Power.NonnegativeFiniteInfluenceMajorant Site)
    (left right : Power.Matrix Site) →
  (∀ x y → 0ℚ ≤ left x y) →
  (∀ x y → 0ℚ ≤ right x y) →
  ∀ x y →
  0ℚ ≤ Power.matrixCompose dataSet left right x y
matrixComposeNonnegative dataSet left right leftNN rightNN x y =
  sumRationalNonnegative
    (Power.sites dataSet)
    (λ middle → left x middle * right middle y)
    (λ middle → mulNN (leftNN x middle) (rightNN middle y))

powerEntriesNonnegative :
  ∀ {Site : Set}
    (dataSet : Power.NonnegativeFiniteInfluenceMajorant Site) →
  ∀ n x y →
  0ℚ ≤ Power.majorantPowerPositive dataSet n x y
powerEntriesNonnegative dataSet zero x y =
  Power.majorantNonnegative dataSet x y
powerEntriesNonnegative dataSet (suc n) x y =
  matrixComposeNonnegative
    dataSet
    (Power.majorantPowerPositive dataSet n)
    (Power.majorant dataSet)
    (powerEntriesNonnegative dataSet n)
    (Power.majorantNonnegative dataSet)
    x y

asNonnegativeInfluencePowers :
  ∀ {Site : Set} →
  (dataSet : Power.NonnegativeFiniteInfluenceMajorant Site) →
  Power.NonnegativeInfluencePowers dataSet
asNonnegativeInfluencePowers dataSet = record
  { Power.NonnegativeInfluencePowers.powerEntriesNonnegative =
      powerEntriesNonnegative dataSet
  }

positivePowerRowMassBoundFromMajorant :
  ∀ {Site : Set}
    (dataSet : Power.NonnegativeFiniteInfluenceMajorant Site) →
  ∀ n x →
  Sums.sumRational
    (Power.sites dataSet)
    (Power.majorantPowerPositive dataSet n x)
  ≤ Power.rationalPower (Power.rowMass dataSet) (suc n)
positivePowerRowMassBoundFromMajorant dataSet =
  Power.positivePowerRowMassBound (asNonnegativeInfluencePowers dataSet)

finiteInfluencePowerPositivityLevel : ProofLevel
finiteInfluencePowerPositivityLevel = machineChecked

finiteInfluencePowerRowMassFromSingleMajorantLevel : ProofLevel
finiteInfluencePowerRowMassFromSingleMajorantLevel = machineChecked

-- Physical YM seam after this reduction: construct the literal absolute
-- derivative-generator majorant and its volume/cutoff-uniform one-row mass
-- bound.  Positivity of every higher Dyson power is no longer a separate input.
physicalYMFiniteInfluenceMajorantAndRowMassLevel : ProofLevel
physicalYMFiniteInfluenceMajorantAndRowMassLevel = conditional
