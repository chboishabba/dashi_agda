module DASHI.Physics.Closure.NSTriadKNHHDirectionalSuperlevelProfileRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Zoran Grujic.
-- Title: "A Geometric Measure-Type Regularity Criterion for Solutions to the
-- 3D Navier-Stokes Equations".
-- DOI: 10.1088/0951-7715/26/1/289.
-- arXiv DOI: 10.48550/arXiv.1111.0217.
--
-- Classical result: Cavalieri/layer-cake representation by superlevel sets.
-- DOI: not applicable to the classical identity.
--
-- DASHI CONTRIBUTION
--
-- Round 41 proved a finite layer-cake identity but left monotonicity of the
-- threshold profile as supplied data.  Here monotonicity is derived from the
-- literal nested-superlevel condition instead.
--
-- For a fixed physical energy cell and two thresholds s1 <= s2, the only
-- structural fact needed is
--
--   Theta > s2  ==>  Theta > s1.
--
-- Encoding the two superlevel decisions as Bools gives an exact finite theorem
--
--   E 1_{Theta>s2} <= E 1_{Theta>s1}.
--
-- Summing over cells proves the monotone bad-mass profile
--
--   M(s2) <= M(s1).
--
-- This is the threshold-distribution view suggested by the Round-41 layer-cake
-- result: good/bad classification is a late cut through one underlying defect
-- distribution, not two unrelated dynamical quantities.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

record NestedSuperlevelEnergyCell : Set where
  field
    energy : ℚ
    energyNonnegative : 0ℚ ≤ energy
    lowerActive upperActive : Bool
    nestedSuperlevel : upperActive ≡ true → lowerActive ≡ true

open NestedSuperlevelEnergyCell public

activeEnergy : ℚ → Bool → ℚ
activeEnergy energy true = energy
activeEnergy energy false = 0ℚ

upperActiveEnergyBelowLower :
  (cell : NestedSuperlevelEnergyCell) →
  activeEnergy (energy cell) (upperActive cell)
  ≤ activeEnergy (energy cell) (lowerActive cell)
upperActiveEnergyBelowLower cell with upperActive cell | lowerActive cell
... | false | false = ℚP.≤-refl
... | false | true = energyNonnegative cell
... | true | true = ℚP.≤-refl
... | true | false =
  ⊥-elim (falseNotTrue (nestedSuperlevel cell refl))
  where
  falseNotTrue : false ≡ true → ⊥
  falseNotTrue ()

lowerBadMass upperBadMass : List NestedSuperlevelEnergyCell → ℚ
lowerBadMass [] = 0ℚ
lowerBadMass (cell ∷ rest) =
  activeEnergy (energy cell) (lowerActive cell) + lowerBadMass rest

upperBadMass [] = 0ℚ
upperBadMass (cell ∷ rest) =
  activeEnergy (energy cell) (upperActive cell) + upperBadMass rest

superlevelBadMassMonotone :
  (cells : List NestedSuperlevelEnergyCell) →
  upperBadMass cells ≤ lowerBadMass cells
superlevelBadMassMonotone [] = ℚP.≤-refl
superlevelBadMassMonotone (cell ∷ rest) =
  ℚP.+-mono-≤
    (upperActiveEnergyBelowLower cell)
    (superlevelBadMassMonotone rest)

record PhysicalThresholdProfilePair : Set where
  field
    lowerThreshold upperThreshold : ℚ
    thresholdOrder : lowerThreshold ≤ upperThreshold
    cells : List NestedSuperlevelEnergyCell

open PhysicalThresholdProfilePair public

physicalThresholdProfileMonotone :
  (profile : PhysicalThresholdProfilePair) →
  upperBadMass (cells profile) ≤ lowerBadMass (cells profile)
physicalThresholdProfileMonotone profile =
  superlevelBadMassMonotone (cells profile)

hhDirectionalSuperlevelMonotonicityClosed : Bool
hhDirectionalSuperlevelMonotonicityClosed = true

physicalThresholdProfilePairFromDirectionalDefectConstructed : Bool
physicalThresholdProfilePairFromDirectionalDefectConstructed = false

hhDirectionalSuperlevelMonotonicityClosedIsTrue :
  hhDirectionalSuperlevelMonotonicityClosed ≡ true
hhDirectionalSuperlevelMonotonicityClosedIsTrue = refl
