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
-- literal nested-superlevel condition and then instantiated on the repository's
-- actual physical directional defect Theta=1-(xi.eta)^2.
--
-- For a fixed physical energy cell and two thresholds s1 <= s2,
--
--   Theta > s2  ==>  Theta > s1.
--
-- Encoding the rational comparison as a Bool gives the exact finite theorem
--
--   E 1_{Theta>s2} <= E 1_{Theta>s1}.
--
-- Summing over cells proves the monotone bad-mass profile M(s2)<=M(s1).
-- Thus good/bad classification is a late cut through one underlying defect
-- distribution, not two unrelated dynamical quantities.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical

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

------------------------------------------------------------------------
-- Actual rational superlevel classifier for the physical directional defect.
------------------------------------------------------------------------

superlevelActive : ℚ → ℚ → Bool
superlevelActive threshold defect with ℚP._<?_ threshold defect
... | yes _ = true
... | no _ = false

superlevelNested :
  ∀ lowerThreshold upperThreshold defect →
  lowerThreshold ≤ upperThreshold →
  superlevelActive upperThreshold defect ≡ true →
  superlevelActive lowerThreshold defect ≡ true
superlevelNested lower upper defect lower≤upper
  with ℚP._<?_ upper defect | ℚP._<?_ lower defect
... | yes upper<defect | yes lower<defect = λ _ → refl
... | yes upper<defect | no notLower<defect =
  λ _ → ⊥-elim
    (notLower<defect (ℚP.≤-<-trans lower≤upper upper<defect))
... | no notUpper<defect | yes lower<defect = λ ()
... | no notUpper<defect | no notLower<defect = λ ()

record PhysicalDirectionalEnergyAtom : Set where
  field
    pair : Physical.PhysicalVorticityPair
    energyWeight : ℚ
    energyWeightNonnegative : 0ℚ ≤ energyWeight

open PhysicalDirectionalEnergyAtom public

physicalDefect : PhysicalDirectionalEnergyAtom → ℚ
physicalDefect atom = Gram.directionalDefect (Physical.directions (pair atom))

asNestedSuperlevelCell :
  (lowerThreshold upperThreshold : ℚ) →
  lowerThreshold ≤ upperThreshold →
  PhysicalDirectionalEnergyAtom →
  NestedSuperlevelEnergyCell
asNestedSuperlevelCell lower upper lower≤upper atom = record
  { energy = energyWeight atom
  ; energyNonnegative = energyWeightNonnegative atom
  ; lowerActive = superlevelActive lower (physicalDefect atom)
  ; upperActive = superlevelActive upper (physicalDefect atom)
  ; nestedSuperlevel = superlevelNested lower upper (physicalDefect atom) lower≤upper
  }

mapNestedCells :
  (lowerThreshold upperThreshold : ℚ) →
  lowerThreshold ≤ upperThreshold →
  List PhysicalDirectionalEnergyAtom → List NestedSuperlevelEnergyCell
mapNestedCells lower upper lower≤upper [] = []
mapNestedCells lower upper lower≤upper (atom ∷ rest) =
  asNestedSuperlevelCell lower upper lower≤upper atom
  ∷ mapNestedCells lower upper lower≤upper rest

record PhysicalThresholdProfilePair : Set where
  field
    lowerThreshold upperThreshold : ℚ
    thresholdOrder : lowerThreshold ≤ upperThreshold
    atoms : List PhysicalDirectionalEnergyAtom

open PhysicalThresholdProfilePair public

profileCells : PhysicalThresholdProfilePair → List NestedSuperlevelEnergyCell
profileCells profile =
  mapNestedCells
    (lowerThreshold profile)
    (upperThreshold profile)
    (thresholdOrder profile)
    (atoms profile)

physicalThresholdProfileMonotone :
  (profile : PhysicalThresholdProfilePair) →
  upperBadMass (profileCells profile) ≤ lowerBadMass (profileCells profile)
physicalThresholdProfileMonotone profile =
  superlevelBadMassMonotone (profileCells profile)

physicalThresholdProfilePair :
  (lowerThreshold upperThreshold : ℚ) →
  lowerThreshold ≤ upperThreshold →
  List PhysicalDirectionalEnergyAtom → PhysicalThresholdProfilePair
physicalThresholdProfilePair lower upper order atoms = record
  { lowerThreshold = lower
  ; upperThreshold = upper
  ; thresholdOrder = order
  ; atoms = atoms
  }

hhDirectionalSuperlevelMonotonicityClosed : Bool
hhDirectionalSuperlevelMonotonicityClosed = true

physicalThresholdProfilePairFromDirectionalDefectConstructed : Bool
physicalThresholdProfilePairFromDirectionalDefectConstructed = true

hhDirectionalSuperlevelMonotonicityClosedIsTrue :
  hhDirectionalSuperlevelMonotonicityClosed ≡ true
hhDirectionalSuperlevelMonotonicityClosedIsTrue = refl

physicalThresholdProfilePairFromDirectionalDefectConstructedIsTrue :
  physicalThresholdProfilePairFromDirectionalDefectConstructed ≡ true
physicalThresholdProfilePairFromDirectionalDefectConstructedIsTrue = refl
