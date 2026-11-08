module DASHI.Moonshine.MonsterSpecialGravityKKWeightTwoCrosswalkExact where

------------------------------------------------------------------------
-- MONSTROUS GRAVITY / FLM GRIESS: EXACT DIMENSION CROSSWALK ONLY.
--
-- Chester--Marrani--Rios, "Monstrous M-Theory", Symmetry 15 (2023) 490,
-- DOI 10.3390/sym15020490.
-- Their proposed 26+1 Einstein/p-form model has a massless 25+1
-- reduced spectrum written as
--
--       1 dilaton + 299 graviton + 98280 + 98304 = 196884.
--
-- This agrees as a FINITE DIMENSION SPLIT with the already-owned FLM
-- orbifold V2 expression:
--
--       dim Sym^2(h_24) + 196560/2 + 24*4096
--          = 300 + 98280 + 98304 = 196884.
--
-- Here 300 = 1 + 299 is the conformal-line versus traceless split
-- at the level of CARDINAL NUMBERS. It is NOT a KK=FLM actual mode
-- isomorphism, an actual Monster gravity action, a SUSY theorem,
-- AdS3 gravity duality, or a 4D Yang--Mills mass-gap proof.
--
-- Witten (2007) arXiv:0706.3359 is a proposed Monster-CFT/AdS3
-- duality, not a theorem that 194 Monster conjugacy classes correspond
-- one-to-one to black holes. Borcherds no-ghost is an established
-- Monster Lie algebra/string theorem, not a four-dimensional YM gap.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Moonshine.MoonshineOrbifoldWeightTwoDecompositionExact as FLM

dilatonCount : Nat
dilatonCount = 1

reducedGravitonPolarizations : Nat
reducedGravitonPolarizations = 299

leechEvenNormFourCount : Nat
leechEvenNormFourCount = FLM.pairedNormFourOrbitCount

twistedGravityComparisonCount : Nat
twistedGravityComparisonCount = FLM.twistedInvariantWeightTwoDimension

gravitoDilatonSymmetricCount : Nat
gravitoDilatonSymmetricCount =
  dilatonCount + reducedGravitonPolarizations

gravitoDilatonSymmetricCountIs300 :
  gravitoDilatonSymmetricCount ≡ FLM.symmetricSquareDimension
gravitoDilatonSymmetricCountIs300 = refl

specialGravityProposedMasslessCount : Nat
specialGravityProposedMasslessCount =
  gravitoDilatonSymmetricCount + leechEvenNormFourCount
  + twistedGravityComparisonCount

proposedMasslessCountIs196884 :
  specialGravityProposedMasslessCount ≡ FLM.moonshineWeightTwoDimension
proposedMasslessCountIs196884 = refl

nontrivialMonsterCountMatches :
  reducedGravitonPolarizations + leechEvenNormFourCount
    + twistedGravityComparisonCount
  ≡ FLM.monsterNontrivialWeightTwoDimension
nontrivialMonsterCountMatches = refl

------------------------------------------------------------------------
-- CHester--Marrani--Rios p-FORM CONTENT, exact published equation (72):
--   98280 = C(24,5) + 4*C(24,4) + 6*C(24,3)
--                 + 4*C(24,2) + 24.
-- This decomposes the 98280 COUNT; it does not turn p-form states into
-- the actual FLM norm-four lattice vectors or their Monster action.
------------------------------------------------------------------------

fiveFormLittleGroupDimension : Nat
fiveFormLittleGroupDimension = 42504

fourFormLittleGroupDimension : Nat
fourFormLittleGroupDimension = 10626

threeFormLittleGroupDimension : Nat
threeFormLittleGroupDimension = 2024

twoFormLittleGroupDimension : Nat
twoFormLittleGroupDimension = 276

vectorLittleGroupDimension : Nat
vectorLittleGroupDimension = 24

masslessPFormLeechComparison : Nat
masslessPFormLeechComparison =
  fiveFormLittleGroupDimension
  + 4 * fourFormLittleGroupDimension
  + 6 * threeFormLittleGroupDimension
  + 4 * twoFormLittleGroupDimension
  + vectorLittleGroupDimension

pFormSpectrumIsLeechNormFourOrbitCount :
  masslessPFormLeechComparison ≡ FLM.pairedNormFourOrbitCount
pFormSpectrumIsLeechNormFourOrbitCount = refl

-- EXACT TYPED coordinate chart on the GRAVITY SIDE.
GravityDilaton : Set
GravityDilaton = Fin dilatonCount

GravityTracelessMetric : Set
GravityTracelessMetric = Fin reducedGravitonPolarizations

GravityLeechComparison : Set
GravityLeechComparison = Fin leechEvenNormFourCount

GravityTwistedComparison : Set
GravityTwistedComparison = FLM.TwistedInvariantWeightTwoCoordinate

-- We deliberately do NOT declare the gravity full carrier to be the
-- canonical Griess algebra. Its first two sector tags carry different
-- interpretation. A valid Monster/KK action would have to preserve the
-- actual source dynamics and Griess first product, not just cardinality.
GravityScalarOrMetric : Set
GravityScalarOrMetric = GravityDilaton ⊎ GravityTracelessMetric

GravityCandidateCoordinate : Set
GravityCandidateCoordinate =
  (GravityScalarOrMetric ⊎ GravityLeechComparison)
  ⊎ GravityTwistedComparison

gravityDilatonCoordinate : GravityCandidateCoordinate
gravityDilatonCoordinate = inj₁ (inj₁ (inj₁ zero))

gravityMetricCoordinate : GravityTracelessMetric → GravityCandidateCoordinate
gravityMetricCoordinate m = inj₁ (inj₁ (inj₂ m))

gravityLeechCoordinate : GravityLeechComparison → GravityCandidateCoordinate
gravityLeechCoordinate l = inj₁ (inj₂ l)

gravityTwistedCoordinate : GravityTwistedComparison → GravityCandidateCoordinate
gravityTwistedCoordinate t = inj₂ t

dilatonIsDistinctFromEveryMetricCoordinate :
  (metric : GravityTracelessMetric) →
  gravityDilatonCoordinate ≡ gravityMetricCoordinate metric → ⊥
dilatonIsDistinctFromEveryMetricCoordinate metric ()

dilatonDistinctFromTwisted :
  (t : GravityTwistedComparison) →
  gravityDilatonCoordinate ≡ gravityTwistedCoordinate t → ⊥
dilatonDistinctFromTwisted t ()

-- An abstract numerical matching is not a Griess automorphism
-- or representation equivalence: no action, multiplier, original
-- first product or mixed operator data enters the proofs above.
record ActualSpecialGravityPromotion : Set where
  field
    actualActionConstructed : Bool
    actualGriessModeOneWeldConstructed : Bool
    actualKKFieldEquationAndSourceMetricConstructed : Bool
    actualAdS3GravityDualityProved : Bool
    actualFourDimensionalYMMassGapProved : Bool

onlyArithmeticComparison : ActualSpecialGravityPromotion
onlyArithmeticComparison = record
  { actualActionConstructed = false
  ; actualGriessModeOneWeldConstructed = false
  ; actualKKFieldEquationAndSourceMetricConstructed = false
  ; actualAdS3GravityDualityProved = false
  ; actualFourDimensionalYMMassGapProved = false
  }
