module DASHI.Physics.Constructive.FinitePolymerKPBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Roman Kotecky and David Preiss,
-- "Cluster expansion for abstract polymer models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- DASHI CONTRIBUTION
--
-- Construct an exact three-polymer incompatibility model.  Polymer alpha is
-- incompatible with beta and gamma, while beta and gamma are compatible.
-- Unit weighted activities give incompatibility sums 2,1,1, exactly meeting
-- the chosen size budgets 2,1,1.  The hard-core partition function is
-- enumerated from the five compatible families and equals 5.
--
-- This is a finite KP-style budget witness.  Exponential activity weights,
-- arbitrary polymer families, logarithmic cluster coefficients, thermodynamic
-- limits and Yang--Mills large-field estimates remain separate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Nat.Base using (_≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_)


data Polymer : Set where
  alpha beta gamma : Polymer

polymerActivity : Polymer → Nat
polymerActivity alpha = 1
polymerActivity beta = 1
polymerActivity gamma = 1

polymerMajorant : Polymer → Nat
polymerMajorant alpha = 1
polymerMajorant beta = 1
polymerMajorant gamma = 1

weightedActivity : Polymer → Nat
weightedActivity polymer =
  polymerActivity polymer * polymerMajorant polymer

incompatible : Polymer → Polymer → Bool
incompatible alpha alpha = false
incompatible alpha beta = true
incompatible alpha gamma = true
incompatible beta alpha = true
incompatible beta beta = false
incompatible beta gamma = false
incompatible gamma alpha = true
incompatible gamma beta = false
incompatible gamma gamma = false

incompatibilitySymmetric : ∀ first second →
  incompatible first second ≡ incompatible second first
incompatibilitySymmetric alpha alpha = refl
incompatibilitySymmetric alpha beta = refl
incompatibilitySymmetric alpha gamma = refl
incompatibilitySymmetric beta alpha = refl
incompatibilitySymmetric beta beta = refl
incompatibilitySymmetric beta gamma = refl
incompatibilitySymmetric gamma alpha = refl
incompatibilitySymmetric gamma beta = refl
incompatibilitySymmetric gamma gamma = refl

allPolymers : List Polymer
allPolymers = alpha ∷ beta ∷ gamma ∷ []

sumNat : List Nat → Nat
sumNat [] = zero
sumNat (value ∷ values) = value + sumNat values

incompatibleWeightedActivities : Polymer → List Nat
incompatibleWeightedActivities alpha =
  weightedActivity beta ∷ weightedActivity gamma ∷ []
incompatibleWeightedActivities beta =
  weightedActivity alpha ∷ []
incompatibleWeightedActivities gamma =
  weightedActivity alpha ∷ []

incompatibilityWeight : Polymer → Nat
incompatibilityWeight polymer =
  sumNat (incompatibleWeightedActivities polymer)

polymerSizeBudget : Polymer → Nat
polymerSizeBudget alpha = 2
polymerSizeBudget beta = 1
polymerSizeBudget gamma = 1

alphaBudgetExact : incompatibilityWeight alpha ≡ polymerSizeBudget alpha
alphaBudgetExact = refl

betaBudgetExact : incompatibilityWeight beta ≡ polymerSizeBudget beta
betaBudgetExact = refl

gammaBudgetExact : incompatibilityWeight gamma ≡ polymerSizeBudget gamma
gammaBudgetExact = refl

finiteKPCriterion : ∀ polymer →
  incompatibilityWeight polymer ≤ polymerSizeBudget polymer
finiteKPCriterion alpha = ≤-refl
finiteKPCriterion beta = ≤-refl
finiteKPCriterion gamma = ≤-refl

------------------------------------------------------------------------
-- Exact compatible-family enumeration.
------------------------------------------------------------------------

data CompatibleFamily : Set where
  emptyFamily
  alphaFamily
  betaFamily
  gammaFamily
  betaGammaFamily : CompatibleFamily

familyWeight : CompatibleFamily → Nat
familyWeight emptyFamily = 1
familyWeight alphaFamily = polymerActivity alpha
familyWeight betaFamily = polymerActivity beta
familyWeight gammaFamily = polymerActivity gamma
familyWeight betaGammaFamily = polymerActivity beta * polymerActivity gamma

compatibleFamilies : List CompatibleFamily
compatibleFamilies =
  emptyFamily
  ∷ alphaFamily
  ∷ betaFamily
  ∷ gammaFamily
  ∷ betaGammaFamily
  ∷ []

mapFamilyWeight : List CompatibleFamily → List Nat
mapFamilyWeight [] = []
mapFamilyWeight (family ∷ families) =
  familyWeight family ∷ mapFamilyWeight families

finitePolymerPartitionFunction : Nat
finitePolymerPartitionFunction =
  sumNat (mapFamilyWeight compatibleFamilies)

partitionFunctionIsFive : finitePolymerPartitionFunction ≡ 5
partitionFunctionIsFive = refl

record FiniteKPBudgetCertificate : Set where
  field
    symmetricIncompatibility : ∀ first second →
      incompatible first second ≡ incompatible second first
    alphaBudget : incompatibilityWeight alpha ≤ polymerSizeBudget alpha
    betaBudget : incompatibilityWeight beta ≤ polymerSizeBudget beta
    gammaBudget : incompatibilityWeight gamma ≤ polymerSizeBudget gamma
    partitionEnumeration : finitePolymerPartitionFunction ≡ 5

canonicalFiniteKPBudgetCertificate : FiniteKPBudgetCertificate
canonicalFiniteKPBudgetCertificate = record
  { symmetricIncompatibility = incompatibilitySymmetric
  ; alphaBudget = finiteKPCriterion alpha
  ; betaBudget = finiteKPCriterion beta
  ; gammaBudget = finiteKPCriterion gamma
  ; partitionEnumeration = partitionFunctionIsFive
  }

record GeneralKPClusterBoundary : Set₁ where
  field
    GeneralPolymer : Set
    activityNorm : GeneralPolymer → Set
    incompatibilityGraph : Set
    exponentialMajorant : Set
    kpStrictInequality : Set
    absolutelyConvergentClusterExpansion : Set
    logarithmicPartitionFunction : Set
    correlationDecay : Set
    thermodynamicLimit : Set
