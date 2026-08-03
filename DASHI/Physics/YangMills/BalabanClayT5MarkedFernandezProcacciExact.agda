module DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _≤ᵇ_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Separate Kotecký--Preiss and Fernández--Procacci marked criteria.
--
-- Roman Kotecký and David Preiss, "Cluster Expansion for Abstract Polymer
-- Models", Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Roberto Fernández and Aldo Procacci, "Cluster Expansion for Abstract Polymer
-- Models. New Bounds from an Old Approach", Communications in Mathematical
-- Physics 274 (2007), 123--140.
-- DOI: 10.1007/s00220-007-0279-2; arXiv:math-ph/0605041.
--
-- The criteria are not conflated.  The FP neighborhood partition function is
-- retained explicitly and gives the stronger eight-clique threshold used below.
------------------------------------------------------------------------

sumℚ : List ℚ → ℚ
sumℚ [] = 0ℚ
sumℚ (x ∷ xs) = x + sumℚ xs

record AbstractPolymerModel (Polymer : Set) : Set₁ where
  field
    incompatible : Polymer → Polymer → Set
    activity : Polymer → ℚ
    absoluteActivity : Polymer → ℚ
    activityAbsoluteDefinition : ∀ polymer → Set
    activityNonnegative : ∀ polymer → 0ℚ ≤ absoluteActivity polymer

open AbstractPolymerModel public

record KoteckyPreissCriterion (Polymer : Set)
    (model : AbstractPolymerModel Polymer) : Set₁ where
  field
    sizeWeight : Polymer → ℚ
    exponentialWeight : Polymer → ℚ
    incompatibleNeighborhood : Polymer → List Polymer

    neighborhoodComplete : ∀ root incompatiblePolymer →
      incompatible model root incompatiblePolymer → Set

    kpWeightedNeighborhoodSum : Polymer → ℚ
    kpWeightedNeighborhoodSumDefinition : ∀ root → Set
    kpCriterion : ∀ root →
      kpWeightedNeighborhoodSum root ≤ sizeWeight root

open KoteckyPreissCriterion public

record FernandezProcacciCriterion (Polymer : Set)
    (model : AbstractPolymerModel Polymer) : Set₁ where
  field
    majorant : Polymer → ℚ
    incompatibleNeighborhood : Polymer → List Polymer

    compatibleSubfamilies : List Polymer → List (List Polymer)
    familyWeight : List Polymer → ℚ
    neighborhoodPartitionFunction : Polymer → ℚ

    familyWeightDefinition : ∀ family → Set
    compatibleSubfamiliesExact : ∀ root → Set
    neighborhoodPartitionFunctionDefinition : ∀ root → Set

    fpCriterion : ∀ polymer →
      absoluteActivity model polymer
        * neighborhoodPartitionFunction polymer
      ≤ majorant polymer

open FernandezProcacciCriterion public

------------------------------------------------------------------------
-- Exact eight-way clique calculation.
------------------------------------------------------------------------

mu rhoBase rhoFPMax fpEightCliquePhi fpSlack : ℚ
mu = + 1 / 4
rhoBase = + 1 / 16
rhoFPMax = + 1 / 12
fpEightCliquePhi = + 3 / 1
fpSlack = + 1 / 48

onePlusEightMuExact :
  1ℚ + (+ 8 / 1) * mu ≡ fpEightCliquePhi
onePlusEightMuExact = ℚRing.solve []
muOverPhiExact :
  mu / fpEightCliquePhi ≡ rhoFPMax
muOverPhiExact = ℚRing.solve []
baseBelowFPMaximum : rhoBase ≤ rhoFPMax
baseBelowFPMaximum = ℚP.≤ᵇ⇒≤ tt

fpSlackExact : rhoFPMax - rhoBase ≡ fpSlack
fpSlackExact = ℚRing.solve []
record EightCliqueNeighborhood (Polymer : Set) : Set₁ where
  field
    root : Polymer
    extensions : List Polymer
    extensionCountIsEight : Set
    everyExtensionIncompatibleWithRoot : ∀ extension → Set
    distinctExtensionsPairwiseIncompatible : Set

    compatibleSubfamiliesAreEmptyOrSingleton : Set
    allMajorantsEqualMu : ∀ extension → Set
    neighborhoodPartitionFunctionIsOnePlusEightMu : Set

open EightCliqueNeighborhood public

------------------------------------------------------------------------
-- Marked activities.  The rational 6/5 inflation target is kept separate from
-- the logarithmic 1/5 action slack.  A source estimate must prove the former
-- from the latter; the formalism does not identify additive and multiplicative
-- margins.
------------------------------------------------------------------------

markedInflation markedActivityMaximum markedFPSlack : ℚ
markedInflation = + 6 / 5
markedActivityMaximum = + 3 / 40
markedFPSlack = + 1 / 120

markedBaseActivityExact :
  markedInflation * rhoBase ≡ markedActivityMaximum
markedBaseActivityExact = ℚRing.solve []
markedActivityBelowFPMaximum : markedActivityMaximum ≤ rhoFPMax
markedActivityBelowFPMaximum = ℚP.≤ᵇ⇒≤ tt

markedFPSlackExact : rhoFPMax - markedActivityMaximum ≡ markedFPSlack
markedFPSlackExact = ℚRing.solve []
record MarkedActivityData (Polymer Observable : Set)
    (model : AbstractPolymerModel Polymer) : Set₁ where
  field
    source : Observable → ℚ
    markedActivity : Observable → Polymer → ℚ
    absoluteMarkedActivity : Observable → Polymer → ℚ

    sourceAdmissible : Observable → Set
    markedActivityDefinition : ∀ observable polymer → Set
    markedActivityAbsoluteDefinition : ∀ observable polymer → Set

    baseActivityBelowOneSixteenth : ∀ polymer →
      absoluteActivity model polymer ≤ rhoBase

    -- This explicit monotone-multiplication receipt avoids depending on a
    -- particular standard-library argument order for rational positivity lemmas.
    inflatedBaseActivityBelowThreeFortieths : ∀ polymer →
      markedInflation * absoluteActivity model polymer
      ≤ markedActivityMaximum

    logarithmicSourceCostBelowOneFifth : ∀ observable →
      sourceAdmissible observable → Set

    markedInflationBelowSixFifths : ∀ observable polymer →
      sourceAdmissible observable →
      absoluteMarkedActivity observable polymer
      ≤ markedInflation * absoluteActivity model polymer

open MarkedActivityData public

markedActivityBelowThreeFortieths :
  ∀ {Polymer Observable model}
    (dataSet : MarkedActivityData Polymer Observable model)
    observable polymer →
    sourceAdmissible dataSet observable →
    absoluteMarkedActivity dataSet observable polymer
    ≤ markedActivityMaximum
markedActivityBelowThreeFortieths dataSet observable polymer admissible =
  ℚP.≤-trans
    (markedInflationBelowSixFifths dataSet observable polymer admissible)
    (inflatedBaseActivityBelowThreeFortieths dataSet polymer)

markedActivityBelowFPThreshold :
  ∀ {Polymer Observable model}
    (dataSet : MarkedActivityData Polymer Observable model)
    observable polymer →
    sourceAdmissible dataSet observable →
    absoluteMarkedActivity dataSet observable polymer ≤ rhoFPMax
markedActivityBelowFPThreshold dataSet observable polymer admissible =
  ℚP.≤-trans
    (markedActivityBelowThreeFortieths dataSet observable polymer admissible)
    markedActivityBelowFPMaximum

record MarkedFernandezProcacciClosure
    (Polymer Observable : Set)
    (model : AbstractPolymerModel Polymer)
    (marked : MarkedActivityData Polymer Observable model) : Set₁ where
  field
    fp : FernandezProcacciCriterion Polymer model
    markedNeighborhoodPartitionFunction : Observable → Polymer → ℚ

    markedFPCondition : ∀ observable polymer →
      sourceAdmissible marked observable → Set

    markedClusterExpansionAbsolutelyConvergent : ∀ observable →
      sourceAdmissible marked observable → Set

    markedPartitionFunctionNonzero : ∀ observable →
      sourceAdmissible marked observable → Set

    markedLogPartitionAnalyticInSource : ∀ observable →
      sourceAdmissible marked observable → Set

    singleScaleExponentialMomentBound : ∀ observable →
      sourceAdmissible marked observable → Set

open MarkedFernandezProcacciClosure public

kpCriterionSeparatedLevel : ProofLevel
kpCriterionSeparatedLevel = machineChecked

fpEightCliqueArithmeticLevel : ProofLevel
fpEightCliqueArithmeticLevel = machineChecked

markedFPSlackArithmeticLevel : ProofLevel
markedFPSlackArithmeticLevel = machineChecked

markedFPClusterInputsLevel : ProofLevel
markedFPClusterInputsLevel = conditional
