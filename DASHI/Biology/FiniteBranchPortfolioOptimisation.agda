module DASHI.Biology.FiniteBranchPortfolioOptimisation where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.DirectedAttractorPortfolioCalculus as Directed

data Portfolio3 : Set where
  emptyPortfolio alignedOnly exploreOnly trapOnly alignedExplore alignedTrap exploreTrap allThree : Portfolio3

rawBranchCount : Portfolio3 → Nat
rawBranchCount emptyPortfolio = 0
rawBranchCount alignedOnly = 1
rawBranchCount exploreOnly = 1
rawBranchCount trapOnly = 1
rawBranchCount alignedExplore = 2
rawBranchCount alignedTrap = 2
rawBranchCount exploreTrap = 2
rawBranchCount allThree = 3

effectiveBasinCount : Portfolio3 → Nat
effectiveBasinCount emptyPortfolio = 0
effectiveBasinCount alignedOnly = 1
effectiveBasinCount exploreOnly = 1
effectiveBasinCount trapOnly = 1
effectiveBasinCount alignedExplore = 2
effectiveBasinCount alignedTrap = 2
effectiveBasinCount exploreTrap = 2
effectiveBasinCount allThree = 2

portfolioBenefit : Portfolio3 → Nat
portfolioBenefit emptyPortfolio = 0
portfolioBenefit alignedOnly = 4
portfolioBenefit exploreOnly = 2
portfolioBenefit trapOnly = 2
portfolioBenefit alignedExplore = 7
portfolioBenefit alignedTrap = 6
portfolioBenefit exploreTrap = 4
portfolioBenefit allThree = 9

portfolioBurden : Portfolio3 → Nat
portfolioBurden emptyPortfolio = 0
portfolioBurden alignedOnly = 1
portfolioBurden exploreOnly = 1
portfolioBurden trapOnly = 4
portfolioBurden alignedExplore = 2
portfolioBurden alignedTrap = 6
portfolioBurden exploreTrap = 5
portfolioBurden allThree = 8

portfolioValue : Portfolio3 → Nat
portfolioValue p = portfolioBenefit p ∸ portfolioBurden p

portfolioServiceable : Portfolio3 → Bool
portfolioServiceable _ = true

portfolioReading : Portfolio3 → String
portfolioReading emptyPortfolio = "No branch is serviced; cost is zero and no progress or information is produced."
portfolioReading alignedOnly = "The aligned branch produces progress with bounded servicing burden."
portfolioReading exploreOnly = "The exploratory branch produces information but less direct progress."
portfolioReading trapOnly = "The attractive dead end has local benefit cancelled by capture burden."
portfolioReading alignedExplore = "Aligned progress and exploration reinforce one another and form the optimal finite portfolio."
portfolioReading alignedTrap = "The trap route interferes with aligned progress and removes its positive net value."
portfolioReading exploreTrap = "Capture burden cancels the informational branch."
portfolioReading allThree = "All branches remain serviceable, but capture and interference make maximum raw count suboptimal."

emptyValueIsZero : portfolioValue emptyPortfolio ≡ 0
emptyValueIsZero = refl
alignedOnlyValueIsThree : portfolioValue alignedOnly ≡ 3
alignedOnlyValueIsThree = refl
exploreOnlyValueIsOne : portfolioValue exploreOnly ≡ 1
exploreOnlyValueIsOne = refl
trapOnlyValueIsZero : portfolioValue trapOnly ≡ 0
trapOnlyValueIsZero = refl
alignedExploreValueIsFive : portfolioValue alignedExplore ≡ 5
alignedExploreValueIsFive = refl
alignedTrapValueIsZero : portfolioValue alignedTrap ≡ 0
alignedTrapValueIsZero = refl
exploreTrapValueIsZero : portfolioValue exploreTrap ≡ 0
exploreTrapValueIsZero = refl
allThreeValueIsOne : portfolioValue allThree ≡ 1
allThreeValueIsOne = refl

one≤five : 1 ≤ 5
one≤five = s≤s z≤n
three≤five : 3 ≤ 5
three≤five = s≤s (s≤s (s≤s z≤n))
five≤five : 5 ≤ 5
five≤five = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

alignedExploreDominates : (candidate : Portfolio3) → portfolioValue candidate ≤ portfolioValue alignedExplore
alignedExploreDominates emptyPortfolio = z≤n
alignedExploreDominates alignedOnly = three≤five
alignedExploreDominates exploreOnly = one≤five
alignedExploreDominates trapOnly = z≤n
alignedExploreDominates alignedExplore = five≤five
alignedExploreDominates alignedTrap = z≤n
alignedExploreDominates exploreTrap = z≤n
alignedExploreDominates allThree = one≤five

record OptimalPortfolio (portfolio : Portfolio3) : Set where
  constructor optimalPortfolio
  field dominatesEveryPortfolio : (candidate : Portfolio3) → portfolioValue candidate ≤ portfolioValue portfolio

open OptimalPortfolio public

alignedExploreOptimal : OptimalPortfolio alignedExplore
alignedExploreOptimal = optimalPortfolio alignedExploreDominates

allThreeCountIsThree : rawBranchCount allThree ≡ 3
allThreeCountIsThree = refl
allThreeEffectiveCountIsTwo : effectiveBasinCount allThree ≡ 2
allThreeEffectiveCountIsTwo = refl
allThreeIsServiceable : portfolioServiceable allThree ≡ true
allThreeIsServiceable = refl

two≤five : 2 ≤ 5
two≤five = s≤s (s≤s z≤n)

maxCountBelowOptimal : portfolioValue allThree < portfolioValue alignedExplore
maxCountBelowOptimal = two≤five

threeNotEqualTwo : ¬ (3 ≡ 2)
threeNotEqualTwo ()

record MaximumCountSuboptimalWitness : Set where
  constructor maximumCountSuboptimalWitness
  field
    maximumCountPortfolio selectedOptimalPortfolio : Portfolio3
    maximumCountIsThree : rawBranchCount maximumCountPortfolio ≡ 3
    maximumCountServiceable : portfolioServiceable maximumCountPortfolio ≡ true
    maximumCountEffectiveBasins : effectiveBasinCount maximumCountPortfolio ≡ 2
    rawAndEffectiveCountsDiffer : ¬ (3 ≡ 2)
    maximumCountHasLowerValue : portfolioValue maximumCountPortfolio < portfolioValue selectedOptimalPortfolio
    selectedPortfolioIsOptimal : OptimalPortfolio selectedOptimalPortfolio

canonicalMaximumCountSuboptimal : MaximumCountSuboptimalWitness
canonicalMaximumCountSuboptimal =
  maximumCountSuboptimalWitness allThree alignedExplore refl refl refl threeNotEqualTwo maxCountBelowOptimal alignedExploreOptimal

alignedPlusExploreBaseBenefit : Nat
alignedPlusExploreBaseBenefit = portfolioBenefit alignedOnly + portfolioBenefit exploreOnly

alignedExploreComplementarityBonus : Nat
alignedExploreComplementarityBonus = portfolioBenefit alignedExplore ∸ alignedPlusExploreBaseBenefit

alignedExploreBonusIsOne : alignedExploreComplementarityBonus ≡ 1
alignedExploreBonusIsOne = refl

alignedTrapJointBurdenExceedsSeparateBurden :
  portfolioBurden alignedOnly + portfolioBurden trapOnly < portfolioBurden alignedTrap
alignedTrapJointBurdenExceedsSeparateBurden =
  s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

record AdditionComparison : Set where
  constructor additionComparison
  field
    basePortfolio extendedPortfolio : Portfolio3
    baseValue extendedValue : Nat
    additionReading : String

open AdditionComparison public

explorationAddedToAligned : AdditionComparison
explorationAddedToAligned = additionComparison alignedOnly alignedExplore
  (portfolioValue alignedOnly) (portfolioValue alignedExplore)
  "Adding exploration to the aligned branch is constructive because complementarity exceeds servicing burden."

trapAddedToAligned : AdditionComparison
trapAddedToAligned = additionComparison alignedOnly alignedTrap
  (portfolioValue alignedOnly) (portfolioValue alignedTrap)
  "Adding the trap branch destroys value because capture and interference exceed its local benefit."

alignedAdditionConstructive : baseValue explorationAddedToAligned < extendedValue explorationAddedToAligned
alignedAdditionConstructive = s≤s (s≤s (s≤s (s≤s z≤n)))

trapAdditionDestructive : extendedValue trapAddedToAligned < baseValue trapAddedToAligned
trapAdditionDestructive = s≤s z≤n

record FinitePortfolioOptimisationBoundary : Set where
  constructor finitePortfolioOptimisationBoundary
  field
    maximumCountIsOptimalPromotion : Bool
    maximumCountIsOptimalPromotionIsFalse : maximumCountIsOptimalPromotion ≡ false
    serviceablePortfolioIsOptimalPromotion : Bool
    serviceablePortfolioIsOptimalPromotionIsFalse : serviceablePortfolioIsOptimalPromotion ≡ false
    rawCountEqualsEffectiveDiversityPromotion : Bool
    rawCountEqualsEffectiveDiversityPromotionIsFalse : rawCountEqualsEffectiveDiversityPromotion ≡ false
    positiveLocalBenefitImpliesConstructiveAdditionPromotion : Bool
    positiveLocalBenefitImpliesConstructiveAdditionPromotionIsFalse : positiveLocalBenefitImpliesConstructiveAdditionPromotion ≡ false
    finiteOptimalPortfolioEqualsUniversalPolicyPromotion : Bool
    finiteOptimalPortfolioEqualsUniversalPolicyPromotionIsFalse : finiteOptimalPortfolioEqualsUniversalPolicyPromotion ≡ false
    boundaryReading : String

open FinitePortfolioOptimisationBoundary public

canonicalFinitePortfolioOptimisationBoundary : FinitePortfolioOptimisationBoundary
canonicalFinitePortfolioOptimisationBoundary =
  finitePortfolioOptimisationBoundary false refl false refl false refl false refl false refl
    "The exact eight-case optimiser proves that a serviceable maximum-count portfolio can have fewer effective basins and lower value than a smaller coherent portfolio. Branch addition is evaluated relative to interaction, capture, and complementarity rather than local benefit alone."
