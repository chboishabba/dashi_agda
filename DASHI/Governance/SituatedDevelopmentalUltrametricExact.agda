module DASHI.Governance.SituatedDevelopmentalUltrametricExact where

-- DASHI ORIGINAL FINITE ULTRAMETRIC MODEL.
-- A rooted tree is a candidate representation of developmental timing and
-- shared context, NOT a clinical assertion that an early ACE irreversibly
-- sets glucocorticoid receptor density or an adult attractor basin.
-- The tree, not a person identity, supplies the distance.
open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as NF

-- Two nested partitions: childhood branch and later situated branch.
data ChildhoodBranch : Set where sharedBranch otherBranch : ChildhoodBranch
data AdultBranch : Set where localA localB : AdultBranch

record DevelopmentalLeaf : Set where
  constructor developmental-leaf
  field
    childhood : ChildhoodBranch
    adulthood : AdultBranch
open DevelopmentalLeaf public

-- Distance levels are exact natural-number surrogates for an ultrametric:
-- 0 same leaf, 1 same early branch/different later branch,
-- 2 diverged at the earlier branch. This is not literally |x-y|_3;
-- embeddings into 3-adic balls would require a separate digit map.
treeDistance : DevelopmentalLeaf → DevelopmentalLeaf → Nat
treeDistance (developmental-leaf sharedBranch localA)
             (developmental-leaf sharedBranch localA) = 0
treeDistance (developmental-leaf sharedBranch localB)
             (developmental-leaf sharedBranch localB) = 0
treeDistance (developmental-leaf otherBranch localA)
             (developmental-leaf otherBranch localA) = 0
treeDistance (developmental-leaf otherBranch localB)
             (developmental-leaf otherBranch localB) = 0
treeDistance (developmental-leaf sharedBranch _) (developmental-leaf sharedBranch _) = 1
treeDistance (developmental-leaf otherBranch _) (developmental-leaf otherBranch _) = 1
treeDistance (developmental-leaf sharedBranch _) (developmental-leaf otherBranch _) = 2
treeDistance (developmental-leaf otherBranch _) (developmental-leaf sharedBranch _) = 2

leafA : DevelopmentalLeaf
leafA = developmental-leaf sharedBranch localA
leafB : DevelopmentalLeaf
leafB = developmental-leaf sharedBranch localB
leafC : DevelopmentalLeaf
leafC = developmental-leaf otherBranch localA

sameBranchClose : treeDistance leafA leafB ≡ 1
sameBranchClose = refl

differentEarlyBranchFar : treeDistance leafA leafC ≡ 2
differentEarlyBranchFar = refl

-- Show explicitly that identical adult "exposure" labels do not determine
-- earlier developmental ancestry. There is no biological response assignment.
data AdultExposure : Set where commonAdultExposure : AdultExposure
adultObservation : DevelopmentalLeaf → AdultExposure
adultObservation _ = commonAdultExposure

childhoodContext : DevelopmentalLeaf → ChildhoodBranch
childhoodContext = childhood

adultExposureDoesNotIdentifyChildhood :
  NF.NonFactorabilityWitness adultObservation childhoodContext
adultExposureDoesNotIdentifyChildhood =
  NF.nonFactorabilityWitness leafA leafC refl (λ ())

anyAdultExposureRechartStillLosesHistory :
  ∀ {Chart : Set} (chart : AdultExposure → Chart) →
  NF.FactorsThrough
    (λ leaf → chart (adultObservation leaf)) childhoodContext → ⊥
anyAdultExposureRechartStillLosesHistory chart =
  NF.rechartingCannotRecoverErasedPhenomenon chart
    adultExposureDoesNotIdentifyChildhood

-- The developmental sensitivity and physiological map are independent,
-- evidence-dependent parameters. Ultrametric distance is not causality.
record DevelopmentalCalibration (Response : Set) : Set₁ where
  field
    response : DevelopmentalLeaf → Response
    developmentalMeasurementEvidence : Set
    withinPersonTimingEvidence : Set
    alternativeHistoriesReviewed : Set
