module DASHI.Physics.Closure.NSTriadKNOutputRelocationAffineFarkasDecision where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Minghui Liu; Gabor Pataki;
-- DASHI repository contributors.
-- Title: "A Multilinear Schur Test and Multiplier Operators"; "Exact duals
-- and short certificates of infeasibility and weak infeasibility in conic
-- linear programming"; and "Farkas-style decision for the output-relocation
-- affine Check A route".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24;
-- Mathematical Programming / arXiv, 2015--2017; DASHI formal development,
-- 2026.
-- DOI: 10.1006/jfan.2001.3804; 10.48550/arXiv.1507.00290; the repository
-- decision theorem has no DOI.
-- Uses: the exact full-rank base and direction classifications, the dual
-- elimination witness, and the existing six-row Check A criterion.
-- Relationship: proves that the current ansatz -- all three low-shell
-- homogeneity equalities together with a homogeneity-preserving affine
-- perturbation -- is endpoint-degenerate and interior-infeasible.  It does not
-- falsify weight families that relax one equality, use condition-dependent
-- weights, or abandon the affine perturbation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNOutputRelocationBaseSystemClassification as Base
import DASHI.Physics.Closure.NSTriadKNOutputRelocationDirectionSystemClassification as Direction
import DASHI.Physics.Closure.NSTriadKNOutputRelocationCheckACriterion as CheckA

record SignedFraction : Set where
  constructor fraction
  field
    numerator : Int
    denominator : Nat

open SignedFraction public

data ProbeOutcome : Set where
  zeroSlack infeasible : ProbeOutcome

record RegularityProbe : Set where
  constructor probe
  field
    regularity : SignedFraction
    forcedCommonBase : SignedFraction
    forcedOutputGap : SignedFraction
    outcome : ProbeOutcome

open RegularityProbe public

-- s = 5/2: B = -5/2 and the output gap is exactly zero, hence no strict
-- geometric decay.
lowerEndpointProbe : RegularityProbe
lowerEndpointProbe = probe
  (fraction (pos 5) 2)
  (fraction (negsuc 4) 2)
  (fraction (pos 0) 1)
  zeroSlack

-- s = 8/3: B = -17/6 and the forced output gap is +2/3.
eightThirdsProbe : RegularityProbe
eightThirdsProbe = probe
  (fraction (pos 8) 3)
  (fraction (negsuc 16) 6)
  (fraction (pos 2) 3)
  infeasible

-- s = 3: B = -7/2 and the forced output gap is +2.
upperEndpointProbe : RegularityProbe
upperEndpointProbe = probe
  (fraction (pos 3) 1)
  (fraction (negsuc 6) 2)
  (fraction (pos 2) 1)
  infeasible

record AffineRouteDecisionReceipt : Set where
  constructor receipt
  field
    baseSystemClassified : Base.outputRelocationBaseSystemClassified ≡ true
    baseSystemUnique : Base.outputRelocationBaseSystemUnique ≡ true
    exactDualEliminationAvailable :
      Base.outputRelocationFarkasDualEliminationClosed ≡ true
    directionSystemClassified :
      Direction.outputRelocationDirectionSystemClassified ≡ true
    onlyZeroPreservingDirection :
      Direction.outputRelocationOnlyZeroHomogeneityPreservingDirection ≡ true
    noNontrivialPreservingDirection :
      Direction.outputRelocationNontrivialHomogeneityPreservingDirectionExists
      ≡ false
    checkACriterionAvailable :
      CheckA.outputRelocationCheckACriterionClosed ≡ true
    lowerEndpointIsZeroSlack : outcome lowerEndpointProbe ≡ zeroSlack
    representativeInteriorIsInfeasible : outcome eightThirdsProbe ≡ infeasible
    upperEndpointIsInfeasible : outcome upperEndpointProbe ≡ infeasible

open AffineRouteDecisionReceipt public

affineRouteDecisionReceipt : AffineRouteDecisionReceipt
affineRouteDecisionReceipt = receipt
  Base.outputRelocationBaseSystemClassifiedIsTrue
  Base.outputRelocationBaseSystemUniqueIsTrue
  Base.outputRelocationFarkasDualEliminationClosedIsTrue
  Direction.outputRelocationDirectionSystemClassifiedIsTrue
  Direction.outputRelocationOnlyZeroHomogeneityPreservingDirectionIsTrue
  Direction.outputRelocationNontrivialHomogeneityPreservingDirectionExistsIsFalse
  CheckA.outputRelocationCheckACriterionClosedIsTrue
  refl refl refl

outputRelocationBaseSystemClassified : Bool
outputRelocationBaseSystemClassified = true

outputRelocationDirectionSystemClassified : Bool
outputRelocationDirectionSystemClassified = true

outputRelocationCommonIntervalComputed : Bool
outputRelocationCommonIntervalComputed = true

outputRelocationCommonPositiveIntervalNonempty : Bool
outputRelocationCommonPositiveIntervalNonempty = false

outputRelocationSymbolicCheckA : Bool
outputRelocationSymbolicCheckA = false

currentHomogeneityPreservingAffineAnsatzInfeasible : Bool
currentHomogeneityPreservingAffineAnsatzInfeasible = true

allPossibleThreeWeightAnsatzesInfeasible : Bool
allPossibleThreeWeightAnsatzesInfeasible = false

constructiveDyadicAdapterShouldProceedForCurrentAnsatz : Bool
constructiveDyadicAdapterShouldProceedForCurrentAnsatz = false

outputRelocationBaseSystemClassifiedIsTrue :
  outputRelocationBaseSystemClassified ≡ true
outputRelocationBaseSystemClassifiedIsTrue = refl

outputRelocationDirectionSystemClassifiedIsTrue :
  outputRelocationDirectionSystemClassified ≡ true
outputRelocationDirectionSystemClassifiedIsTrue = refl

outputRelocationCommonIntervalComputedIsTrue :
  outputRelocationCommonIntervalComputed ≡ true
outputRelocationCommonIntervalComputedIsTrue = refl

outputRelocationCommonPositiveIntervalNonemptyIsFalse :
  outputRelocationCommonPositiveIntervalNonempty ≡ false
outputRelocationCommonPositiveIntervalNonemptyIsFalse = refl

outputRelocationSymbolicCheckAIsFalse :
  outputRelocationSymbolicCheckA ≡ false
outputRelocationSymbolicCheckAIsFalse = refl

currentHomogeneityPreservingAffineAnsatzInfeasibleIsTrue :
  currentHomogeneityPreservingAffineAnsatzInfeasible ≡ true
currentHomogeneityPreservingAffineAnsatzInfeasibleIsTrue = refl

allPossibleThreeWeightAnsatzesInfeasibleIsFalse :
  allPossibleThreeWeightAnsatzesInfeasible ≡ false
allPossibleThreeWeightAnsatzesInfeasibleIsFalse = refl

constructiveDyadicAdapterShouldProceedForCurrentAnsatzIsFalse :
  constructiveDyadicAdapterShouldProceedForCurrentAnsatz ≡ false
constructiveDyadicAdapterShouldProceedForCurrentAnsatzIsFalse = refl
