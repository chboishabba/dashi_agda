module DASHI.Physics.YangMills.BalabanWilsonRGCoefficientCombinatoricsExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanDyadicQuantitativeRegionExact
import DASHI.Physics.YangMills.BalabanConcreteFiniteBackgroundCutset as Cutset

------------------------------------------------------------------------
-- Exact four-dimensional combinatorial normalization of the candidate
-- coefficients.
--
-- These equalities remove the five candidate pairs as opaque numerals: each is
-- expressed through the literal dimension, the two orientations of each link,
-- and the 2^4 vertices of the Boolean four-cell.  This is only the counting and
-- normalization layer.  The remaining analytic task is to prove that each
-- differentiated Wilson/RG operator is bounded by its corresponding majorant.
------------------------------------------------------------------------

latticeDimension : Nat
latticeDimension = 4

signedLinkDirections : Nat
signedLinkDirections = latticeDimension + latticeDimension

booleanCellCardinality : Nat
booleanCellCardinality = pow2 latticeDimension

curvatureIncidenceMajorant : QuadraticMajorant
curvatureIncidenceMajorant =
  quadraticMajorant
    (signedLinkDirections * signedLinkDirections)
    (signedLinkDirections * signedLinkDirections)

transportIncidenceMajorant : QuadraticMajorant
transportIncidenceMajorant =
  quadraticMajorant signedLinkDirections latticeDimension

chartIncidenceMajorant : QuadraticMajorant
chartIncidenceMajorant =
  quadraticMajorant
    booleanCellCardinality
    (signedLinkDirections * latticeDimension)

gaugeFixingIncidenceMajorant : QuadraticMajorant
gaugeFixingIncidenceMajorant =
  quadraticMajorant
    (signedLinkDirections * latticeDimension)
    (signedLinkDirections * signedLinkDirections)

blockConstraintIncidenceMajorant : QuadraticMajorant
blockConstraintIncidenceMajorant =
  quadraticMajorant
    booleanCellCardinality
    (signedLinkDirections * signedLinkDirections)

curvatureCandidateFromIncidence :
  curvatureIncidenceMajorant ≡ curvatureCandidate
curvatureCandidateFromIncidence = refl

transportCandidateFromIncidence :
  transportIncidenceMajorant ≡ transportCandidate
transportCandidateFromIncidence = refl

chartCandidateFromIncidence :
  chartIncidenceMajorant ≡ chartCandidate
chartCandidateFromIncidence = refl

gaugeFixingCandidateFromIncidence :
  gaugeFixingIncidenceMajorant ≡ gaugeFixingCandidate
gaugeFixingCandidateFromIncidence = refl

blockConstraintCandidateFromIncidence :
  blockConstraintIncidenceMajorant ≡ blockConstraintCandidate
blockConstraintCandidateFromIncidence = refl

derivedFiveComponentMajorant : QuadraticMajorant
derivedFiveComponentMajorant =
  sumMajorants
    (curvatureIncidenceMajorant
    ∷ transportIncidenceMajorant
    ∷ chartIncidenceMajorant
    ∷ gaugeFixingIncidenceMajorant
    ∷ blockConstraintIncidenceMajorant
    ∷ [])

derivedFiveComponentMatchesCandidate :
  derivedFiveComponentMajorant ≡ fiveComponentCandidate
derivedFiveComponentMatchesCandidate = refl

------------------------------------------------------------------------
-- Literal operator carrier matching.
--
-- Unlike an untyped list of five assumptions, this record is indexed by the
-- repository's actual ConcreteHessianDifference owner.  Every coefficient and
-- every analytic estimate is therefore attached to the corresponding literal
-- curvature/transport/chart/gauge/block component on the same index and state.
------------------------------------------------------------------------

record LiteralWilsonRGOperatorCoefficientMatch
    (Index State Operator : Set)
    (hessian : Cutset.ConcreteHessianDifference Index State Operator) : Set₁ where
  field
    operatorMajorant : Operator → QuadraticMajorant
    MagnitudeBelow : Operator → QuadraticMajorant → Set

    curvatureMajorantMatches : ∀ index state →
      operatorMajorant (Cutset.curvatureDifference hessian index state)
      ≡ curvatureIncidenceMajorant
    transportMajorantMatches : ∀ index state →
      operatorMajorant (Cutset.transportDifference hessian index state)
      ≡ transportIncidenceMajorant
    chartMajorantMatches : ∀ index state →
      operatorMajorant (Cutset.chartDifference hessian index state)
      ≡ chartIncidenceMajorant
    gaugeFixingMajorantMatches : ∀ index state →
      operatorMajorant (Cutset.gaugeFixingDifference hessian index state)
      ≡ gaugeFixingIncidenceMajorant
    blockConstraintMajorantMatches : ∀ index state →
      operatorMajorant (Cutset.blockConstraintDifference hessian index state)
      ≡ blockConstraintIncidenceMajorant

    curvatureOperatorEstimate : ∀ index state →
      MagnitudeBelow
        (Cutset.curvatureDifference hessian index state)
        curvatureIncidenceMajorant
    transportOperatorEstimate : ∀ index state →
      MagnitudeBelow
        (Cutset.transportDifference hessian index state)
        transportIncidenceMajorant
    chartOperatorEstimate : ∀ index state →
      MagnitudeBelow
        (Cutset.chartDifference hessian index state)
        chartIncidenceMajorant
    gaugeFixingOperatorEstimate : ∀ index state →
      MagnitudeBelow
        (Cutset.gaugeFixingDifference hessian index state)
        gaugeFixingIncidenceMajorant
    blockConstraintOperatorEstimate : ∀ index state →
      MagnitudeBelow
        (Cutset.blockConstraintDifference hessian index state)
        blockConstraintIncidenceMajorant

open LiteralWilsonRGOperatorCoefficientMatch public

wilsonRGIncidenceArithmeticLevel : ProofLevel
wilsonRGIncidenceArithmeticLevel = computed

literalWilsonRGOperatorCarrierMatchingLevel : ProofLevel
literalWilsonRGOperatorCarrierMatchingLevel = machineChecked

literalWilsonRGOperatorEstimateLevel : ProofLevel
literalWilsonRGOperatorEstimateLevel = conditional
