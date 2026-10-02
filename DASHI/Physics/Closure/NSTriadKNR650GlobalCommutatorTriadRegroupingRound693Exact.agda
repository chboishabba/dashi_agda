{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorTriadRegroupingRound693Exact where

------------------------------------------------------------------------
-- ROUND693 / GLOBAL COMMUTATOR OUTER INCIDENCE -> COMPLETE TRIAD REGROUPING
--
-- R692 expands the coherent commutator into same-output ordered pairs and
-- exposes the beta/spectator-row orientation.  This file removes the remaining
-- output-list bookkeeping on that OUTER incidence.
--
-- For beta in the output fibre F_k, its row can be written canonically using
-- F_{k(beta)}.  Therefore summing output rows over all k is exactly one fold
-- over the concatenated literal output fibres.  R39 identifies the full
-- cutoff concatenation with the complete duplicate-free physical triad
-- enumeration.
--
-- On that complete carrier, R38 already proves that
--
--   beta |-> pEnergyLeg beta,
--   beta |-> qEnergyLeg beta,
--   beta |-> swapTriad beta
--
-- are exact list permutations.  Hence the FULL outer-row sum may be reindexed
-- by each triad leg with no multiplicity or stabilizer assumption.
--
-- Important boundary: R690/R691 use NONZERO outputs.  The nonzero-output
-- concatenation is exposed exactly below, but cyclic closure of that selected
-- carrier is NOT asserted until zero-leg contributions are proved harmless.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; map)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNF4GlobalOutputFiberPartitionRound39Exact as R39
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFullSquareAsSpectatorRowsRound546Exact as R546
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorIncidenceExpansionRound692Exact as R692

F : C3.RealField _
F = Rational.rationalRealField

module Regrouping
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module E = R692.Expansion physicalSystem S

  globalOuterRow :
    Physical.PhysicalTriadIncidence → ℚ
  globalOuterRow beta =
    R546.spectatorRow
      E.commutatorPair beta
      (E.fibre (Physical.k beta))

  foldGlobalOuterRows :
    List Physical.PhysicalTriadIncidence → ℚ
  foldGlobalOuterRows =
    R38.foldPower globalOuterRow

  rowAtListedOutputIsGlobal :
    (output : Z3.FourierMode) →
    (beta : Physical.PhysicalTriadIncidence) →
    beta Cube.∈ E.fibre output →
    R546.spectatorRow E.commutatorPair beta (E.fibre output)
    ≡ globalOuterRow beta
  rowAtListedOutputIsGlobal output beta member =
    sym
      (cong
        (λ selected →
          R546.spectatorRow E.commutatorPair beta (E.fibre selected))
        (Output.physicalOutputFiberSound member))

  allRowsAtOutputAreGlobalFold :
    (output : Z3.FourierMode) →
    (items : List Physical.PhysicalTriadIncidence) →
    ((beta : Physical.PhysicalTriadIncidence) →
      beta Cube.∈ items → beta Cube.∈ E.fibre output) →
    R546.allSpectatorRows E.commutatorPair (E.fibre output) items
    ≡ foldGlobalOuterRows items
  allRowsAtOutputAreGlobalFold output [] included = refl
  allRowsAtOutputAreGlobalFold output (beta ∷ rest) included =
    cong₂ _+_
      (rowAtListedOutputIsGlobal
        output beta (included beta (Cube.here refl)))
      (allRowsAtOutputAreGlobalFold
        output rest
        (λ selected member → included selected (Cube.there member)))

  outputPairSumIsGlobalRowFold :
    (output : Z3.FourierMode) →
    E.outputPairIncidenceSum output
    ≡ foldGlobalOuterRows (E.fibre output)
  outputPairSumIsGlobalRowFold output =
    trans
      (E.outputPairIncidenceSumIsSpectatorRows output)
      (allRowsAtOutputAreGlobalFold
        output
        (E.fibre output)
        (λ beta member → member))

  sumOutputPairsIsConcatGlobalRows :
    (outputs : List Z3.FourierMode) →
    E.sumOutputPairIncidences outputs
    ≡ foldGlobalOuterRows
        (R39.concatOutputFibers E.cutoff outputs)
  sumOutputPairsIsConcatGlobalRows [] = refl
  sumOutputPairsIsConcatGlobalRows (output ∷ rest) =
    trans
      (cong₂ _+_
        (outputPairSumIsGlobalRowFold output)
        (sumOutputPairsIsConcatGlobalRows rest))
      (sym
        (R39.foldAppend
          globalOuterRow
          (E.fibre output)
          (R39.concatOutputFibers E.cutoff rest)))

  fullOutputPairSumIsCompletePhysicalOuterRows :
    E.sumOutputPairIncidences (Cube.cutoffModes E.cutoff)
    ≡ foldGlobalOuterRows
        (Physical.physicalTriadEnumeration E.cutoff)
  fullOutputPairSumIsCompletePhysicalOuterRows =
    trans
      (sumOutputPairsIsConcatGlobalRows
        (Cube.cutoffModes E.cutoff))
      (R38.foldPermutationInvariant
        globalOuterRow
        (R39.literalOutputPartitionPermutation E.cutoff))

  nonzeroOutputPairSumIsSelectedPhysicalOuterRows :
    E.nonzeroGlobalPairIncidenceSum
    ≡ foldGlobalOuterRows
        (R39.concatOutputFibers
          E.cutoff (Canonical.nonzeroCutoffModes E.cutoff))
  nonzeroOutputPairSumIsSelectedPhysicalOuterRows =
    sumOutputPairsIsConcatGlobalRows
      (Canonical.nonzeroCutoffModes E.cutoff)

  fullOuterRowsPEnergyRegroup :
    foldGlobalOuterRows (Physical.physicalTriadEnumeration E.cutoff)
    ≡
    R38.foldPower
      (λ beta → globalOuterRow (Orbit.pEnergyLeg beta))
      (Physical.physicalTriadEnumeration E.cutoff)
  fullOuterRowsPEnergyRegroup =
    trans
      (sym
        (R38.foldPermutationInvariant
          globalOuterRow
          (R38.pEnergyLegEnumerationPermutation E.cutoff)))
      (R38.foldMap
        globalOuterRow Orbit.pEnergyLeg
        (Physical.physicalTriadEnumeration E.cutoff))

  fullOuterRowsQEnergyRegroup :
    foldGlobalOuterRows (Physical.physicalTriadEnumeration E.cutoff)
    ≡
    R38.foldPower
      (λ beta → globalOuterRow (Orbit.qEnergyLeg beta))
      (Physical.physicalTriadEnumeration E.cutoff)
  fullOuterRowsQEnergyRegroup =
    trans
      (sym
        (R38.foldPermutationInvariant
          globalOuterRow
          (R38.qEnergyLegEnumerationPermutation E.cutoff)))
      (R38.foldMap
        globalOuterRow Orbit.qEnergyLeg
        (Physical.physicalTriadEnumeration E.cutoff))

  fullOuterRowsSwapRegroup :
    foldGlobalOuterRows (Physical.physicalTriadEnumeration E.cutoff)
    ≡
    R38.foldPower
      (λ beta → globalOuterRow (Symmetry.swapTriad beta))
      (Physical.physicalTriadEnumeration E.cutoff)
  fullOuterRowsSwapRegroup =
    trans
      (sym
        (R38.foldPermutationInvariant
          globalOuterRow
          (R38.swapTriadEnumerationPermutation E.cutoff)))
      (R38.foldMap
        globalOuterRow Symmetry.swapTriad
        (Physical.physicalTriadEnumeration E.cutoff))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round693OuterRowsFlattenToLiteralOutputPartition : Bool
round693OuterRowsFlattenToLiteralOutputPartition = true

round693FullOutputRowsRouteToCompletePhysicalEnumeration : Bool
round693FullOutputRowsRouteToCompletePhysicalEnumeration = true

round693FullCarrierPEnergyLegPermutationAvailable : Bool
round693FullCarrierPEnergyLegPermutationAvailable = true

round693FullCarrierQEnergyLegPermutationAvailable : Bool
round693FullCarrierQEnergyLegPermutationAvailable = true

round693FullCarrierSwapPermutationAvailable : Bool
round693FullCarrierSwapPermutationAvailable = true

round693NonzeroSelectedCarrierCyclicClosureProved : Bool
round693NonzeroSelectedCarrierCyclicClosureProved = false

round693ZeroLegContributionEliminated : Bool
round693ZeroLegContributionEliminated = false

round693NestedProjectedForcingTriadOrbitExpanded : Bool
round693NestedProjectedForcingTriadOrbitExpanded = false

round693OrbitContributionCancellationClosed : Bool
round693OrbitContributionCancellationClosed = false

round693IntroducesEstimate : Bool
round693IntroducesEstimate = false

round693ClayPromotion : Bool
round693ClayPromotion = false

round693OuterRowsFlattenToLiteralOutputPartitionIsTrue :
  round693OuterRowsFlattenToLiteralOutputPartition ≡ true
round693OuterRowsFlattenToLiteralOutputPartitionIsTrue = refl

round693FullOutputRowsRouteToCompletePhysicalEnumerationIsTrue :
  round693FullOutputRowsRouteToCompletePhysicalEnumeration ≡ true
round693FullOutputRowsRouteToCompletePhysicalEnumerationIsTrue = refl

round693FullCarrierPEnergyLegPermutationAvailableIsTrue :
  round693FullCarrierPEnergyLegPermutationAvailable ≡ true
round693FullCarrierPEnergyLegPermutationAvailableIsTrue = refl

round693FullCarrierQEnergyLegPermutationAvailableIsTrue :
  round693FullCarrierQEnergyLegPermutationAvailable ≡ true
round693FullCarrierQEnergyLegPermutationAvailableIsTrue = refl

round693FullCarrierSwapPermutationAvailableIsTrue :
  round693FullCarrierSwapPermutationAvailable ≡ true
round693FullCarrierSwapPermutationAvailableIsTrue = refl

round693NonzeroSelectedCarrierCyclicClosureProvedIsFalse :
  round693NonzeroSelectedCarrierCyclicClosureProved ≡ false
round693NonzeroSelectedCarrierCyclicClosureProvedIsFalse = refl

round693ZeroLegContributionEliminatedIsFalse :
  round693ZeroLegContributionEliminated ≡ false
round693ZeroLegContributionEliminatedIsFalse = refl

round693NestedProjectedForcingTriadOrbitExpandedIsFalse :
  round693NestedProjectedForcingTriadOrbitExpanded ≡ false
round693NestedProjectedForcingTriadOrbitExpandedIsFalse = refl

round693OrbitContributionCancellationClosedIsFalse :
  round693OrbitContributionCancellationClosed ≡ false
round693OrbitContributionCancellationClosedIsFalse = refl

round693IntroducesEstimateIsFalse :
  round693IntroducesEstimate ≡ false
round693IntroducesEstimateIsFalse = refl

round693ClayPromotionIsFalse :
  round693ClayPromotion ≡ false
round693ClayPromotionIsFalse = refl
