module DASHI.Physics.Closure.NSTriadKNSpectatorAmplitudeToWeightedGramCarrierBidiExact where

------------------------------------------------------------------------
-- SPECTATOR AMPLITUDE -> R473 SELECTED-COEFFICIENT WEIGHTED GRAM CARRIER
--
-- Fix beta.  On a finite physical output fibre, take
--
--   cells        = [ mixedPlusMinus(alpha) ]
--   coefficients = [ 1 / (lambda_alpha + lambda_beta) ].
--
-- R541 identifies the corresponding R294 complex weight with realEmbed of
-- exactly that rational coefficient.  Therefore R473.weightedCells is exactly
-- the list of R544/R440 spectator-weighted amplitude cells, and its weighted
-- cell sum is exactly the amplitude aggregate.
--
-- This adds no operator bound.  It only moves the selected amplitude problem
-- onto the already-owned signed weighted-Gram ledger without asking for R473's
-- stronger arbitrary-coefficient operator theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorDoubleCellAmplitudeFoldRound544Exact as R544
import DASHI.Physics.Closure.NSTriadKNDoubleMixedPhysicalDampedTangentRound388Exact as R388
import DASHI.Physics.Closure.NSTriadKNWeightedPhysicalGramOperatorCarrierRound473Exact as R473
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224

F : C3.RealField _
F = Rational.rationalRealField

module SpectatorAmplitudeGram
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Spec = R541.Spectator physicalSystem S
  module D = R388.PhysicalDoubleMixed physicalSystem S
  module Amp (beta : Physical.PhysicalTriadIncidence) =
    R544.Fold physicalSystem S (Spec.spectatorWeight beta)

  mixedCells :
    List Physical.PhysicalTriadIncidence → List (C3.Complex3 F)
  mixedCells items = map D.Pair.mixedCell items

  spectatorCoefficients :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence → List ℚ
  spectatorCoefficients beta items =
    map (λ alpha → Spec.Swap.pairResolvent alpha beta) items

  weightedCellsAreAmplitudeCells :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R473.weightedCells
      (spectatorCoefficients beta items)
      (mixedCells items)
    ≡ map (Amp.amplitude beta) items
  weightedCellsAreAmplitudeCells beta [] = refl
  weightedCellsAreAmplitudeCells beta (alpha ∷ rest) =
    cong₂ _∷_
      (cong
        (λ selectedWeight →
          C3.complex3Scale selectedWeight (D.Pair.mixedCell alpha))
        (Spec.spectatorWeightMeaning beta alpha))
      (weightedCellsAreAmplitudeCells beta rest)

  sumCellsMapIsFoldVector :
    (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
    (items : List Physical.PhysicalTriadIncidence) →
    R180.sumCells (map value items) ≡ R224.foldVector value items
  sumCellsMapIsFoldVector value [] = refl
  sumCellsMapIsFoldVector value (alpha ∷ rest) =
    cong (C3.complex3Add (value alpha))
      (sumCellsMapIsFoldVector value rest)

  selectedWeightedCellSumIsAmplitudeAggregate :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R473.weightedCellSum
      (mixedCells items)
      (spectatorCoefficients beta items)
    ≡ R224.foldVector (Amp.amplitude beta) items
  selectedWeightedCellSumIsAmplitudeAggregate beta items =
    trans
      (cong R180.sumCells (weightedCellsAreAmplitudeCells beta items))
      (sumCellsMapIsFoldVector (Amp.amplitude beta) items)

spectatorAmplitudeSelectedWeightedGramCarrierClosed : Bool
spectatorAmplitudeSelectedWeightedGramCarrierClosed = true

spectatorAmplitudeArbitraryCoefficientOperatorBoundRequired : Bool
spectatorAmplitudeArbitraryCoefficientOperatorBoundRequired = false

spectatorAmplitudeSelectedGramUniformBoundClosed : Bool
spectatorAmplitudeSelectedGramUniformBoundClosed = false

clayPromotion : Bool
clayPromotion = false
