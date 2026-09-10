module DASHI.Physics.Closure.NSTriadKNSpectatorAmplitudeSelectedGramEnergyFrontierBidiExact where

------------------------------------------------------------------------
-- SPECTATOR AMPLITUDE: EXACT ENERGY MASS + SELECTED SIGNED GRAM INTERFERENCE
--
-- The preceding owners give:
--   * exact selected-coefficient R473 carrier for the R544 amplitude fold;
--   * pointwise spectator-weighted mixed-cell energy bound.
--
-- This file sums the pointwise mass bound with no fibre-cardinality factor and
-- uses R473's exact polarization ledger.  Therefore the only nontrivial
-- aggregation residual is an upper bound on the SELECTED signed Gram term for
-- the literal spectator coefficient sequence.  No arbitrary-coefficient
-- operator theorem is demanded.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorDoubleCellAmplitudeFoldRound544Exact as R544
import DASHI.Physics.Closure.NSTriadKNWeightedPhysicalGramOperatorCarrierRound473Exact as R473
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNSpectatorWeightedMixedAmplitudeCellEnergyBidiExact as Cell
import DASHI.Physics.Closure.NSTriadKNSpectatorAmplitudeToWeightedGramCarrierBidiExact as Gram

F : C3.RealField _
F = Rational.rationalRealField

module AmplitudeFrontier
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  system = Field30.finiteSystem physicalSystem
  velocity = Audit.velocity system

  module Spec = R541.Spectator physicalSystem S
  module Amp (beta : Physical.PhysicalTriadIncidence) =
    R544.Fold physicalSystem S (Spec.spectatorWeight beta)
  module G = Gram.SpectatorAmplitudeGram physicalSystem S
  module C = Cell.SpectatorWeightedAmplitudeCell
    physicalSystem S L velocityTransverse

  weightedEnergyMajorant :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence → ℚ
  weightedEnergyMajorant beta [] = 0ℚ
  weightedEnergyMajorant beta (alpha ∷ rest) =
    let w = Spec.Swap.pairResolvent alpha beta in
    (w * w)
      * (L2.complex3NormSquared (velocity (Physical.p alpha))
        * L2.complex3NormSquared (velocity (Physical.q alpha)))
    + weightedEnergyMajorant beta rest

  mappedAmplitudeMass :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence → ℚ
  mappedAmplitudeMass beta items =
    R180.cellMassSum (map (Amp.amplitude beta) items)

  mappedAmplitudeMassBelowWeightedEnergy :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    mappedAmplitudeMass beta items ≤ weightedEnergyMajorant beta items
  mappedAmplitudeMassBelowWeightedEnergy beta [] = ℚP.≤-refl
  mappedAmplitudeMassBelowWeightedEnergy beta (alpha ∷ rest) =
    ℚP.+-mono-≤
      (C.weightedMixedAmplitudeCellBelowEnergy beta alpha)
      (mappedAmplitudeMassBelowWeightedEnergy beta rest)

  selectedWeightedCellMassIsMappedAmplitudeMass :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R473.weightedCellMass
      (G.mixedCells items)
      (G.spectatorCoefficients beta items)
    ≡ mappedAmplitudeMass beta items
  selectedWeightedCellMassIsMappedAmplitudeMass beta items =
    cong R180.cellMassSum (G.weightedCellsAreAmplitudeCells beta items)

  selectedWeightedCellMassBelowEnergy :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R473.weightedCellMass
      (G.mixedCells items)
      (G.spectatorCoefficients beta items)
    ≤ weightedEnergyMajorant beta items
  selectedWeightedCellMassBelowEnergy beta items =
    subst
      (_≤ weightedEnergyMajorant beta items)
      (sym (selectedWeightedCellMassIsMappedAmplitudeMass beta items))
      (mappedAmplitudeMassBelowWeightedEnergy beta items)

  selectedSignedGram :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence → ℚ
  selectedSignedGram beta items =
    R473.weightedSignedGram
      (G.mixedCells items)
      (G.spectatorCoefficients beta items)

  amplitudeAggregateLedger :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    L2.complex3NormSquared (R224.foldVector (Amp.amplitude beta) items)
    ≡ R473.weightedCellMass
        (G.mixedCells items)
        (G.spectatorCoefficients beta items)
      + selectedSignedGram beta items
  amplitudeAggregateLedger beta items =
    trans
      (cong L2.complex3NormSquared
        (sym (G.selectedWeightedCellSumIsAmplitudeAggregate beta items)))
      (R473.weightedPhysicalGramLedger
        (G.mixedCells items)
        (G.spectatorCoefficients beta items))

------------------------------------------------------------------------
-- The only selected-amplitude aggregation theorem needed from here.
------------------------------------------------------------------------

record SelectedGramUpper
    (beta : Physical.PhysicalTriadIncidence)
    (items : List Physical.PhysicalTriadIncidence) : Set where
  constructor selected-gram-upper
  field
    gramCeiling : ℚ
    selectedGramBelowCeiling : selectedSignedGram beta items ≤ gramCeiling

open SelectedGramUpper public

selectedGramUpperBoundsAmplitude :
  (beta : Physical.PhysicalTriadIncidence) →
  (items : List Physical.PhysicalTriadIncidence) →
  (B : SelectedGramUpper beta items) →
  L2.complex3NormSquared (R224.foldVector (Amp.amplitude beta) items)
  ≤ weightedEnergyMajorant beta items + gramCeiling B
selectedGramUpperBoundsAmplitude beta items B =
  let
    massBound = selectedWeightedCellMassBelowEnergy beta items
    gramBound = selectedGramBelowCeiling B
    combined = ℚP.+-mono-≤ massBound gramBound
  in
  subst
    (λ lower → lower ≤ weightedEnergyMajorant beta items + gramCeiling B)
    (sym (amplitudeAggregateLedger beta items))
    combined

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

amplitudeCellMassEnergyBoundClosed : Bool
amplitudeCellMassEnergyBoundClosed = true

amplitudeSelectedWeightedGramCarrierClosed : Bool
amplitudeSelectedWeightedGramCarrierClosed = true

amplitudeArbitraryCoefficientOperatorTheoremMandatory : Bool
amplitudeArbitraryCoefficientOperatorTheoremMandatory = false

amplitudeSelectedGramUniformUpperClosed : Bool
amplitudeSelectedGramUniformUpperClosed = false

clayPromotion : Bool
clayPromotion = false
