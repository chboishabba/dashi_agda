module DASHI.Physics.Closure.NSTriadKNSelectedPacketProjectedPairingRound98Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- ROUND98 / SELECTED F4 SAME-OBJECT IDENTIFICATION
--
-- Round39 proves that the actual projected Galerkin convection-energy pairing
-- is the raw ordered-incidence fold. Round96 instead packages packet transfer
-- by summing all three energy legs, with each leg using the symmetrized
-- ordered-pair power. The complete physical enumeration therefore carries the
-- same factor six as Round38's unweighted theorem.
--
-- This module proves the selected/packet analogue exactly:
--
--   selected projected pairing
--     = weighted ordered-incidence fold
--     = (1/6) * Round96.sumPacketTransfer
--     = (1/6) * Round96.sumBoundaryTransfer.
--
-- The last equality uses Round96's exact internal-triad cancellation and hence
-- requires only the already-native reality/divergence-free hypotheses.
--
-- This closes the nonlinear same-object/normalization part of
-- PhysicalPacketBoundaryFluxLogReserveIdentification. It does NOT invent an
-- extra forcing receipt: the remaining linear packet-energy PDE step is only
-- the selected pairing of the already-existing projected ODE with u_k and the
-- literal viscous energy term.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; map)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Equation
import DASHI.Physics.Closure.NSTriadKNPhysicalPacketBoundaryFluxRound96Exact as Round96
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as Round38
import DASHI.Physics.Closure.NSTriadKNF4ProjectedOutputPairingRound39Exact as OutputPairing
import DASHI.Physics.Closure.NSTriadKNF4GlobalOutputFiberPartitionRound39Exact as Round39
import DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxNormalizationRound98Exact as Norm

F : C3.RealField _
F = Rational.rationalRealField

weightedOrderedPower :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → ℚ
weightedOrderedPower E I selected velocity tau =
  Round96.selectTransfer (selected (Physical.k tau))
    (Round38.orderedPower E I tau velocity)

weightedPairPower :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → ℚ
weightedPairPower E I selected velocity tau =
  Round96.selectTransfer (selected (Physical.k tau))
    (Round38.orderedPairPower E I tau velocity)

weightedSwapPower :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → ℚ
weightedSwapPower E I selected velocity tau =
  Round96.selectTransfer (selected (Physical.k tau))
    (Round38.orderedPower E I (Symmetry.swapTriad tau) velocity)

weightedFold :
  (Physical.PhysicalTriadIncidence → ℚ) →
  List Physical.PhysicalTriadIncidence → ℚ
weightedFold = Round38.foldPower

weightedOrderedFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
weightedOrderedFold E I selected velocity =
  weightedFold (weightedOrderedPower E I selected velocity)

weightedPairFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
weightedPairFold E I selected velocity =
  weightedFold (weightedPairPower E I selected velocity)

weightedSwapFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
weightedSwapFold E I selected velocity =
  weightedFold (weightedSwapPower E I selected velocity)

selectTransferAdd : ∀ selected a b →
  Round96.selectTransfer selected (a + b)
  ≡ Round96.selectTransfer selected a + Round96.selectTransfer selected b
selectTransferAdd true a b = refl
selectTransferAdd false a b = refl

weightedPairPowerDecomposition :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau : Physical.PhysicalTriadIncidence) →
  weightedPairPower E I selected velocity tau
  ≡ weightedOrderedPower E I selected velocity tau
    + weightedSwapPower E I selected velocity tau
weightedPairPowerDecomposition E I selected velocity tau =
  trans
    (cong
      (Round96.selectTransfer (selected (Physical.k tau)))
      (Round38.orderedPairPowerIsOrderedPlusSwap E I tau velocity))
    (selectTransferAdd
      (selected (Physical.k tau))
      (Round38.orderedPower E I tau velocity)
      (Round38.orderedPower E I (Symmetry.swapTriad tau) velocity))

weightedPairFoldDecomposition :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  weightedPairFold E I selected velocity items
  ≡ weightedOrderedFold E I selected velocity items
    + weightedSwapFold E I selected velocity items
weightedPairFoldDecomposition E I selected velocity [] = solve []
weightedPairFoldDecomposition E I selected velocity (tau ∷ rest) =
  trans
    (cong
      (_+ weightedPairFold E I selected velocity rest)
      (weightedPairPowerDecomposition E I selected velocity tau))
    (trans
      (cong
        (λ tail →
          (weightedOrderedPower E I selected velocity tau
            + weightedSwapPower E I selected velocity tau) + tail)
        (weightedPairFoldDecomposition E I selected velocity rest))
      (solve
        ( weightedOrderedPower E I selected velocity tau
        ∷ weightedSwapPower E I selected velocity tau
        ∷ weightedOrderedFold E I selected velocity rest
        ∷ weightedSwapFold E I selected velocity rest
        ∷ [])))

weightedSwapFoldInvariant :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  weightedSwapFold E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
  ≡ weightedOrderedFold E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
weightedSwapFoldInvariant E I selected velocity cutoff =
  trans
    (sym
      (Round38.foldMap
        (weightedOrderedPower E I selected velocity)
        Symmetry.swapTriad
        (Physical.physicalTriadEnumeration cutoff)))
    (Round38.foldPermutationInvariant
      (weightedOrderedPower E I selected velocity)
      (Round38.swapTriadEnumerationPermutation cutoff))

weightedPairFoldIsDoubleOrdered :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  weightedPairFold E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
  ≡ weightedOrderedFold E I selected velocity
      (Physical.physicalTriadEnumeration cutoff)
    + weightedOrderedFold E I selected velocity
      (Physical.physicalTriadEnumeration cutoff)
weightedPairFoldIsDoubleOrdered E I selected velocity cutoff =
  trans
    (weightedPairFoldDecomposition E I selected velocity
      (Physical.physicalTriadEnumeration cutoff))
    (cong
      (weightedOrderedFold E I selected velocity
        (Physical.physicalTriadEnumeration cutoff) +_)
      (weightedSwapFoldInvariant E I selected velocity cutoff))

weightedPEnergyFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
weightedPEnergyFold E I selected velocity =
  weightedFold
    (λ tau →
      Round96.selectTransfer (selected (Physical.p tau))
        (Round38.orderedPairPower E I (Orbit.pEnergyLeg tau) velocity))

weightedQEnergyFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
weightedQEnergyFold E I selected velocity =
  weightedFold
    (λ tau →
      Round96.selectTransfer (selected (Physical.q tau))
        (Round38.orderedPairPower E I (Orbit.qEnergyLeg tau) velocity))

weightedPEnergyFoldInvariant :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  weightedPEnergyFold E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
  ≡ weightedPairFold E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
weightedPEnergyFoldInvariant E I selected velocity cutoff =
  trans
    (sym
      (Round38.foldMap
        (weightedPairPower E I selected velocity)
        Orbit.pEnergyLeg
        (Physical.physicalTriadEnumeration cutoff)))
    (Round38.foldPermutationInvariant
      (weightedPairPower E I selected velocity)
      (Round38.pEnergyLegEnumerationPermutation cutoff))

weightedQEnergyFoldInvariant :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  weightedQEnergyFold E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
  ≡ weightedPairFold E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
weightedQEnergyFoldInvariant E I selected velocity cutoff =
  trans
    (sym
      (Round38.foldMap
        (weightedPairPower E I selected velocity)
        Orbit.qEnergyLeg
        (Physical.physicalTriadEnumeration cutoff)))
    (Round38.foldPermutationInvariant
      (weightedPairPower E I selected velocity)
      (Round38.qEnergyLegEnumerationPermutation cutoff))

packetTransferThreeFoldDecomposition :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  Round96.sumPacketTransfer E I selected velocity items
  ≡ weightedPairFold E I selected velocity items
    + weightedPEnergyFold E I selected velocity items
    + weightedQEnergyFold E I selected velocity items
packetTransferThreeFoldDecomposition E I selected velocity [] = solve []
packetTransferThreeFoldDecomposition E I selected velocity (tau ∷ rest) =
  trans
    (cong
      (Round96.packetTriadTransfer E I selected velocity tau +_)
      (packetTransferThreeFoldDecomposition E I selected velocity rest))
    (solve
      ( weightedPairPower E I selected velocity tau
      ∷ Round96.selectTransfer (selected (Physical.p tau))
          (Round38.orderedPairPower E I (Orbit.pEnergyLeg tau) velocity)
      ∷ Round96.selectTransfer (selected (Physical.q tau))
          (Round38.orderedPairPower E I (Orbit.qEnergyLeg tau) velocity)
      ∷ weightedPairFold E I selected velocity rest
      ∷ weightedPEnergyFold E I selected velocity rest
      ∷ weightedQEnergyFold E I selected velocity rest
      ∷ []))

sumPacketTransferIsSixWeightedOrderedFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  Round96.sumPacketTransfer E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
  ≡ Round38.sixFold
      (weightedOrderedFold E I selected velocity
        (Physical.physicalTriadEnumeration cutoff))
sumPacketTransferIsSixWeightedOrderedFold E I selected velocity cutoff =
  let
    enumeration = Physical.physicalTriadEnumeration cutoff
    pairTotal = weightedPairFold E I selected velocity enumeration
    orderedTotal = weightedOrderedFold E I selected velocity enumeration
  in
  trans
    (packetTransferThreeFoldDecomposition E I selected velocity enumeration)
    (trans
      (cong₂
        (λ p q → pairTotal + p + q)
        (weightedPEnergyFoldInvariant E I selected velocity cutoff)
        (weightedQEnergyFoldInvariant E I selected velocity cutoff))
      (trans
        (cong
          (λ p → p + pairTotal + pairTotal)
          (weightedPairFoldIsDoubleOrdered E I selected velocity cutoff))
        (solve (orderedTotal ∷ []))))

normalizedPacketTransferIsWeightedOrderedFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  Norm.normalizedPacketTransfer E I selected velocity cutoff
  ≡ weightedOrderedFold E I selected velocity
      (Physical.physicalTriadEnumeration cutoff)
normalizedPacketTransferIsWeightedOrderedFold E I selected velocity cutoff =
  let
    total = weightedOrderedFold E I selected velocity
      (Physical.physicalTriadEnumeration cutoff)
  in
  trans
    (cong (Norm.oneSixth *_)
      (sumPacketTransferIsSixWeightedOrderedFold
        E I selected velocity cutoff))
    (solve (total ∷ []))

------------------------------------------------------------------------
-- Selected projected output pairing = weighted ordered fold.
------------------------------------------------------------------------

selectedProjectedOutputPower :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  (Z3.FourierMode → Bool) →
  Z3.FourierMode → ℚ
selectedProjectedOutputPower system selected output =
  Round96.selectTransfer (selected output)
    (OutputPairing.realHermitianPower
      (Equation.velocity system output)
      (Equation.projectedNonlinearity system output))

sumSelectedProjectedPairings :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  (Z3.FourierMode → Bool) →
  List Z3.FourierMode → ℚ
sumSelectedProjectedPairings system selected [] = 0ℚ
sumSelectedProjectedPairings system selected (output ∷ rest) =
  selectedProjectedOutputPower system selected output
  + sumSelectedProjectedPairings system selected rest

literalSelectedProjectedPairing :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  (Z3.FourierMode → Bool) → ℚ
literalSelectedProjectedPairing system selected =
  sumSelectedProjectedPairings system selected
    (Cube.cutoffModes (Equation.cutoff system))

weightedFoldAppend :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  ∀ left right →
  weightedFold value (Cube._++_ left right)
  ≡ weightedFold value left + weightedFold value right
weightedFoldAppend value [] right = refl
weightedFoldAppend value (tau ∷ rest) right =
  trans
    (cong (value tau +_) (weightedFoldAppend value rest right))
    (solve
      ( value tau
      ∷ weightedFold value rest
      ∷ weightedFold value right
      ∷ []))

fiberWeightedFoldTrue :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) →
  (output : Z3.FourierMode) →
  selected output ≡ true →
  weightedOrderedFold E I selected (Equation.velocity system)
    (Equation.concreteTriadsAt system output)
  ≡ Round38.foldPower
      (λ tau → Round38.orderedPower E I tau (Equation.velocity system))
      (Equation.concreteTriadsAt system output)
fiberWeightedFoldTrue {E} {I} system selected output outputTrue =
  go
    (Equation.concreteTriadsAt system output)
    (λ tau member → Equation.concreteTriadsAtOutputAgreement member)
  where
  go :
    (items : List Physical.PhysicalTriadIncidence) →
    (∀ tau → Cube._∈_ tau items → Physical.k tau ≡ output) →
    weightedOrderedFold E I selected (Equation.velocity system) items
    ≡ Round38.foldPower
        (λ tau → Round38.orderedPower E I tau (Equation.velocity system)) items
  go [] pointwise = refl
  go (tau ∷ rest) pointwise
    rewrite pointwise tau (Cube.here refl) | outputTrue =
    cong
      (Round38.orderedPower E I tau (Equation.velocity system) +_)
      (go rest (λ chosen member → pointwise chosen (Cube.there member)))

fiberWeightedFoldFalse :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) →
  (output : Z3.FourierMode) →
  selected output ≡ false →
  weightedOrderedFold E I selected (Equation.velocity system)
    (Equation.concreteTriadsAt system output)
  ≡ 0ℚ
fiberWeightedFoldFalse {E} {I} system selected output outputFalse =
  go
    (Equation.concreteTriadsAt system output)
    (λ tau member → Equation.concreteTriadsAtOutputAgreement member)
  where
  go :
    (items : List Physical.PhysicalTriadIncidence) →
    (∀ tau → Cube._∈_ tau items → Physical.k tau ≡ output) →
    weightedOrderedFold E I selected (Equation.velocity system) items ≡ 0ℚ
  go [] pointwise = refl
  go (tau ∷ rest) pointwise
    rewrite pointwise tau (Cube.here refl) | outputFalse =
    go rest (λ chosen member → pointwise chosen (Cube.there member))

selectedOutputPairingEqualsWeightedFiberFold :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) →
  (output : Z3.FourierMode) →
  selectedProjectedOutputPower system selected output
  ≡ weightedOrderedFold E I selected (Equation.velocity system)
      (Equation.concreteTriadsAt system output)
selectedOutputPairingEqualsWeightedFiberFold {E} {I}
    system selected output with selected output
... | true =
  trans
    (OutputPairing.projectedOutputEnergyPairingEqualsOrderedFiberFold
      system output)
    (sym (fiberWeightedFoldTrue system selected output refl))
... | false =
  sym (fiberWeightedFoldFalse system selected output refl)

sumSelectedProjectedPairingsEqualsConcatWeightedFold :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) →
  (outputs : List Z3.FourierMode) →
  sumSelectedProjectedPairings system selected outputs
  ≡ weightedOrderedFold E I selected (Equation.velocity system)
      (Round39.concatOutputFibers (Equation.cutoff system) outputs)
sumSelectedProjectedPairingsEqualsConcatWeightedFold system selected [] = refl
sumSelectedProjectedPairingsEqualsConcatWeightedFold {E} {I}
    system selected (output ∷ rest) =
  trans
    (cong₂ _+_
      (selectedOutputPairingEqualsWeightedFiberFold system selected output)
      (sumSelectedProjectedPairingsEqualsConcatWeightedFold
        system selected rest))
    (sym
      (weightedFoldAppend
        (weightedOrderedPower E I selected (Equation.velocity system))
        (Equation.concreteTriadsAt system output)
        (Round39.concatOutputFibers (Equation.cutoff system) rest)))

literalSelectedProjectedPairingEqualsWeightedOrderedFold :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) →
  literalSelectedProjectedPairing system selected
  ≡ weightedOrderedFold E I selected (Equation.velocity system)
      (Physical.physicalTriadEnumeration (Equation.cutoff system))
literalSelectedProjectedPairingEqualsWeightedOrderedFold {E} {I}
    system selected =
  trans
    (sumSelectedProjectedPairingsEqualsConcatWeightedFold
      system selected (Cube.cutoffModes (Equation.cutoff system)))
    (Round38.foldPermutationInvariant
      (weightedOrderedPower E I selected (Equation.velocity system))
      (Round39.literalOutputPartitionPermutation (Equation.cutoff system)))

literalSelectedProjectedPairingIsNormalizedPacketTransfer :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) →
  literalSelectedProjectedPairing system selected
  ≡ Norm.normalizedPacketTransfer E I selected
      (Equation.velocity system) (Equation.cutoff system)
literalSelectedProjectedPairingIsNormalizedPacketTransfer {E} {I}
    system selected =
  trans
    (literalSelectedProjectedPairingEqualsWeightedOrderedFold system selected)
    (sym
      (normalizedPacketTransferIsWeightedOrderedFold
        E I selected (Equation.velocity system) (Equation.cutoff system)))

literalSelectedProjectedPairingIsNormalizedBoundaryFlux :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) →
  Audit.RealityCondition (Equation.velocity system) →
  Audit.DivergenceFreeCondition E (Equation.velocity system) →
  literalSelectedProjectedPairing system selected
  ≡ Norm.normalizedBoundaryTransfer E I selected
      (Equation.velocity system) (Equation.cutoff system)
literalSelectedProjectedPairingIsNormalizedBoundaryFlux {E} {I}
    system selected reality divergenceFree =
  trans
    (literalSelectedProjectedPairingIsNormalizedPacketTransfer system selected)
    (Norm.normalizedLiteralPacketTransferIsBoundaryFlux
      E I selected (Equation.velocity system)
      reality divergenceFree (Equation.cutoff system))

round98SelectedWeightedOutputFiberIdentificationClosed : Bool
round98SelectedWeightedOutputFiberIdentificationClosed = true

round98SelectedProjectedPairingIsNormalizedBoundaryFlux : Bool
round98SelectedProjectedPairingIsNormalizedBoundaryFlux = true

round98SelectedWeightedOutputFiberIdentificationClosedIsTrue :
  round98SelectedWeightedOutputFiberIdentificationClosed ≡ true
round98SelectedWeightedOutputFiberIdentificationClosedIsTrue = refl
