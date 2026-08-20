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
-- The actual projected Galerkin convection-energy pairing is the raw ordered
-- physical-incidence fold (Round39). Round96 instead records each physical
-- incidence through all three energy legs and uses ordered-pair power. The
-- selected analogue of Round38 therefore has the same exact factor six:
--
--   Round96.sumPacketTransfer = 6 * selectedOrderedFold.
--
-- Consequently the literal selected projected pairing is exactly
--
--   (1/6) * Round96.sumPacketTransfer
--   = (1/6) * Round96.sumBoundaryTransfer.
--
-- The latter equality is Round96's exact internal/all-external cancellation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
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

selectedOrderedPower :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → ℚ
selectedOrderedPower E I selected velocity tau =
  Round96.selectTransfer (selected (Physical.k tau))
    (Round38.orderedPower E I tau velocity)

selectedPairPower :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → ℚ
selectedPairPower E I selected velocity tau =
  Round96.selectTransfer (selected (Physical.k tau))
    (Round38.orderedPairPower E I tau velocity)

selectedOrderedFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
selectedOrderedFold E I selected velocity =
  Round38.foldPower (selectedOrderedPower E I selected velocity)

selectedPairFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
selectedPairFold E I selected velocity =
  Round38.foldPower (selectedPairPower E I selected velocity)

selectAdd : ∀ b x y →
  Round96.selectTransfer b (x + y)
  ≡ Round96.selectTransfer b x + Round96.selectTransfer b y
selectAdd true x y = refl
selectAdd false x y = refl

selectedPairPointwise :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (tau : Physical.PhysicalTriadIncidence) →
  selectedPairPower E I selected velocity tau
  ≡ selectedOrderedPower E I selected velocity tau
    + selectedOrderedPower E I selected velocity (Symmetry.swapTriad tau)
selectedPairPointwise E I selected velocity tau =
  trans
    (cong
      (Round96.selectTransfer (selected (Physical.k tau)))
      (Round38.orderedPairPowerIsOrderedPlusSwap E I tau velocity))
    (selectAdd
      (selected (Physical.k tau))
      (Round38.orderedPower E I tau velocity)
      (Round38.orderedPower E I (Symmetry.swapTriad tau) velocity))

selectedPairFoldSplit :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  selectedPairFold E I selected velocity items
  ≡ selectedOrderedFold E I selected velocity items
    + Round38.foldPower
      (λ tau → selectedOrderedPower E I selected velocity
        (Symmetry.swapTriad tau)) items
selectedPairFoldSplit E I selected velocity [] = solve []
selectedPairFoldSplit E I selected velocity (tau ∷ rest) =
  trans
    (cong
      (_+ selectedPairFold E I selected velocity rest)
      (selectedPairPointwise E I selected velocity tau))
    (trans
      (cong
        (λ tail →
          (selectedOrderedPower E I selected velocity tau
            + selectedOrderedPower E I selected velocity
              (Symmetry.swapTriad tau)) + tail)
        (selectedPairFoldSplit E I selected velocity rest))
      (solve
        ( selectedOrderedPower E I selected velocity tau
        ∷ selectedOrderedPower E I selected velocity (Symmetry.swapTriad tau)
        ∷ selectedOrderedFold E I selected velocity rest
        ∷ Round38.foldPower
            (λ t → selectedOrderedPower E I selected velocity
              (Symmetry.swapTriad t)) rest
        ∷ [])))

selectedPairFoldIsDoubleOrdered :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  selectedPairFold E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
  ≡ selectedOrderedFold E I selected velocity
      (Physical.physicalTriadEnumeration cutoff)
    + selectedOrderedFold E I selected velocity
      (Physical.physicalTriadEnumeration cutoff)
selectedPairFoldIsDoubleOrdered E I selected velocity cutoff =
  trans
    (selectedPairFoldSplit E I selected velocity
      (Physical.physicalTriadEnumeration cutoff))
    (cong
      (selectedOrderedFold E I selected velocity
        (Physical.physicalTriadEnumeration cutoff) +_)
      (trans
        (sym
          (Round38.foldMap
            (selectedOrderedPower E I selected velocity)
            Symmetry.swapTriad
            (Physical.physicalTriadEnumeration cutoff)))
        (Round38.foldPermutationInvariant
          (selectedOrderedPower E I selected velocity)
          (Round38.swapTriadEnumerationPermutation cutoff))))

pEnergySelectedPairFold qEnergySelectedPairFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
pEnergySelectedPairFold E I selected velocity =
  Round38.foldPower
    (λ tau → Round96.selectTransfer (selected (Physical.p tau))
      (Round38.orderedPairPower E I (Orbit.pEnergyLeg tau) velocity))
qEnergySelectedPairFold E I selected velocity =
  Round38.foldPower
    (λ tau → Round96.selectTransfer (selected (Physical.q tau))
      (Round38.orderedPairPower E I (Orbit.qEnergyLeg tau) velocity))

pEnergySelectedPairInvariant :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  pEnergySelectedPairFold E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
  ≡ selectedPairFold E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
pEnergySelectedPairInvariant E I selected velocity cutoff =
  trans
    (sym
      (Round38.foldMap
        (selectedPairPower E I selected velocity)
        Orbit.pEnergyLeg
        (Physical.physicalTriadEnumeration cutoff)))
    (Round38.foldPermutationInvariant
      (selectedPairPower E I selected velocity)
      (Round38.pEnergyLegEnumerationPermutation cutoff))

qEnergySelectedPairInvariant :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  qEnergySelectedPairFold E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
  ≡ selectedPairFold E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
qEnergySelectedPairInvariant E I selected velocity cutoff =
  trans
    (sym
      (Round38.foldMap
        (selectedPairPower E I selected velocity)
        Orbit.qEnergyLeg
        (Physical.physicalTriadEnumeration cutoff)))
    (Round38.foldPermutationInvariant
      (selectedPairPower E I selected velocity)
      (Round38.qEnergyLegEnumerationPermutation cutoff))

packetTransferSplit :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  Round96.sumPacketTransfer E I selected velocity items
  ≡ selectedPairFold E I selected velocity items
    + pEnergySelectedPairFold E I selected velocity items
    + qEnergySelectedPairFold E I selected velocity items
packetTransferSplit E I selected velocity [] = solve []
packetTransferSplit E I selected velocity (tau ∷ rest) =
  trans
    (cong
      (Round96.packetTriadTransfer E I selected velocity tau +_)
      (packetTransferSplit E I selected velocity rest))
    (solve
      ( selectedPairPower E I selected velocity tau
      ∷ Round96.selectTransfer (selected (Physical.p tau))
          (Round38.orderedPairPower E I (Orbit.pEnergyLeg tau) velocity)
      ∷ Round96.selectTransfer (selected (Physical.q tau))
          (Round38.orderedPairPower E I (Orbit.qEnergyLeg tau) velocity)
      ∷ selectedPairFold E I selected velocity rest
      ∷ pEnergySelectedPairFold E I selected velocity rest
      ∷ qEnergySelectedPairFold E I selected velocity rest
      ∷ []))

sumPacketTransferIsSixSelectedOrderedFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  Round96.sumPacketTransfer E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
  ≡ Round38.sixFold
      (selectedOrderedFold E I selected velocity
        (Physical.physicalTriadEnumeration cutoff))
sumPacketTransferIsSixSelectedOrderedFold E I selected velocity cutoff =
  let
    enumeration = Physical.physicalTriadEnumeration cutoff
    pairTotal = selectedPairFold E I selected velocity enumeration
    orderedTotal = selectedOrderedFold E I selected velocity enumeration
    pInv = pEnergySelectedPairInvariant E I selected velocity cutoff
    qInv = qEnergySelectedPairInvariant E I selected velocity cutoff
    pairDouble = selectedPairFoldIsDoubleOrdered E I selected velocity cutoff
  in
  trans
    (packetTransferSplit E I selected velocity enumeration)
    (trans
      (cong₂ (λ p q → pairTotal + p + q) pInv qInv)
      (trans
        (cong₂ _+_ (cong₂ _+_ pairDouble pairDouble) pairDouble)
        (solve (orderedTotal ∷ []))))

normalizedPacketTransferIsSelectedOrderedFold :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  Norm.normalizedPacketTransfer E I selected velocity cutoff
  ≡ selectedOrderedFold E I selected velocity
      (Physical.physicalTriadEnumeration cutoff)
normalizedPacketTransferIsSelectedOrderedFold E I selected velocity cutoff =
  let total = selectedOrderedFold E I selected velocity
        (Physical.physicalTriadEnumeration cutoff)
  in
  trans
    (cong (Norm.oneSixth *_)
      (sumPacketTransferIsSixSelectedOrderedFold E I selected velocity cutoff))
    (solve (total ∷ []))

------------------------------------------------------------------------
-- Literal selected projected pairing = selected ordered fold.
------------------------------------------------------------------------

selectedProjectedOutputPower :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  (Z3.FourierMode → Bool) → Z3.FourierMode → ℚ
selectedProjectedOutputPower system selected output =
  Round96.selectTransfer (selected output)
    (OutputPairing.realHermitianPower
      (Equation.velocity system output)
      (Equation.projectedNonlinearity system output))

sumSelectedProjectedPairings :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  (Z3.FourierMode → Bool) → List Z3.FourierMode → ℚ
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

selectedFiberFold :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) →
  (output : Z3.FourierMode) →
  selectedProjectedOutputPower system selected output
  ≡ selectedOrderedFold E I selected (Equation.velocity system)
      (Equation.concreteTriadsAt system output)
selectedFiberFold {E} {I} system selected output with selected output
... | true =
  trans
    (OutputPairing.projectedOutputEnergyPairingEqualsOrderedFiberFold
      system output)
    (sym (goTrue (Equation.concreteTriadsAt system output)
      (λ tau member → Equation.concreteTriadsAtOutputAgreement member)))
  where
  goTrue :
    (items : List Physical.PhysicalTriadIncidence) →
    (∀ tau → Cube._∈_ tau items → Physical.k tau ≡ output) →
    selectedOrderedFold E I (λ _ → true) (Equation.velocity system) items
    ≡ Round38.foldPower
        (λ tau → Round38.orderedPower E I tau (Equation.velocity system)) items
  goTrue [] pointwise = refl
  goTrue (tau ∷ rest) pointwise =
    cong
      (Round38.orderedPower E I tau (Equation.velocity system) +_)
      (goTrue rest (λ chosen member → pointwise chosen (Cube.there member)))
... | false =
  sym (goFalse (Equation.concreteTriadsAt system output)
    (λ tau member → Equation.concreteTriadsAtOutputAgreement member))
  where
  goFalse :
    (items : List Physical.PhysicalTriadIncidence) →
    (∀ tau → Cube._∈_ tau items → Physical.k tau ≡ output) →
    selectedOrderedFold E I (λ _ → false) (Equation.velocity system) items
    ≡ 0ℚ
  goFalse [] pointwise = refl
  goFalse (tau ∷ rest) pointwise =
    goFalse rest (λ chosen member → pointwise chosen (Cube.there member))

-- We avoid a separate selected-output-fibre partition theorem: Round39 already
-- proves the literal concatenated fibre list is a permutation of the complete
-- enumeration, and foldPermutationInvariant works for any scalar value map.
foldAppend :
  (value : Physical.PhysicalTriadIncidence → ℚ) →
  ∀ left right →
  Round38.foldPower value (Cube._++_ left right)
  ≡ Round38.foldPower value left + Round38.foldPower value right
foldAppend value [] right = refl
foldAppend value (tau ∷ rest) right =
  trans
    (cong (value tau +_) (foldAppend value rest right))
    (solve
      (value tau ∷ Round38.foldPower value rest
       ∷ Round38.foldPower value right ∷ []))

sumSelectedEqualsConcatFold :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) →
  (outputs : List Z3.FourierMode) →
  sumSelectedProjectedPairings system selected outputs
  ≡ selectedOrderedFold E I selected (Equation.velocity system)
      (Round39.concatOutputFibers (Equation.cutoff system) outputs)
sumSelectedEqualsConcatFold system selected [] = refl
sumSelectedEqualsConcatFold {E} {I} system selected (output ∷ rest) =
  trans
    (cong₂ _+_
      (selectedFiberFold system selected output)
      (sumSelectedEqualsConcatFold system selected rest))
    (sym
      (foldAppend
        (selectedOrderedPower E I selected (Equation.velocity system))
        (Equation.concreteTriadsAt system output)
        (Round39.concatOutputFibers (Equation.cutoff system) rest)))

literalSelectedProjectedPairingEqualsSelectedOrderedFold :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) →
  literalSelectedProjectedPairing system selected
  ≡ selectedOrderedFold E I selected (Equation.velocity system)
      (Physical.physicalTriadEnumeration (Equation.cutoff system))
literalSelectedProjectedPairingEqualsSelectedOrderedFold {E} {I}
    system selected =
  trans
    (sumSelectedEqualsConcatFold
      system selected (Cube.cutoffModes (Equation.cutoff system)))
    (Round38.foldPermutationInvariant
      (selectedOrderedPower E I selected (Equation.velocity system))
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
    (literalSelectedProjectedPairingEqualsSelectedOrderedFold system selected)
    (sym (normalizedPacketTransferIsSelectedOrderedFold
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

round98SelectedWeightedOutputFiberIdentificationClosedIsTrue :
  round98SelectedWeightedOutputFiberIdentificationClosed ≡ true
round98SelectedWeightedOutputFiberIdentificationClosedIsTrue = refl
