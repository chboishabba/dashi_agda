module DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedDoubleMixedMassRound456Exact where

------------------------------------------------------------------------
-- ROUND456 / PHYSICAL NORMALIZED DOUBLE-MIXED MASS -> 48 E^2
--
-- R455 turns scalar radius calibration into unit norm of each literal
-- normalized direction.  R329 transports incompressibility to transversality
-- against that normalized direction.  R452 then gives, pointwise,
--
--   ||doubleMixedCell(p,q)||^2 <= 48 E_p E_q.
--
-- R454 identifies the literal fixed-output fibre with an R453 selected pair
-- sum, hence
--
--   sum_{p+q=k} E_p E_q <= (sum_m E_m)^2
--
-- on the cutoff cube.  This file composes those owners on the exact R225
-- physical companion carrier.  No fibre cardinality, shell count, or new
-- analytic inequality appears.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNCriticalSlotQuadraticKernelRound167Exact as R167
import DASHI.Physics.Closure.NSTriadKNHHAntiParallelQuadraticKernelNormRound174Exact as R174
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNStrongLowLiteralNestedKernelRound329Exact as R329
import DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact as R452
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergySquareRound453Exact as R453
import DASHI.Physics.Closure.NSTriadKNFixedOutputEnergySquareRoutingRound454Exact as R454
import DASHI.Physics.Closure.NSTriadKNRationalNormalizedDirectionUnitRound455Exact as R455

F : C3.RealField _
F = Rational.rationalRealField

norm : C3.Complex3 F → ℚ
norm = L2.complex3NormSquared

record PhysicalModeRadiusCalibration
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F) : Set where
  constructor physical-mode-radius-calibration
  field
    calibrate :
      (mode : Z3.FourierMode) →
      R455.RationalModeRadiusCalibration E I S mode

open PhysicalModeRadiusCalibration public

physicalUnitDirectionPair :
  (E : C3.IntegerEmbedding F)
  (I : C3.ModeInverseSquare F E)
  (S : Helical.HelicalModeScalars F) →
  PhysicalModeRadiusCalibration E I S →
  (tau : Physical.PhysicalTriadIncidence) →
  R452.UnitDirectionPair
    (R167.normalizedDirection E S (Physical.p tau))
    (R167.normalizedDirection E S (Physical.q tau))
physicalUnitDirectionPair E I S C tau =
  R452.unit-direction-pair
    (R455.normalizedDirectionUnit E I S (Physical.p tau)
      (calibrate C (Physical.p tau)))
    (R455.normalizedDirectionUnit E I S (Physical.q tau)
      (calibrate C (Physical.q tau)))

physicalTransverseHighPair :
  {E : C3.IntegerEmbedding F}
  {I : C3.ModeInverseSquare F E}
  {S : Helical.HelicalModeScalars F}
  {L : Helical.PeriodicHelicalProjectorLaws F E I S}
  {H : R142.HelicalHalfCalibration S}
  {velocity : Z3.FourierMode → C3.Complex3 F} →
  R225.PhysicalFixedOutputHelicityData E I S L H velocity →
  (tau : Physical.PhysicalTriadIncidence) →
  R145.TransverseHighPair
    (R167.normalizedDirection E S (Physical.p tau))
    (R167.normalizedDirection E S (Physical.q tau))
    (velocity (Physical.p tau))
    (velocity (Physical.q tau))
physicalTransverseHighPair {E = E} {S = S} {velocity = velocity} P tau = record
  { R145.aTransverseP =
      R329.transverseToNormalizedDirection E S (Physical.p tau)
        (velocity (Physical.p tau))
        (R225.velocityTransverse P (Physical.p tau))
  ; R145.bTransverseQ =
      R329.transverseToNormalizedDirection E S (Physical.q tau)
        (velocity (Physical.q tau))
        (R225.velocityTransverse P (Physical.q tau))
  }

physicalDoubleMixedCellMassBelowFortyEight :
  {E : C3.IntegerEmbedding F}
  {I : C3.ModeInverseSquare F E}
  {S : Helical.HelicalModeScalars F}
  {L : Helical.PeriodicHelicalProjectorLaws F E I S}
  {H : R142.HelicalHalfCalibration S}
  {velocity : Z3.FourierMode → C3.Complex3 F} →
  (P : R225.PhysicalFixedOutputHelicityData E I S L H velocity) →
  (C : PhysicalModeRadiusCalibration E I S) →
  (tau : Physical.PhysicalTriadIncidence) →
  norm (R225.doubleMixedCell S velocity tau)
  ≤ R452.fortyEight
      * (norm (velocity (Physical.p tau))
        * norm (velocity (Physical.q tau)))
physicalDoubleMixedCellMassBelowFortyEight
    {E = E} {I = I} {S = S} {velocity = velocity} P C tau =
  let
    pDir = R167.normalizedDirection E S (Physical.p tau)
    qDir = R167.normalizedDirection E S (Physical.q tau)
    uP = velocity (Physical.p tau)
    uQ = velocity (Physical.q tau)

    iBound = R452.iScaledNormalizedSlotMassBelowFortyEight
      pDir qDir uP uQ
      (physicalUnitDirectionPair E I S C tau)
      (physicalTransverseHighPair P tau)

    sameObject = R225.iQuadraticKernelCellIsDoubleMixedCell P tau
  in
  subst
    (λ selected →
      norm selected ≤ R452.fortyEight * (norm uP * norm uQ))
    sameObject
    iBound

physicalEnergy :
  (Z3.FourierMode → C3.Complex3 F) → Z3.FourierMode → ℚ
physicalEnergy velocity mode = norm (velocity mode)

physicalModalEnergy :
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  R453.ModalEnergy Z3.FourierMode
physicalModalEnergy velocity =
  R453.modal-energy
    (physicalEnergy velocity)
    (λ mode → Separation.complex3NormSquaredNonnegative (velocity mode))

sumDoubleMixedMass :
  {E : C3.IntegerEmbedding F}
  {I : C3.ModeInverseSquare F E} →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
sumDoubleMixedMass S velocity [] = 0ℚ
sumDoubleMixedMass S velocity (tau ∷ rest) =
  norm (R225.doubleMixedCell S velocity tau)
  + sumDoubleMixedMass S velocity rest

fortyEightNN : 0ℚ ≤ R452.fortyEight
fortyEightNN =
  let
    oneNN = Rational.squareNonnegative 1ℚ
    twoNN = Rational.addNonnegative oneNN oneNN
    fourNN = Rational.addNonnegative twoNN twoNN
    sixNN = Rational.addNonnegative (Rational.addNonnegative twoNN twoNN) twoNN
    twelveNN = Rational.addNonnegative sixNN sixNN
  in
  R96.productNonnegative twelveNN fourNN

sumDoubleMixedMassBelowEnergyProducts :
  {E : C3.IntegerEmbedding F}
  {I : C3.ModeInverseSquare F E}
  {S : Helical.HelicalModeScalars F}
  {L : Helical.PeriodicHelicalProjectorLaws F E I S}
  {H : R142.HelicalHalfCalibration S}
  {velocity : Z3.FourierMode → C3.Complex3 F} →
  (P : R225.PhysicalFixedOutputHelicityData E I S L H velocity) →
  (C : PhysicalModeRadiusCalibration E I S) →
  (items : List Physical.PhysicalTriadIncidence) →
  sumDoubleMixedMass S velocity items
  ≤ R452.fortyEight * R454.triadEnergyProductSum
      (physicalEnergy velocity) items
sumDoubleMixedMassBelowEnergyProducts P C [] =
  subst
    (0ℚ ≤_)
    (sym (ℚP.*-zeroʳ R452.fortyEight))
    ℚP.≤-refl
sumDoubleMixedMassBelowEnergyProducts
    {S = S} {velocity = velocity} P C (tau ∷ rest) =
  let
    headBound = physicalDoubleMixedCellMassBelowFortyEight P C tau
    tailBound = sumDoubleMixedMassBelowEnergyProducts P C rest
    added = ℚP.+-mono-≤ headBound tailBound
    pair =
      physicalEnergy velocity (Physical.p tau)
      * physicalEnergy velocity (Physical.q tau)
    tailPairs = R454.triadEnergyProductSum (physicalEnergy velocity) rest
    endpoint :
      R452.fortyEight * pair + R452.fortyEight * tailPairs
      ≡ R452.fortyEight * (pair + tailPairs)
    endpoint = solve (R452.fortyEight ∷ pair ∷ tailPairs ∷ [])
  in
  subst
    (λ upper →
      norm (R225.doubleMixedCell S velocity tau)
        + sumDoubleMixedMass S velocity rest ≤ upper)
    endpoint
    added

fixedOutputDoubleMixedMassBelowEnergySquare :
  {E : C3.IntegerEmbedding F}
  {I : C3.ModeInverseSquare F E}
  {S : Helical.HelicalModeScalars F}
  {L : Helical.PeriodicHelicalProjectorLaws F E I S}
  {H : R142.HelicalHalfCalibration S}
  {velocity : Z3.FourierMode → C3.Complex3 F} →
  (P : R225.PhysicalFixedOutputHelicityData E I S L H velocity) →
  (C : PhysicalModeRadiusCalibration E I S) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  sumDoubleMixedMass S velocity (Output.physicalOutputFiber cutoff output)
  ≤ R452.fortyEight
      * (R453.sumEnergy (physicalModalEnergy velocity) (Cube.cutoffModes cutoff)
        * R453.sumEnergy (physicalModalEnergy velocity) (Cube.cutoffModes cutoff))
fixedOutputDoubleMixedMassBelowEnergySquare
    {velocity = velocity} P C cutoff output =
  let
    fibre = Output.physicalOutputFiber cutoff output
    local = sumDoubleMixedMassBelowEnergyProducts P C fibre
    selected =
      R454.WithEnergy.physicalOutputFibreEnergyBelowSquare
        (physicalModalEnergy velocity) cutoff output
    scaled :
      R452.fortyEight
        * R454.triadEnergyProductSum (physicalEnergy velocity) fibre
      ≤ R452.fortyEight
        * (R453.sumEnergy (physicalModalEnergy velocity) (Cube.cutoffModes cutoff)
          * R453.sumEnergy (physicalModalEnergy velocity) (Cube.cutoffModes cutoff))
    scaled =
      let instance fortyEightNNI = nonNegative fortyEightNN
      in ℚP.*-monoˡ-≤-nonNeg R452.fortyEight selected
  in
  ℚP.≤-trans local scaled

round456PhysicalNormalizedCellMassBoundClosed : Bool
round456PhysicalNormalizedCellMassBoundClosed = true

round456FixedOutputNormalizedMassPaidByEnergySquare : Bool
round456FixedOutputNormalizedMassPaidByEnergySquare = true

round456IntroducesCardinalityTax : Bool
round456IntroducesCardinalityTax = false

round456RequiresPhysicalModeRadiusCalibration : Bool
round456RequiresPhysicalModeRadiusCalibration = true

round456PackageAClosed : Bool
round456PackageAClosed = false

round456ClayPromotion : Bool
round456ClayPromotion = false

round456IntroducesCardinalityTaxIsFalse :
  round456IntroducesCardinalityTax ≡ false
round456IntroducesCardinalityTaxIsFalse = refl
