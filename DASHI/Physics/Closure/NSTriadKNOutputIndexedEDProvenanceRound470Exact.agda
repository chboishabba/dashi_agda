module DASHI.Physics.Closure.NSTriadKNOutputIndexedEDProvenanceRound470Exact where

------------------------------------------------------------------------
-- ROUND470 / OUTPUT-LOCAL ED PROVENANCE -> GLOBAL R436 ROUTING
--
-- R435 erases the modal-pair provenance of each scalar `cellED`. R436 therefore
-- had to ask a caller for one global equality between `sumED` and an R109
-- selected-pair sum. That global receipt is too late: the information was
-- already erased.
--
-- This owner repairs the direction of compilation. Each fixed-output cell is
-- constructed together with the local same-object receipt
--
--   cellED(k) = fold_{tau : outputFiber(k)} selectedPairED(tau).
--
-- From those local receipts only, list induction gives the sum over all output
-- fibres. R39 identifies their concatenation with the complete physical triad
-- enumeration, and R469 identifies that physical fold with the R109 selected
-- cartesian pair sum. Thus R436.PhysicalFixedOutputEDRouting is constructed
-- automatically: no caller-supplied global partition equality remains.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (map)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergyDissipationProductRound109Exact as R109
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNF4GlobalOutputFiberPartitionRound39Exact as R39
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlCellEDAdapterRound219Exact as R219
import DASHI.Physics.Closure.NSTriadKNFixedOutputCriticalConeFamilyRound435Exact as R435
import DASHI.Physics.Closure.NSTriadKNFixedOutputEDSelectorRoutingRound436Exact as R436
import DASHI.Physics.Closure.NSTriadKNSelectedPairPhysicalTriadRoutingRound469Exact as R469

F : C3.RealField _
F = Rational.rationalRealField

record OutputIndexedPhysicalEDFamily
    {theta coefficient : ℚ}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat)
    (select : Z3.FourierMode → Z3.FourierMode → Bool) : Set₁ where
  constructor output-indexed-physical-ed-family
  field
    cellAt :
      Z3.FourierMode →
      R435.UniformFixedOutputCriticalConeCell theta coefficient

    cellEDMeaning :
      (output : Z3.FourierMode) →
      R435.cellED (cellAt output)
      ≡ R38.foldPower
          (R469.selectedTriadValue
            (R219.physicalModalED E I velocity) select)
          (Output.physicalOutputFiber cutoff output)

open OutputIndexedPhysicalEDFamily public

cellsForOutputs :
  ∀ {theta coefficient E I velocity cutoff select} →
  OutputIndexedPhysicalEDFamily
    {theta} {coefficient} E I velocity cutoff select →
  List Z3.FourierMode →
  List (R435.UniformFixedOutputCriticalConeCell theta coefficient)
cellsForOutputs family outputs = map (cellAt family) outputs

sumEDCellsForOutputs :
  ∀ {theta coefficient E I velocity cutoff select}
    (family : OutputIndexedPhysicalEDFamily
      {theta} {coefficient} E I velocity cutoff select)
    (outputs : List Z3.FourierMode) →
  R435.sumED (cellsForOutputs family outputs)
  ≡ R38.foldPower
      (R469.selectedTriadValue (R219.physicalModalED E I velocity) select)
      (R39.concatOutputFibers cutoff outputs)
sumEDCellsForOutputs family [] = refl
sumEDCellsForOutputs {E = E} {I = I} {velocity = velocity}
    {cutoff = cutoff} {select = select} family (output ∷ rest) =
  let
    value = R469.selectedTriadValue (R219.physicalModalED E I velocity) select
  in
  trans
    (cong₂ _+_
      (cellEDMeaning family output)
      (sumEDCellsForOutputs family rest))
    (sym
      (R39.foldAppend value
        (Output.physicalOutputFiber cutoff output)
        (R39.concatOutputFibers cutoff rest)))

cellsForCutoff :
  ∀ {theta coefficient E I velocity cutoff select} →
  OutputIndexedPhysicalEDFamily
    {theta} {coefficient} E I velocity cutoff select →
  List (R435.UniformFixedOutputCriticalConeCell theta coefficient)
cellsForCutoff {cutoff = cutoff} family =
  cellsForOutputs family (Cube.cutoffModes cutoff)

globalEDPartitionEquality :
  ∀ {theta coefficient E I velocity cutoff select}
    (family : OutputIndexedPhysicalEDFamily
      {theta} {coefficient} E I velocity cutoff select) →
  R435.sumED (cellsForCutoff family)
  ≡
  R109.selectedOrderedPairSum
    (R219.physicalModalED E I velocity)
    (R469.outputFilteredSelect cutoff select)
    (Cube.cutoffModes cutoff)
    (Cube.cutoffModes cutoff)
globalEDPartitionEquality {E = E} {I = I} {velocity = velocity}
    {cutoff = cutoff} {select = select} family =
  trans
    (sumEDCellsForOutputs family (Cube.cutoffModes cutoff))
    (sym
      (R469.selectedPairsEqualOutputFibrePartitionFold
        (R219.physicalModalED E I velocity) cutoff select))

physicalRoutingFromOutputIndexedFamily :
  ∀ {theta coefficient E I velocity cutoff select}
    (family : OutputIndexedPhysicalEDFamily
      {theta} {coefficient} E I velocity cutoff select) →
  R436.PhysicalFixedOutputEDRouting
    (cellsForCutoff family)
    E I velocity (Cube.cutoffModes cutoff)
physicalRoutingFromOutputIndexedFamily {cutoff = cutoff} {select = select} family = record
  { R436.select = R469.outputFilteredSelect cutoff select
  ; R436.fibreEDSumMeaning = globalEDPartitionEquality family
  }

outputIndexedFamilyToGlobalSelectedPairPayment :
  ∀ {theta coefficient E I velocity cutoff select}
    (family : OutputIndexedPhysicalEDFamily
      {theta} {coefficient} E I velocity cutoff select) →
  R435.GlobalSelectedPairEDPayment (cellsForCutoff family)
outputIndexedFamilyToGlobalSelectedPairPayment
    {E = E} {I = I} {velocity = velocity} {cutoff = cutoff} family =
  R436.physicalRoutingToGlobalSelectedPairEDPayment
    (cellsForCutoff family)
    E I velocity (Cube.cutoffModes cutoff)
    (physicalRoutingFromOutputIndexedFamily family)

outputIndexedFamilyGlobalCriticalConeBound :
  ∀ {theta coefficient E I velocity cutoff select}
    (family : OutputIndexedPhysicalEDFamily
      {theta} {coefficient} E I velocity cutoff select) →
  0ℚ ≤ coefficient →
  R435.sumCross (cellsForCutoff family)
  ≤ theta * R435.sumCompanion (cellsForCutoff family)
    + coefficient
      * (R436.globalPhysicalEnergyDissipationProduct
          E I velocity (Cube.cutoffModes cutoff)
        + R436.globalPhysicalEnergyDissipationProduct
          E I velocity (Cube.cutoffModes cutoff))
outputIndexedFamilyGlobalCriticalConeBound
    {E = E} {I = I} {velocity = velocity} {cutoff = cutoff}
    family coefficientNN =
  R436.physicalRoutingClosesGlobalFixedOutputEDBudget
    (cellsForCutoff family)
    E I velocity (Cube.cutoffModes cutoff)
    coefficientNN
    (physicalRoutingFromOutputIndexedFamily family)

round470GlobalR436PartitionEqualityDerived : Bool
round470GlobalR436PartitionEqualityDerived = true

round470CallerSuppliedGlobalPartitionEqualityRequired : Bool
round470CallerSuppliedGlobalPartitionEqualityRequired = false

round470OnlyOutputLocalEDProvenanceRequired : Bool
round470OnlyOutputLocalEDProvenanceRequired = true

round470AddsOutputCardinalityFactor : Bool
round470AddsOutputCardinalityFactor = false

round470ContainsPostulate : Bool
round470ContainsPostulate = false

round470PackageAClosed : Bool
round470PackageAClosed = false

round470ClayPromotion : Bool
round470ClayPromotion = false

round470CallerSuppliedGlobalPartitionEqualityRequiredIsFalse :
  round470CallerSuppliedGlobalPartitionEqualityRequired ≡ false
round470CallerSuppliedGlobalPartitionEqualityRequiredIsFalse = refl

round470AddsOutputCardinalityFactorIsFalse :
  round470AddsOutputCardinalityFactor ≡ false
round470AddsOutputCardinalityFactorIsFalse = refl

round470ContainsPostulateIsFalse : round470ContainsPostulate ≡ false
round470ContainsPostulateIsFalse = refl
