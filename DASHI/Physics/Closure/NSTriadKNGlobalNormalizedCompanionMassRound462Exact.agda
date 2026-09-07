module DASHI.Physics.Closure.NSTriadKNGlobalNormalizedCompanionMassRound462Exact where

------------------------------------------------------------------------
-- ROUND462 / GLOBAL NONZERO-OUTPUT NORMALIZED COMPANION MASS <= 48 E_N^2
--
-- R456 pays one arbitrary incidence list pointwise by 48 times its energy-
-- product fold.  The remaining issue is global routing without paying the same
-- E_N^2 once for every output.
--
-- Round34 defines the live output list as `removeZero (cutoffModes N)`.
-- Round39 proves the concatenation of ALL literal output fibres is a
-- permutation of `physicalTriadEnumeration N`.  Since every cell mass is
-- nonnegative, removing the zero-output block can only decrease the mass.
--
-- Finally the complete physical triad enumeration is exactly a filtered
-- Cartesian product of cutoff modes, and R453 pays ANY Boolean-selected pair
-- energy sum by E_N^2.  Hence the complete selected nonzero-output companion
-- mass is paid ONCE:
--
--   sum_{k != 0} sum_{tau in F_k} ||D_tau||^2 <= 48 E_N^2.
--
-- No output-count or incidence-count factor appears.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; NonNegative; nonNegative; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNF4GlobalOutputFiberPartitionRound39Exact as R39
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact as R452
import DASHI.Physics.Closure.NSTriadKNSelectedPairEnergySquareRound453Exact as R453
import DASHI.Physics.Closure.NSTriadKNFixedOutputEnergySquareRoutingRound454Exact as R454
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedDoubleMixedMassRound456Exact as R456

F : C3.RealField _
F = Rational.rationalRealField

norm : C3.Complex3 F → ℚ
norm = L2.complex3NormSquared

sumMassAppend :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (left right : List Physical.PhysicalTriadIncidence) →
  R456.sumDoubleMixedMass S velocity (Cube._++_ left right)
  ≡ R456.sumDoubleMixedMass S velocity left
    + R456.sumDoubleMixedMass S velocity right
sumMassAppend S velocity [] right = refl
sumMassAppend S velocity (tau ∷ rest) right =
  trans
    (cong₂ _+_ refl (sumMassAppend S velocity rest right))
    (solve
      ( norm (R225.doubleMixedCell S velocity tau)
      ∷ R456.sumDoubleMixedMass S velocity rest
      ∷ R456.sumDoubleMixedMass S velocity right ∷ []))

sumMassNN :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (items : List Physical.PhysicalTriadIncidence) →
  0ℚ ≤ R456.sumDoubleMixedMass S velocity items
sumMassNN S velocity [] = ℚP.≤-refl
sumMassNN S velocity (tau ∷ rest) =
  Rational.addNonnegative
    (Separation.complex3NormSquaredNonnegative
      (R225.doubleMixedCell S velocity tau))
    (sumMassNN S velocity rest)

outputMassSum :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Helical.HelicalModeScalars F →
  (Z3.FourierMode → C3.Complex3 F) →
  Nat → List Z3.FourierMode → ℚ
outputMassSum S velocity cutoff [] = 0ℚ
outputMassSum S velocity cutoff (output ∷ rest) =
  R456.sumDoubleMixedMass S velocity
    (Output.physicalOutputFiber cutoff output)
  + outputMassSum S velocity cutoff rest

outputMassSumIsConcatMass :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat) (outputs : List Z3.FourierMode) →
  outputMassSum S velocity cutoff outputs
  ≡ R456.sumDoubleMixedMass S velocity
      (R39.concatOutputFibers cutoff outputs)
outputMassSumIsConcatMass S velocity cutoff [] = refl
outputMassSumIsConcatMass S velocity cutoff (output ∷ rest) =
  trans
    (cong₂ _+_ refl (outputMassSumIsConcatMass S velocity cutoff rest))
    (sym
      (sumMassAppend S velocity
        (Output.physicalOutputFiber cutoff output)
        (R39.concatOutputFibers cutoff rest)))

removeZeroOutputMassBelow :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat) (outputs : List Z3.FourierMode) →
  outputMassSum S velocity cutoff (Canonical.removeZero outputs)
  ≤ outputMassSum S velocity cutoff outputs
removeZeroOutputMassBelow S velocity cutoff [] = ℚP.≤-refl
removeZeroOutputMassBelow S velocity cutoff (output ∷ rest)
  with Output.modeEqual output Z3.zeroMode
... | true =
  let
    ih = removeZeroOutputMassBelow S velocity cutoff rest
    headNN = sumMassNN S velocity (Output.physicalOutputFiber cutoff output)
    lifted :
      0ℚ + outputMassSum S velocity cutoff (Canonical.removeZero rest)
      ≤ R456.sumDoubleMixedMass S velocity
          (Output.physicalOutputFiber cutoff output)
        + outputMassSum S velocity cutoff rest
    lifted = ℚP.+-mono-≤ headNN ih
  in
  subst
    (λ lower → lower ≤
      R456.sumDoubleMixedMass S velocity
        (Output.physicalOutputFiber cutoff output)
      + outputMassSum S velocity cutoff rest)
    (ℚP.+-identityˡ
      (outputMassSum S velocity cutoff (Canonical.removeZero rest)))
    lifted
... | false =
  ℚP.+-mono-≤ ℚP.≤-refl
    (removeZeroOutputMassBelow S velocity cutoff rest)

massFoldAsR38 :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (items : List Physical.PhysicalTriadIncidence) →
  R456.sumDoubleMixedMass S velocity items
  ≡ R38.foldPower
      (λ tau → norm (R225.doubleMixedCell S velocity tau)) items
massFoldAsR38 S velocity [] = refl
massFoldAsR38 S velocity (tau ∷ rest) =
  cong₂ _+_ refl (massFoldAsR38 S velocity rest)

fullOutputMassIsPhysicalEnumerationMass :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (velocity : Z3.FourierMode → C3.Complex3 F)
    (cutoff : Nat) →
  outputMassSum S velocity cutoff (Cube.cutoffModes cutoff)
  ≡ R456.sumDoubleMixedMass S velocity
      (Physical.physicalTriadEnumeration cutoff)
fullOutputMassIsPhysicalEnumerationMass S velocity cutoff =
  trans
    (outputMassSumIsConcatMass S velocity cutoff (Cube.cutoffModes cutoff))
    (trans
      (massFoldAsR38 S velocity (R39.concatOutputFibers cutoff (Cube.cutoffModes cutoff)))
      (trans
        (R38.foldPermutationInvariant
          (λ tau → norm (R225.doubleMixedCell S velocity tau))
          (R39.literalOutputPartitionPermutation cutoff))
        (sym
          (massFoldAsR38 S velocity
            (Physical.physicalTriadEnumeration cutoff)))))

physicalSelector : Nat → Z3.FourierMode → Z3.FourierMode → Bool
physicalSelector cutoff p q =
  Physical.modeWithinCutoff cutoff (Z3.addMode p q)

pairSelectedSum :
  (energy : Z3.FourierMode → ℚ) →
  Nat → List (Cube.Pair Z3.FourierMode Z3.FourierMode) → ℚ
pairSelectedSum energy cutoff [] = 0ℚ
pairSelectedSum energy cutoff (pair ∷ rest) with
  physicalSelector cutoff (Cube.first pair) (Cube.second pair)
... | true =
  energy (Cube.first pair) * energy (Cube.second pair)
  + pairSelectedSum energy cutoff rest
... | false = pairSelectedSum energy cutoff rest

enumeratedEnergyExact :
  (energy : Z3.FourierMode → ℚ) →
  (cutoff : Nat) →
  (pairs : List (Cube.Pair Z3.FourierMode Z3.FourierMode)) →
  R454.triadEnergyProductSum energy (Physical.enumerateFromPairs cutoff pairs)
  ≡ pairSelectedSum energy cutoff pairs
enumeratedEnergyExact energy cutoff [] = refl
enumeratedEnergyExact energy cutoff (pair ∷ rest)
  with Physical.modeWithinCutoff cutoff
    (Z3.addMode (Cube.first pair) (Cube.second pair))
... | true = cong₂ _+_ refl (enumeratedEnergyExact energy cutoff rest)
... | false = enumeratedEnergyExact energy cutoff rest

mappedBlockSelectedExact :
  (E : R453.ModalEnergy Z3.FourierMode) →
  (cutoff : Nat) (left : Z3.FourierMode) →
  (rights : List Z3.FourierMode) →
  pairSelectedSum (R453.energy E) cutoff
    (Cube.map (λ right → Cube.pair left right) rights)
  ≡ R453.selectedEnergyInner E (physicalSelector cutoff) left rights
mappedBlockSelectedExact E cutoff left [] = refl
mappedBlockSelectedExact E cutoff left (right ∷ rest)
  with physicalSelector cutoff left right
... | true = cong₂ _+_ refl (mappedBlockSelectedExact E cutoff left rest)
... | false = mappedBlockSelectedExact E cutoff left rest

pairSelectedAppend :
  (energy : Z3.FourierMode → ℚ) →
  (cutoff : Nat) →
  (left right : List (Cube.Pair Z3.FourierMode Z3.FourierMode)) →
  pairSelectedSum energy cutoff (Cube._++_ left right)
  ≡ pairSelectedSum energy cutoff left + pairSelectedSum energy cutoff right
pairSelectedAppend energy cutoff [] right = refl
pairSelectedAppend energy cutoff (pair ∷ rest) right
  with physicalSelector cutoff (Cube.first pair) (Cube.second pair)
... | true rewrite pairSelectedAppend energy cutoff rest right = refl
... | false = pairSelectedAppend energy cutoff rest right

cartesianSelectedExact :
  (E : R453.ModalEnergy Z3.FourierMode) →
  (cutoff : Nat) →
  (lefts rights : List Z3.FourierMode) →
  pairSelectedSum (R453.energy E) cutoff (Cube.cartesian lefts rights)
  ≡ R453.selectedEnergyPairSum E (physicalSelector cutoff) lefts rights
cartesianSelectedExact E cutoff [] rights = refl
cartesianSelectedExact E cutoff (left ∷ rest) rights =
  trans
    (pairSelectedAppend (R453.energy E) cutoff
      (Cube.map (λ right → Cube.pair left right) rights)
      (Cube.cartesian rest rights))
    (cong₂ _+_
      (mappedBlockSelectedExact E cutoff left rights)
      (cartesianSelectedExact E cutoff rest rights))

physicalEnumerationEnergyBelowSquare :
  (E : R453.ModalEnergy Z3.FourierMode) →
  (cutoff : Nat) →
  R454.triadEnergyProductSum (R453.energy E)
      (Physical.physicalTriadEnumeration cutoff)
  ≤ R453.sumEnergy E (Cube.cutoffModes cutoff)
      * R453.sumEnergy E (Cube.cutoffModes cutoff)
physicalEnumerationEnergyBelowSquare E cutoff =
  let
    pairs = Cube.cartesian (Cube.cutoffModes cutoff) (Cube.cutoffModes cutoff)
    exact :
      R454.triadEnergyProductSum (R453.energy E)
        (Physical.physicalTriadEnumeration cutoff)
      ≡ R453.selectedEnergyPairSum E (physicalSelector cutoff)
          (Cube.cutoffModes cutoff) (Cube.cutoffModes cutoff)
    exact =
      trans
        (enumeratedEnergyExact (R453.energy E) cutoff pairs)
        (cartesianSelectedExact E cutoff
          (Cube.cutoffModes cutoff) (Cube.cutoffModes cutoff))

    bound = R453.selectedEnergyPairSumBound
      E (physicalSelector cutoff) (Cube.cutoffModes cutoff)
  in
  subst
    (λ lower → lower ≤
      R453.sumEnergy E (Cube.cutoffModes cutoff)
        * R453.sumEnergy E (Cube.cutoffModes cutoff))
    (sym exact)
    bound

module PhysicalGlobalMass
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    {velocity : Z3.FourierMode → C3.Complex3 F}
    (P : R225.PhysicalFixedOutputHelicityData E I S L H velocity)
    (C : R456.PhysicalModeRadiusCalibration E I S)
    (cutoff : Nat) where

  modalEnergy = R456.physicalModalEnergy velocity
  energySquare =
    R453.sumEnergy modalEnergy (Cube.cutoffModes cutoff)
      * R453.sumEnergy modalEnergy (Cube.cutoffModes cutoff)

  selectedMass : ℚ
  selectedMass = outputMassSum S velocity cutoff (Canonical.nonzeroCutoffModes cutoff)

  fullMass : ℚ
  fullMass = R456.sumDoubleMixedMass S velocity
    (Physical.physicalTriadEnumeration cutoff)

  selectedMassBelowFull : selectedMass ≤ fullMass
  selectedMassBelowFull =
    ℚP.≤-trans
      (removeZeroOutputMassBelow S velocity cutoff (Cube.cutoffModes cutoff))
      (subst
        (λ upper → outputMassSum S velocity cutoff (Cube.cutoffModes cutoff) ≤ upper)
        (fullOutputMassIsPhysicalEnumerationMass S velocity cutoff)
        ℚP.≤-refl)

  fullMassBelowEnergyProducts :
    fullMass
    ≤ R452.fortyEight
      * R454.triadEnergyProductSum (R456.physicalEnergy velocity)
          (Physical.physicalTriadEnumeration cutoff)
  fullMassBelowEnergyProducts =
    R456.sumDoubleMixedMassBelowEnergyProducts
      P C (Physical.physicalTriadEnumeration cutoff)

  energyProductsBelowSquare = physicalEnumerationEnergyBelowSquare modalEnergy cutoff

  scaledEnergyProductsBelowSquare :
    R452.fortyEight
      * R454.triadEnergyProductSum (R456.physicalEnergy velocity)
          (Physical.physicalTriadEnumeration cutoff)
    ≤ R452.fortyEight * energySquare
  scaledEnergyProductsBelowSquare =
    let
      instance fortyEightNNI : NonNegative R452.fortyEight
      fortyEightNNI = nonNegative R456.fortyEightNN
    in
    ℚP.*-monoˡ-≤-nonNeg R452.fortyEight energyProductsBelowSquare

  globalNonzeroOutputMassBelowEnergySquare :
    selectedMass ≤ R452.fortyEight * energySquare
  globalNonzeroOutputMassBelowEnergySquare =
    ℚP.≤-trans selectedMassBelowFull
      (ℚP.≤-trans fullMassBelowEnergyProducts scaledEnergyProductsBelowSquare)

round462GlobalNonzeroOutputMassPaidOnceByEnergySquare : Bool
round462GlobalNonzeroOutputMassPaidOnceByEnergySquare = true

round462OutputCardinalityTaxIntroduced : Bool
round462OutputCardinalityTaxIntroduced = false

round462UsesLiteralRound39OutputPartition : Bool
round462UsesLiteralRound39OutputPartition = true

round462ContainsPostulate : Bool
round462ContainsPostulate = false

round462PackageAClosed : Bool
round462PackageAClosed = false

round462ClayPromotion : Bool
round462ClayPromotion = false

round462OutputCardinalityTaxIntroducedIsFalse :
  round462OutputCardinalityTaxIntroduced ≡ false
round462OutputCardinalityTaxIntroducedIsFalse = refl

round462ContainsPostulateIsFalse : round462ContainsPostulate ≡ false
round462ContainsPostulateIsFalse = refl
