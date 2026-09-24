{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650MaskedCompleteTriadOrbitResidueRound696Exact where

------------------------------------------------------------------------
-- ROUND696 / NONZERO GLOBAL COMMUTATOR ON A CYCLICALLY CLOSED FULL CARRIER
--
-- R690/R691 select k != 0, while R38's exact p/q energy-leg permutations act
-- on the COMPLETE physical triad enumeration.  Do not restrict the carrier
-- and then ask it to be cyclically closed.  Instead keep the full carrier and
-- mask the scalar contribution when the selected output is zero.
--
-- Define
--
--   row*(beta) = row(beta)   if k(beta) != 0,
--              = 0          if k(beta) = 0.
--
-- The full masked fold is EXACTLY the R692 nonzero-output commutator pair sum.
-- Since the underlying list is still the complete physical enumeration, R38
-- may reindex row* through pEnergyLeg and qEnergyLeg without any boundary
-- hypothesis.
--
-- Hence the literal three-leg residue
--
--   R_triangle(beta)
--     = row*(beta)
--       + row*(pEnergyLeg beta)
--       + row*(qEnergyLeg beta)
--
-- satisfies
--
--   sum_beta R_triangle(beta)
--     = 3 * [nonzero global commutator pair sum].
--
-- This is an orbit regrouping identity, not a cancellation claim.  It handles
-- zero legs by masking rather than by assuming a mean-zero theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; map)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNF4GlobalOutputFiberPartitionRound39Exact as R39
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorIncidenceExpansionRound692Exact as R692
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorTriadRegroupingRound693Exact as R693

F : C3.RealField _
F = Rational.rationalRealField

three : ℚ
three = 3

module MaskedOrbit
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module E = R692.Expansion physicalSystem S
  module G = R693.Regrouping physicalSystem S

  maskedOuterRow :
    Physical.PhysicalTriadIncidence → ℚ
  maskedOuterRow beta
    with Output.modeEqual (Physical.k beta) Z3.zeroMode
  ... | true = 0ℚ
  ... | false = G.globalOuterRow beta

  selectedOutputPairSum :
    Z3.FourierMode → ℚ
  selectedOutputPairSum output
    with Output.modeEqual output Z3.zeroMode
  ... | true = 0ℚ
  ... | false = E.outputPairIncidenceSum output

  sumSelectedOutputPairs :
    List Z3.FourierMode → ℚ
  sumSelectedOutputPairs [] = 0ℚ
  sumSelectedOutputPairs (output ∷ rest) =
    selectedOutputPairSum output + sumSelectedOutputPairs rest

  selectedOutputSumIsRemoveZeroSum :
    (outputs : List Z3.FourierMode) →
    sumSelectedOutputPairs outputs
    ≡ E.sumOutputPairIncidences (Canonical.removeZero outputs)
  selectedOutputSumIsRemoveZeroSum [] = refl
  selectedOutputSumIsRemoveZeroSum (output ∷ rest)
    with Output.modeEqual output Z3.zeroMode
  ... | true = selectedOutputSumIsRemoveZeroSum rest
  ... | false =
    cong₂ _+_ refl (selectedOutputSumIsRemoveZeroSum rest)

  maskedRowZeroOnZeroFibre :
    (output : Z3.FourierMode) →
    Output.modeEqual output Z3.zeroMode ≡ true →
    (items : List Physical.PhysicalTriadIncidence) →
    ((beta : Physical.PhysicalTriadIncidence) →
      beta Cube.∈ items → beta Cube.∈ E.fibre output) →
    R38.foldPower maskedOuterRow items ≡ 0ℚ
  maskedRowZeroOnZeroFibre output outputZero [] included = refl
  maskedRowZeroOnZeroFibre output outputZero (beta ∷ rest) included =
    let
      headMember = included beta (Cube.here refl)
      tailIncluded =
        λ selected member → included selected (Cube.there member)
      headZero : maskedOuterRow beta ≡ 0ℚ
      headZero
        rewrite Output.physicalOutputFiberSound headMember
              | outputZero = refl
    in
    trans
      (cong₂ _+_
        headZero
        (maskedRowZeroOnZeroFibre
          output outputZero rest tailIncluded))
      (solve [])

  maskedRowGlobalOnNonzeroFibre :
    (output : Z3.FourierMode) →
    Output.modeEqual output Z3.zeroMode ≡ false →
    (items : List Physical.PhysicalTriadIncidence) →
    ((beta : Physical.PhysicalTriadIncidence) →
      beta Cube.∈ items → beta Cube.∈ E.fibre output) →
    R38.foldPower maskedOuterRow items
    ≡ R38.foldPower G.globalOuterRow items
  maskedRowGlobalOnNonzeroFibre output outputNonzero [] included = refl
  maskedRowGlobalOnNonzeroFibre
      output outputNonzero (beta ∷ rest) included =
    let
      headMember = included beta (Cube.here refl)
      tailIncluded =
        λ selected member → included selected (Cube.there member)
      headMeaning :
        maskedOuterRow beta ≡ G.globalOuterRow beta
      headMeaning
        rewrite Output.physicalOutputFiberSound headMember
              | outputNonzero = refl
    in
    cong₂ _+_
      headMeaning
      (maskedRowGlobalOnNonzeroFibre
        output outputNonzero rest tailIncluded)

  selectedOutputPairSumIsMaskedFibreFold :
    (output : Z3.FourierMode) →
    selectedOutputPairSum output
    ≡ R38.foldPower maskedOuterRow (E.fibre output)
  selectedOutputPairSumIsMaskedFibreFold output
    with Output.modeEqual output Z3.zeroMode in decision
  ... | true =
    sym
      (maskedRowZeroOnZeroFibre
        output decision (E.fibre output)
        (λ beta member → member))
  ... | false =
    trans
      (G.outputPairSumIsGlobalRowFold output)
      (sym
        (maskedRowGlobalOnNonzeroFibre
          output decision (E.fibre output)
          (λ beta member → member)))

  sumSelectedOutputsIsConcatMaskedFold :
    (outputs : List Z3.FourierMode) →
    sumSelectedOutputPairs outputs
    ≡
    R38.foldPower maskedOuterRow
      (R39.concatOutputFibers E.cutoff outputs)
  sumSelectedOutputsIsConcatMaskedFold [] = refl
  sumSelectedOutputsIsConcatMaskedFold (output ∷ rest) =
    trans
      (cong₂ _+_
        (selectedOutputPairSumIsMaskedFibreFold output)
        (sumSelectedOutputsIsConcatMaskedFold rest))
      (sym
        (R39.foldAppend
          maskedOuterRow
          (E.fibre output)
          (R39.concatOutputFibers E.cutoff rest)))

  nonzeroGlobalPairSumIsFullMaskedFold :
    E.nonzeroGlobalPairIncidenceSum
    ≡
    R38.foldPower maskedOuterRow
      (Physical.physicalTriadEnumeration E.cutoff)
  nonzeroGlobalPairSumIsFullMaskedFold =
    trans
      (sym
        (selectedOutputSumIsRemoveZeroSum
          (Cube.cutoffModes E.cutoff)))
      (trans
        (sumSelectedOutputsIsConcatMaskedFold
          (Cube.cutoffModes E.cutoff))
        (R38.foldPermutationInvariant
          maskedOuterRow
          (R39.literalOutputPartitionPermutation E.cutoff)))

  maskedFoldPEnergyInvariant :
    R38.foldPower maskedOuterRow
      (Physical.physicalTriadEnumeration E.cutoff)
    ≡
    R38.foldPower
      (λ beta → maskedOuterRow (Orbit.pEnergyLeg beta))
      (Physical.physicalTriadEnumeration E.cutoff)
  maskedFoldPEnergyInvariant =
    trans
      (sym
        (R38.foldPermutationInvariant
          maskedOuterRow
          (R38.pEnergyLegEnumerationPermutation E.cutoff)))
      (R38.foldMap
        maskedOuterRow Orbit.pEnergyLeg
        (Physical.physicalTriadEnumeration E.cutoff))

  maskedFoldQEnergyInvariant :
    R38.foldPower maskedOuterRow
      (Physical.physicalTriadEnumeration E.cutoff)
    ≡
    R38.foldPower
      (λ beta → maskedOuterRow (Orbit.qEnergyLeg beta))
      (Physical.physicalTriadEnumeration E.cutoff)
  maskedFoldQEnergyInvariant =
    trans
      (sym
        (R38.foldPermutationInvariant
          maskedOuterRow
          (R38.qEnergyLegEnumerationPermutation E.cutoff)))
      (R38.foldMap
        maskedOuterRow Orbit.qEnergyLeg
        (Physical.physicalTriadEnumeration E.cutoff))

  triadOrbitResidue :
    Physical.PhysicalTriadIncidence → ℚ
  triadOrbitResidue beta =
    maskedOuterRow beta
      + maskedOuterRow (Orbit.pEnergyLeg beta)
      + maskedOuterRow (Orbit.qEnergyLeg beta)

  foldTriadOrbitResidue :
    (items : List Physical.PhysicalTriadIncidence) →
    R38.foldPower triadOrbitResidue items
    ≡
      R38.foldPower maskedOuterRow items
      + R38.foldPower (λ beta → maskedOuterRow (Orbit.pEnergyLeg beta)) items
      + R38.foldPower (λ beta → maskedOuterRow (Orbit.qEnergyLeg beta)) items
  foldTriadOrbitResidue [] = solve []
  foldTriadOrbitResidue (beta ∷ rest) =
    trans
      (cong
        (triadOrbitResidue beta +_)
        (foldTriadOrbitResidue rest))
      (solve
        ( maskedOuterRow beta
        ∷ maskedOuterRow (Orbit.pEnergyLeg beta)
        ∷ maskedOuterRow (Orbit.qEnergyLeg beta)
        ∷ R38.foldPower maskedOuterRow rest
        ∷ R38.foldPower
            (λ selected → maskedOuterRow (Orbit.pEnergyLeg selected)) rest
        ∷ R38.foldPower
            (λ selected → maskedOuterRow (Orbit.qEnergyLeg selected)) rest
        ∷ []))

  completeTriadOrbitResidueIsThreeSelectedCommutator :
    R38.foldPower triadOrbitResidue
      (Physical.physicalTriadEnumeration E.cutoff)
    ≡ three * E.nonzeroGlobalPairIncidenceSum
  completeTriadOrbitResidueIsThreeSelectedCommutator =
    let
      items = Physical.physicalTriadEnumeration E.cutoff
      selected = E.nonzeroGlobalPairIncidenceSum
      masked = R38.foldPower maskedOuterRow items
      pFold =
        R38.foldPower
          (λ beta → maskedOuterRow (Orbit.pEnergyLeg beta)) items
      qFold =
        R38.foldPower
          (λ beta → maskedOuterRow (Orbit.qEnergyLeg beta)) items
      selectedMasked : selected ≡ masked
      selectedMasked = nonzeroGlobalPairSumIsFullMaskedFold
      pMeaning : masked ≡ pFold
      pMeaning = maskedFoldPEnergyInvariant
      qMeaning : masked ≡ qFold
      qMeaning = maskedFoldQEnergyInvariant
    in
    trans
      (foldTriadOrbitResidue items)
      (trans
        (cong₂ _+_
          (cong₂ _+_
            (sym selectedMasked)
            (trans (sym pMeaning) (sym selectedMasked)))
          (trans (sym qMeaning) (sym selectedMasked)))
        (solve (selected ∷ [])))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round696NonzeroSelectionMovedFromCarrierToScalarMask : Bool
round696NonzeroSelectionMovedFromCarrierToScalarMask = true

round696CompletePhysicalCarrierRetainedForCyclicRegrouping : Bool
round696CompletePhysicalCarrierRetainedForCyclicRegrouping = true

round696ZeroLegBoundaryNeedsMeanZeroAssumption : Bool
round696ZeroLegBoundaryNeedsMeanZeroAssumption = false

round696MaskedFullFoldEqualsR692NonzeroGlobalCommutator : Bool
round696MaskedFullFoldEqualsR692NonzeroGlobalCommutator = true

round696ThreeLegOrbitResidueMultiplicityExact : Bool
round696ThreeLegOrbitResidueMultiplicityExact = true

round696OrbitResiduePointwiseZero : Bool
round696OrbitResiduePointwiseZero = false

round696OrbitResidueSignedUniformPaymentClosed : Bool
round696OrbitResidueSignedUniformPaymentClosed = false

round696IntroducesEstimate : Bool
round696IntroducesEstimate = false

round696ClayPromotion : Bool
round696ClayPromotion = false

round696NonzeroSelectionMovedFromCarrierToScalarMaskIsTrue :
  round696NonzeroSelectionMovedFromCarrierToScalarMask ≡ true
round696NonzeroSelectionMovedFromCarrierToScalarMaskIsTrue = refl

round696CompletePhysicalCarrierRetainedForCyclicRegroupingIsTrue :
  round696CompletePhysicalCarrierRetainedForCyclicRegrouping ≡ true
round696CompletePhysicalCarrierRetainedForCyclicRegroupingIsTrue = refl

round696ZeroLegBoundaryNeedsMeanZeroAssumptionIsFalse :
  round696ZeroLegBoundaryNeedsMeanZeroAssumption ≡ false
round696ZeroLegBoundaryNeedsMeanZeroAssumptionIsFalse = refl

round696MaskedFullFoldEqualsR692NonzeroGlobalCommutatorIsTrue :
  round696MaskedFullFoldEqualsR692NonzeroGlobalCommutator ≡ true
round696MaskedFullFoldEqualsR692NonzeroGlobalCommutatorIsTrue = refl

round696ThreeLegOrbitResidueMultiplicityExactIsTrue :
  round696ThreeLegOrbitResidueMultiplicityExact ≡ true
round696ThreeLegOrbitResidueMultiplicityExactIsTrue = refl

round696OrbitResiduePointwiseZeroIsFalse :
  round696OrbitResiduePointwiseZero ≡ false
round696OrbitResiduePointwiseZeroIsFalse = refl

round696OrbitResidueSignedUniformPaymentClosedIsFalse :
  round696OrbitResidueSignedUniformPaymentClosed ≡ false
round696OrbitResidueSignedUniformPaymentClosedIsFalse = refl

round696IntroducesEstimateIsFalse :
  round696IntroducesEstimate ≡ false
round696IntroducesEstimateIsFalse = refl

round696ClayPromotionIsFalse :
  round696ClayPromotion ≡ false
round696ClayPromotionIsFalse = refl
