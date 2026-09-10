module DASHI.Physics.Closure.NSTriadKNWeightedNestedSignedCrossThreeOrbitBidiExact where

------------------------------------------------------------------------
-- WEIGHTED NESTED SLOT -> THREE-ORBIT SIGNED CROSS, BEFORE NORM
--
-- R581 decomposes the literal R584 nested slot fold exactly into four Bony
-- class folds.  The live LH/HL symmetry owner proves the LH and HL folds are
-- equal as VECTORS after the actual slot transform, not merely equal in norm.
-- R573 then applies only fixed linear outer maps (multiplication by i and the
-- outer R294 weight), so the equality and four-way decomposition survive onto
-- the actual nestedWeightedCompanionCell.
--
-- This owner pushes that exact decomposition through R179.realHermitianCross.
-- Hence the scalar consumer itself sees only three independent signed channels:
--
--   2 * LH  +  HH->low  +  comparable.
--
-- No norm, absolute value, Cauchy/Young/Schur estimate, shell count or
-- spacetime majorant is introduced.  The p=0 branch is handled as the literal
-- zero branch already present in R573; normalizedDirection is never required
-- there.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNFourHelicityVectorRecombinationRound576Exact as R576
import DASHI.Physics.Closure.NSTriadKNLiteralFourSignBonyRoutingRound581Exact as R581
import DASHI.Physics.Closure.NSTriadKNNestedSlotBonyClassNormBidiRound584Exact as R584
import DASHI.Physics.Closure.NSTriadKNNestedSlotBonyLHHLNormSymmetryBidiExact as SlotSymmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact as R440

F : C3.RealField _
F = R581.F

module SignedThreeOrbit
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse E mode (Audit.velocity system mode)) where

  module Live = R584.LiveNestedSlot584 W S L H system velocityTransverse
  module Sym = SlotSymmetry.SlotSymmetry W S L H system velocityTransverse

  zero : C3.Complex3 F
  zero = C3.complex3Zero F

  innerItems : Physical.PhysicalTriadIncidence → List Physical.PhysicalTriadIncidence
  innerItems tau =
    Output.physicalOutputFiber (Audit.cutoff system) (Physical.p tau)

  lowHighFold highLowFold highHighToLowFold comparableFold :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  lowHighFold tau =
    R224.foldVector
      (R581.lowHighCell581 (Live.nestedSlotCell584 tau))
      (innerItems tau)
  highLowFold tau =
    R224.foldVector
      (R581.highLowCell581 (Live.nestedSlotCell584 tau))
      (innerItems tau)
  highHighToLowFold tau =
    R224.foldVector
      (R581.highHighToLowCell581 (Live.nestedSlotCell584 tau))
      (innerItems tau)
  comparableFold tau =
    R224.foldVector
      (R581.comparableCell581 (Live.nestedSlotCell584 tau))
      (innerItems tau)

  scaleFour :
    (scalar : C3.Complex F) →
    (a b c d : C3.Complex3 F) →
    C3.complex3Scale scalar (R576.fourVectorTotal a b c d)
    ≡ R576.fourVectorTotal
        (C3.complex3Scale scalar a)
        (C3.complex3Scale scalar b)
        (C3.complex3Scale scalar c)
        (C3.complex3Scale scalar d)
  scaleFour scalar a b c d =
    trans
      (R73.complex3ScaleAdd scalar
        (C3.complex3Add a b) (C3.complex3Add c d))
      (cong₂ C3.complex3Add
        (R73.complex3ScaleAdd scalar a b)
        (R73.complex3ScaleAdd scalar c d))

  weightedClass :
    (Physical.PhysicalTriadIncidence → C3.Complex3 F) →
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedClass classFold tau
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = zero
  ... | false =
    C3.complex3Scale (R294.weight W tau)
      (C3.complex3Scale (C3.complexI F) (classFold tau))

  lowHighWeighted highLowWeighted highHighToLowWeighted comparableWeighted :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  lowHighWeighted = weightedClass lowHighFold
  highLowWeighted = weightedClass highLowFold
  highHighToLowWeighted = weightedClass highHighToLowFold
  comparableWeighted = weightedClass comparableFold

  fourZero : R576.fourVectorTotal zero zero zero zero ≡ zero
  fourZero =
    trans
      (cong₂ C3.complex3Add
        (Algebra.complex3AddZeroRight zero)
        (Algebra.complex3AddZeroRight zero))
      (Algebra.complex3AddZeroRight zero)

  nestedWeightedCellToFourClasses :
    (tau : Physical.PhysicalTriadIncidence) →
    Live.Weighted.nestedWeightedCompanionCell tau
    ≡ R576.fourVectorTotal
        (lowHighWeighted tau)
        (highLowWeighted tau)
        (highHighToLowWeighted tau)
        (comparableWeighted tau)
  nestedWeightedCellToFourClasses tau
      with Output.modeEqual (Physical.p tau) Z3.zeroMode in pDecision
  ... | true = sym fourZero
  ... | false =
    let
      innerDecomposition :
        Live.Weighted.nestedSlotFold tau
        ≡ R576.fourVectorTotal
            (lowHighFold tau)
            (highLowFold tau)
            (highHighToLowFold tau)
            (comparableFold tau)
      innerDecomposition =
        R581.literalFoldToFourClassFolds581
          (Live.nestedSlotCell584 tau) (innerItems tau)

      iScaled :
        C3.complex3Scale (C3.complexI F)
          (Live.Weighted.nestedSlotFold tau)
        ≡ R576.fourVectorTotal
            (C3.complex3Scale (C3.complexI F) (lowHighFold tau))
            (C3.complex3Scale (C3.complexI F) (highLowFold tau))
            (C3.complex3Scale (C3.complexI F) (highHighToLowFold tau))
            (C3.complex3Scale (C3.complexI F) (comparableFold tau))
      iScaled =
        trans
          (cong (C3.complex3Scale (C3.complexI F)) innerDecomposition)
          (scaleFour (C3.complexI F)
            (lowHighFold tau) (highLowFold tau)
            (highHighToLowFold tau) (comparableFold tau))
    in
    trans
      (cong (C3.complex3Scale (R294.weight W tau)) iScaled)
      (scaleFour (R294.weight W tau)
        (C3.complex3Scale (C3.complexI F) (lowHighFold tau))
        (C3.complex3Scale (C3.complexI F) (highLowFold tau))
        (C3.complex3Scale (C3.complexI F) (highHighToLowFold tau))
        (C3.complex3Scale (C3.complexI F) (comparableFold tau)))

  lowHighWeightedEqualsHighLowWeighted :
    (tau : Physical.PhysicalTriadIncidence) →
    lowHighWeighted tau ≡ highLowWeighted tau
  lowHighWeightedEqualsHighLowWeighted tau
      with Output.modeEqual (Physical.p tau) Z3.zeroMode in pDecision
  ... | true = refl
  ... | false =
    let
      pNonzero : Z3.NonZeroMode (Physical.p tau)
      pNonzero = record
        { Z3.notZero = λ pZero →
            Output.falseNotTrue
              (trans (sym pDecision) (Output.modeEqualComplete pZero))
        }

      rawEquality : lowHighFold tau ≡ highLowFold tau
      rawEquality = Sym.nestedSlotLowHighEqualsHighLow tau pNonzero
    in
    cong
      (λ value →
        C3.complex3Scale (R294.weight W tau)
          (C3.complex3Scale (C3.complexI F) value))
      rawEquality

  fourClassSignedCross :
    Physical.PhysicalTriadIncidence → C3.Complex3 F → ℚ
  fourClassSignedCross tau test =
    ( R179.realHermitianCross (lowHighWeighted tau) test
    + R179.realHermitianCross (highLowWeighted tau) test )
    + ( R179.realHermitianCross (highHighToLowWeighted tau) test
      + R179.realHermitianCross (comparableWeighted tau) test )

  threeOrbitSignedCross :
    Physical.PhysicalTriadIncidence → C3.Complex3 F → ℚ
  threeOrbitSignedCross tau test =
    R291.two * R179.realHermitianCross (lowHighWeighted tau) test
    + ( R179.realHermitianCross (highHighToLowWeighted tau) test
      + R179.realHermitianCross (comparableWeighted tau) test )

  nestedWeightedCrossIsFourClassCross :
    (tau : Physical.PhysicalTriadIncidence) →
    (test : C3.Complex3 F) →
    R179.realHermitianCross Live.Weighted.nestedWeightedCompanionCell tau test
    ≡ fourClassSignedCross tau test
  nestedWeightedCrossIsFourClassCross tau test =
    trans
      (cong
        (λ value → R179.realHermitianCross value test)
        (nestedWeightedCellToFourClasses tau))
      (trans
        (R291.realCrossAddLeft
          (C3.complex3Add (lowHighWeighted tau) (highLowWeighted tau))
          (C3.complex3Add (highHighToLowWeighted tau) (comparableWeighted tau))
          test)
        (cong₂ _+_
          (R291.realCrossAddLeft
            (lowHighWeighted tau) (highLowWeighted tau) test)
          (R291.realCrossAddLeft
            (highHighToLowWeighted tau) (comparableWeighted tau) test)))

  fourClassCrossDescendsToThreeOrbit :
    (tau : Physical.PhysicalTriadIncidence) →
    (test : C3.Complex3 F) →
    fourClassSignedCross tau test ≡ threeOrbitSignedCross tau test
  fourClassCrossDescendsToThreeOrbit tau test
      rewrite sym (lowHighWeightedEqualsHighLowWeighted tau) =
    solve
      ( R179.realHermitianCross (lowHighWeighted tau) test
      ∷ R179.realHermitianCross (highHighToLowWeighted tau) test
      ∷ R179.realHermitianCross (comparableWeighted tau) test
      ∷ [])

  nestedWeightedCrossIsThreeOrbitCross :
    (tau : Physical.PhysicalTriadIncidence) →
    (test : C3.Complex3 F) →
    R179.realHermitianCross Live.Weighted.nestedWeightedCompanionCell tau test
    ≡ threeOrbitSignedCross tau test
  nestedWeightedCrossIsThreeOrbitCross tau test =
    trans
      (nestedWeightedCrossIsFourClassCross tau test)
      (fourClassCrossDescendsToThreeOrbit tau test)

  threeOrbitCrossSum :
    List Physical.PhysicalTriadIncidence → C3.Complex3 F → ℚ
  threeOrbitCrossSum [] test = 0ℚ
  threeOrbitCrossSum (tau ∷ rest) test =
    threeOrbitSignedCross tau test + threeOrbitCrossSum rest test

  foldedNestedWeightedCrossIsThreeOrbitSum :
    (items : List Physical.PhysicalTriadIncidence) →
    (test : C3.Complex3 F) →
    R179.realHermitianCross
      (R224.foldVector Live.Weighted.nestedWeightedCompanionCell items)
      test
    ≡ threeOrbitCrossSum items test
  foldedNestedWeightedCrossIsThreeOrbitSum [] test =
    R440.crossZeroLeft test
  foldedNestedWeightedCrossIsThreeOrbitSum (tau ∷ rest) test =
    trans
      (R291.realCrossAddLeft
        (Live.Weighted.nestedWeightedCompanionCell tau)
        (R224.foldVector Live.Weighted.nestedWeightedCompanionCell rest)
        test)
      (cong₂ _+_
        (nestedWeightedCrossIsThreeOrbitCross tau test)
        (foldedNestedWeightedCrossIsThreeOrbitSum rest test))

------------------------------------------------------------------------
-- Status / delayed-lossy-observer firewall.
------------------------------------------------------------------------

weightedNestedCellExactFourClassVectorDecompositionClosed : Bool
weightedNestedCellExactFourClassVectorDecompositionClosed = true

weightedNestedLHHLExactlyEqualBeforeNorm : Bool
weightedNestedLHHLExactlyEqualBeforeNorm = true

signedHermitianConsumerDescendsToThreeBonyOrbits : Bool
signedHermitianConsumerDescendsToThreeBonyOrbits = true

normIntroducedBeforeSignedCross : Bool
normIntroducedBeforeSignedCross = false

absoluteValueIntroducedBeforeSignedCross : Bool
absoluteValueIntroducedBeforeSignedCross = false

cauchySchwarzIntroducedBeforeSignedCross : Bool
cauchySchwarzIntroducedBeforeSignedCross = false

cutoffUniformSignedThreeOrbitBudgetClosed : Bool
cutoffUniformSignedThreeOrbitBudgetClosed = false

clayPromotion : Bool
clayPromotion = false

signedHermitianConsumerDescendsToThreeBonyOrbitsIsTrue :
  signedHermitianConsumerDescendsToThreeBonyOrbits ≡ true
signedHermitianConsumerDescendsToThreeBonyOrbitsIsTrue = refl

normIntroducedBeforeSignedCrossIsFalse :
  normIntroducedBeforeSignedCross ≡ false
normIntroducedBeforeSignedCrossIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
