module DASHI.Physics.Closure.NSTriadKNWeightedHelicalGramOperatorSplitRound475Exact where

------------------------------------------------------------------------
-- ROUND475 / LITERAL WEIGHTED PHYSICAL GRAM -> TWO HELICAL SCALAR BLOCKS
--
-- R473 installs arbitrary rational coefficients on the literal R180/R383
-- signed Gram carrier. R474 proves exact ++/-- splitting for any same-output
-- transverse cell list. This owner closes the remaining mass/same-object seam:
--
--   * rational scaling preserves transversality;
--   * R179 polarization + R287 mixed-helicity orthogonality give the concrete
--     rational L2 Pythagoras identity;
--   * both identities propagate through the finite weighted list.
--
-- Therefore R471.TwoPolarizationSplit is inhabited on the ACTUAL R473 weighted
-- Gram operator. The only remaining analytic leaves are the two scalar
-- same-helicity GramOperatorBound certificates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNGramDebtPairExpansionRound383Exact as R383
import DASHI.Physics.Closure.NSTriadKNWaleffeOutputHelicityGramRound287Exact as R287
import DASHI.Physics.Closure.NSTriadKNGramOperatorBoundConsumerRound471Exact as R471
import DASHI.Physics.Closure.NSTriadKNWeightedPhysicalGramOperatorCarrierRound473Exact as R473
import DASHI.Physics.Closure.NSTriadKNHelicalSignedGramSplitRound474Exact as R474

F : C3.RealField _
F = Rational.rationalRealField

scalePreservesTransverse :
  (E : C3.IntegerEmbedding F) →
  (k : Z3.FourierMode) →
  (coefficient : ℚ) →
  (value : C3.Complex3 F) →
  Helical.Transverse E k value →
  Helical.Transverse E k
    (C3.complex3Scale (C3.realEmbed F coefficient) value)
scalePreservesTransverse E k coefficient value transverse =
  let scalar = C3.realEmbed F coefficient in
  trans
    (Scaling.bilinearDot3ScaleRight scalar (C3.modeVector E k) value)
    (trans
      (cong (C3.complexMultiply scalar) transverse)
      (Field.complexMultiplyZeroRight scalar))

weightedCellsTransverse :
  (E : C3.IntegerEmbedding F) →
  (k : Z3.FourierMode) →
  (coefficients : List ℚ) →
  (cells : List (C3.Complex3 F)) →
  R474.AllTransverse E k cells →
  R474.AllTransverse E k (R473.weightedCells coefficients cells)
weightedCellsTransverse E k [] cells cellsT = R474.transverse[]
weightedCellsTransverse E k (coefficient ∷ coefficients) [] R474.transverse[] =
  R474.transverse[]
weightedCellsTransverse E k (coefficient ∷ coefficients) (cell ∷ cells)
    (R474.transverse∷ cellT cellsT) =
  R474.transverse∷
    (scalePreservesTransverse E k coefficient cell cellT)
    (weightedCellsTransverse E k coefficients cells cellsT)

l2NormHelicalSplit :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (k : Z3.FourierMode) →
  (value : C3.Complex3 F) →
  Helical.Transverse E k value →
  L2.complex3NormSquared value
  ≡ L2.complex3NormSquared (R474.plusCell E I S k value)
      + L2.complex3NormSquared (R474.minusCell E I S k value)
l2NormHelicalSplit E I S L k value transverse =
  let
    plus = R474.plusCell E I S k value
    minus = R474.minusCell E I S k value

    decomposition : C3.complex3Add plus minus ≡ value
    decomposition = Helical.velocityHelicalDecomposition L k value transverse

    mixedZero : R179.realHermitianCross plus minus ≡ 0ℚ
    mixedZero = R287.outputPlusMinusRealGramZero E I S L k value value

    polarized :
      L2.complex3NormSquared (C3.complex3Add plus minus)
      ≡ L2.complex3NormSquared plus
          + L2.complex3NormSquared minus
    polarized =
      trans
        (R179.complex3Polarization plus minus)
        (rewriteMixed plus minus mixedZero)
  in
  trans
    (cong L2.complex3NormSquared (sym decomposition))
    polarized
  where
  rewriteMixed :
    (plus minus : C3.Complex3 F) →
    R179.realHermitianCross plus minus ≡ 0ℚ →
    L2.complex3NormSquared plus + L2.complex3NormSquared minus
      + R179.two * R179.realHermitianCross plus minus
    ≡ L2.complex3NormSquared plus + L2.complex3NormSquared minus
  rewriteMixed plus minus mixedZero rewrite mixedZero =
    solve
      (L2.complex3NormSquared plus
        ∷ L2.complex3NormSquared minus ∷ R179.two ∷ [])

cellMassHelicalSplit :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (k : Z3.FourierMode) →
  (cells : List (C3.Complex3 F)) →
  R474.AllTransverse E k cells →
  R180.cellMassSum cells
  ≡ R180.cellMassSum (R474.mapPlus E I S k cells)
      + R180.cellMassSum (R474.mapMinus E I S k cells)
cellMassHelicalSplit E I S L k [] R474.transverse[] = solve []
cellMassHelicalSplit E I S L k (cell ∷ cells)
    (R474.transverse∷ cellT cellsT) =
  let
    head = l2NormHelicalSplit E I S L k cell cellT
    tail = cellMassHelicalSplit E I S L k cells cellsT

    hp = L2.complex3NormSquared (R474.plusCell E I S k cell)
    hm = L2.complex3NormSquared (R474.minusCell E I S k cell)
    tp = R180.cellMassSum (R474.mapPlus E I S k cells)
    tm = R180.cellMassSum (R474.mapMinus E I S k cells)
  in
  trans
    (cong₂ _+_ head tail)
    (solve (hp ∷ hm ∷ tp ∷ tm ∷ []))

weightedPlusGram :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Helical.HelicalModeScalars F →
  Z3.FourierMode →
  List (C3.Complex3 F) → List ℚ → ℚ
weightedPlusGram E I S k cells coefficients =
  R383.allPairSum
    (R474.mapPlus E I S k (R473.weightedCells coefficients cells))

weightedMinusGram :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Helical.HelicalModeScalars F →
  Z3.FourierMode →
  List (C3.Complex3 F) → List ℚ → ℚ
weightedMinusGram E I S k cells coefficients =
  R383.allPairSum
    (R474.mapMinus E I S k (R473.weightedCells coefficients cells))

weightedPlusMass :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Helical.HelicalModeScalars F →
  Z3.FourierMode →
  List (C3.Complex3 F) → List ℚ → ℚ
weightedPlusMass E I S k cells coefficients =
  R180.cellMassSum
    (R474.mapPlus E I S k (R473.weightedCells coefficients cells))

weightedMinusMass :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  Helical.HelicalModeScalars F →
  Z3.FourierMode →
  List (C3.Complex3 F) → List ℚ → ℚ
weightedMinusMass E I S k cells coefficients =
  R180.cellMassSum
    (R474.mapMinus E I S k (R473.weightedCells coefficients cells))

weightedPhysicalHelicalSplit :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (k : Z3.FourierMode) →
  (cells : List (C3.Complex3 F)) →
  R474.AllTransverse E k cells →
  R471.TwoPolarizationSplit
    (List ℚ)
    (R473.weightedSignedGram cells)
    (weightedPlusGram E I S k cells)
    (weightedMinusGram E I S k cells)
    (R473.weightedCellMass cells)
    (weightedPlusMass E I S k cells)
    (weightedMinusMass E I S k cells)
weightedPhysicalHelicalSplit E I S L k cells cellsT = record
  { R471.gramSplit = gramSplit
  ; R471.massSplit = massSplit
  }
  where
  gramSplit : ∀ coefficients →
    R473.weightedSignedGram cells coefficients
    ≡ weightedPlusGram E I S k cells coefficients
      + weightedMinusGram E I S k cells coefficients
  gramSplit coefficients =
    R474.allPairSumHelicalSplit E I S L k
      (R473.weightedCells coefficients cells)
      (weightedCellsTransverse E k coefficients cells cellsT)

  massSplit : ∀ coefficients →
    R473.weightedCellMass cells coefficients
    ≡ weightedPlusMass E I S k cells coefficients
      + weightedMinusMass E I S k cells coefficients
  massSplit coefficients =
    cellMassHelicalSplit E I S L k
      (R473.weightedCells coefficients cells)
      (weightedCellsTransverse E k coefficients cells cellsT)

helicalScalarBoundsCompileToPhysicalGramOperator :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (k : Z3.FourierMode) →
  (cells : List (C3.Complex3 F)) →
  (cellsT : R474.AllTransverse E k cells) →
  (A : ℚ) →
  R471.GramOperatorBound
    (List ℚ)
    (weightedPlusGram E I S k cells)
    (weightedPlusMass E I S k cells)
    A →
  R471.GramOperatorBound
    (List ℚ)
    (weightedMinusGram E I S k cells)
    (weightedMinusMass E I S k cells)
    A →
  R473.PhysicalSignedGramOperatorBound cells A
helicalScalarBoundsCompileToPhysicalGramOperator
    E I S L k cells cellsT A plusBound minusBound =
  R471.twoPolarizationBoundsCompile
    (weightedPhysicalHelicalSplit E I S L k cells cellsT)
    plusBound minusBound

round475WeightedTransversalityClosed : Bool
round475WeightedTransversalityClosed = true

round475ConcreteL2MassSplitClosed : Bool
round475ConcreteL2MassSplitClosed = true

round475WeightedSignedGramSplitClosed : Bool
round475WeightedSignedGramSplitClosed = true

round475TwoScalarBoundsCompileToPhysicalGramOperator : Bool
round475TwoScalarBoundsCompileToPhysicalGramOperator = true

round475PhysicalPlusScalarBoundClosed : Bool
round475PhysicalPlusScalarBoundClosed = false

round475PhysicalMinusScalarBoundClosed : Bool
round475PhysicalMinusScalarBoundClosed = false

round475PackageAClosed : Bool
round475PackageAClosed = false

round475ClayPromotion : Bool
round475ClayPromotion = false

round475PhysicalPlusScalarBoundClosedIsFalse :
  round475PhysicalPlusScalarBoundClosed ≡ false
round475PhysicalPlusScalarBoundClosedIsFalse = refl

round475PhysicalMinusScalarBoundClosedIsFalse :
  round475PhysicalMinusScalarBoundClosed ≡ false
round475PhysicalMinusScalarBoundClosedIsFalse = refl
