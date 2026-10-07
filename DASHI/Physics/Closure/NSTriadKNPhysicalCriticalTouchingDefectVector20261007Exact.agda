module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectVector20261007Exact where

------------------------------------------------------------------------
-- POSITIVE B4 / CORE-NONCORE DEFECT -> ONE COHERENT VECTOR RESIDUAL
--
-- The previous max-cut puts the remaining defect exactly on two bipartite
-- covariance sums.  Because every live work scalar is
--
--   w_tau = 2 Re <M , A_tau>,
--
-- the bipartite four-aggregate expression is itself one coherent work.  This
-- owner constructs that vector literally and proves
--
--   defect = - coherentWork M R_defect.
--
-- No absolute value or estimate is used.  The surviving B4 analysis is now a
-- norm/geometry payment for one explicit vector residual (or a sharper signed
-- estimate on the same pairing), not an eight-scalar-moment problem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFiniteBipartiteCovarianceExact as Bip
import DASHI.Physics.Closure.NSTriadKNFixedOutputCenteredMultiplierVectorCovarianceExact as Vector
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianCriticalRegionFilteredExact as Filtered
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingDefectBipartite20261007Exact as Defect
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalTouchingPrincipalDefectRows20261007Exact as SplitRows
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as RateLive

F : C3.RealField _
F = Rational.rationalRealField

bipartiteResidualVector :
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence →
  C3.Complex3 F
bipartiteResidualVector rate value left right =
  let
    nL = Pair.natAsRational (length left)
    nR = Pair.natAsRational (length right)
    rL = Pair.rateSum rate left
    rR = Pair.rateSum rate right
    wL = Vector.weightedVectorSum rate value left
    wR = Vector.weightedVectorSum rate value right
    vL = R224.foldVector value left
    vR = R224.foldVector value right
  in
  C3.complex3Add
    (R291.realScale nR wL)
    (C3.complex3Add
      (R291.realScale nL wR)
      (C3.complex3Add
        (R291.realScale (0ℚ - rL) vR)
        (R291.realScale (0ℚ - rR) vL)))

bipartiteCovarianceIsVectorWork :
  (mixed : C3.Complex3 F) →
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (left right : List Physical.PhysicalTriadIncidence) →
  Bip.bipartitePairSum rate (Pair.cellWork mixed value) left right
  ≡ Work.coherentWork mixed
      (bipartiteResidualVector rate value left right)
bipartiteCovarianceIsVectorWork mixed rate value left right =
  let
    work = Pair.cellWork mixed value
    nL = Pair.natAsRational (length left)
    nR = Pair.natAsRational (length right)
    rL = Pair.rateSum rate left
    rR = Pair.rateSum rate right
    weightedL = Vector.weightedVectorSum rate value left
    weightedR = Vector.weightedVectorSum rate value right
    foldL = R224.foldVector value left
    foldR = R224.foldVector value right
    scalarWeightedL = Pair.weightedWorkSum rate work left
    scalarWeightedR = Pair.weightedWorkSum rate work right
    scalarWorkL = Pair.workSum work left
    scalarWorkR = Pair.workSum work right

    closed :
      Bip.bipartitePairSum rate work left right
      ≡ nR * scalarWeightedL + nL * scalarWeightedR
        - rL * scalarWorkR - rR * scalarWorkL
    closed = Bip.bipartiteClosedForm rate work left right

    expanded :
      Work.coherentWork mixed
        (bipartiteResidualVector rate value left right)
      ≡ nR * Work.coherentWork mixed weightedL
        + (nL * Work.coherentWork mixed weightedR
          + ((0ℚ - rL) * Work.coherentWork mixed foldR
            + (0ℚ - rR) * Work.coherentWork mixed foldL))
    expanded =
      trans
        (Work.workAddRight mixed
          (R291.realScale nR weightedL)
          (C3.complex3Add
            (R291.realScale nL weightedR)
            (C3.complex3Add
              (R291.realScale (0ℚ - rL) foldR)
              (R291.realScale (0ℚ - rR) foldL))))
        (cong₂ _+_
          (Work.workScaleRight nR mixed weightedL)
          (trans
            (Work.workAddRight mixed
              (R291.realScale nL weightedR)
              (C3.complex3Add
                (R291.realScale (0ℚ - rL) foldR)
                (R291.realScale (0ℚ - rR) foldL)))
            (cong₂ _+_
              (Work.workScaleRight nL mixed weightedR)
              (trans
                (Work.workAddRight mixed
                  (R291.realScale (0ℚ - rL) foldR)
                  (R291.realScale (0ℚ - rR) foldL))
                (cong₂ _+_
                  (Work.workScaleRight (0ℚ - rL) mixed foldR)
                  (Work.workScaleRight (0ℚ - rR) mixed foldL))))))

    weightedLMeaning :
      Work.coherentWork mixed weightedL ≡ scalarWeightedL
    weightedLMeaning = Vector.weightedVectorWorkMeaning mixed rate value left

    weightedRMeaning :
      Work.coherentWork mixed weightedR ≡ scalarWeightedR
    weightedRMeaning = Vector.weightedVectorWorkMeaning mixed rate value right

    workLMeaning :
      Work.coherentWork mixed foldL ≡ scalarWorkL
    workLMeaning = sym (Pair.workSumAgainstFold mixed value left)

    workRMeaning :
      Work.coherentWork mixed foldR ≡ scalarWorkR
    workRMeaning = sym (Pair.workSumAgainstFold mixed value right)

    normalized :
      nR * Work.coherentWork mixed weightedL
        + (nL * Work.coherentWork mixed weightedR
          + ((0ℚ - rL) * Work.coherentWork mixed foldR
            + (0ℚ - rR) * Work.coherentWork mixed foldL))
      ≡ nR * scalarWeightedL + nL * scalarWeightedR
        - rL * scalarWorkR - rR * scalarWorkL
    normalized
      rewrite weightedLMeaning | weightedRMeaning
            | workLMeaning | workRMeaning =
      solve (nL ∷ nR ∷ rL ∷ rR ∷ scalarWeightedL ∷ scalarWeightedR
        ∷ scalarWorkL ∷ scalarWorkR ∷ [])
  in
  trans closed (sym (trans expanded normalized))

defectResidualVector :
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence →
  C3.Complex3 F
defectResidualVector rate value items =
  C3.complex3Add
    (bipartiteResidualVector rate value
      (Filtered.deepFarLowItems items)
      (Filtered.criticalCoreItems items))
    (bipartiteResidualVector rate value
      (Filtered.deepHighHighItems items)
      (Filtered.criticalCoreItems items))

defectCovarianceIsVectorWork :
  (mixed : C3.Complex3 F) →
  (rate : Physical.PhysicalTriadIncidence → ℚ) →
  (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  Defect.defectCovariance rate (Pair.cellWork mixed value) items
  ≡ Work.coherentWork mixed (defectResidualVector rate value items)
defectCovarianceIsVectorWork mixed rate value items =
  trans
    (cong₂ _+_
      (bipartiteCovarianceIsVectorWork mixed rate value
        (Filtered.deepFarLowItems items)
        (Filtered.criticalCoreItems items))
      (bipartiteCovarianceIsVectorWork mixed rate value
        (Filtered.deepHighHighItems items)
        (Filtered.criticalCoreItems items)))
    (sym
      (Work.workAddRight mixed
        (bipartiteResidualVector rate value
          (Filtered.deepFarLowItems items)
          (Filtered.criticalCoreItems items))
        (bipartiteResidualVector rate value
          (Filtered.deepHighHighItems items)
          (Filtered.criticalCoreItems items))))

module LiveDefectVector
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Rate = RateLive.LiveBony physicalSystem S output
  module R = SplitRows.LivePrincipalDefect physicalSystem S output
  module D = Defect.LiveDefectBipartite physicalSystem S output

  residual : C3.Complex3 F
  residual = defectResidualVector Rate.inputMass Live.value R.items

  defectIsNegativeVectorWork :
    R.defect ≡ 0ℚ - Work.coherentWork (Live.mixed output) residual
  defectIsNegativeVectorWork =
    trans
      D.defectIsNegativeBipartite
      (cong (0ℚ -_)
        (defectCovarianceIsVectorWork
          (Live.mixed output) Rate.inputMass Live.value R.items))

b4DefectOneVectorNormalFormClosed : Bool
b4DefectOneVectorNormalFormClosed = true

b4DefectVectorNormalFormIntroducesAbsoluteValue : Bool
b4DefectVectorNormalFormIntroducesAbsoluteValue = false

b4DefectVectorNormPaymentClosed : Bool
b4DefectVectorNormPaymentClosed = false

clayPromotion : Bool
clayPromotion = false

b4DefectOneVectorNormalFormClosedIsTrue :
  b4DefectOneVectorNormalFormClosed ≡ true
b4DefectOneVectorNormalFormClosedIsTrue = refl

b4DefectVectorNormalFormIntroducesAbsoluteValueIsFalse :
  b4DefectVectorNormalFormIntroducesAbsoluteValue ≡ false
b4DefectVectorNormalFormIntroducesAbsoluteValueIsFalse = refl

b4DefectVectorNormPaymentClosedIsFalse :
  b4DefectVectorNormPaymentClosed ≡ false
b4DefectVectorNormPaymentClosedIsFalse = refl
