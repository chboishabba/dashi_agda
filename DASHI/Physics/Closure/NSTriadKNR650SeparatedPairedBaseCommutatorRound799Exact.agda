{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedPairedBaseCommutatorRound799Exact where

------------------------------------------------------------------------
-- ROUND799 / RAW SEPARATED PAIRED BASE ROW = EIGHT TIMES MASKED R230 WORK
--
-- SI-style same-object reduction: identify the vector carrier first.
--
-- On one literal fixed-output fibre F_k let
--
--   M_k = sum_{alpha in F_k} mixedCell(alpha).
--
-- R763's raw paired base row is the spectator fold against FOUR copies of
-- Product(beta)+Product(swap beta).  After attaching the swap-invariant
-- fully-separated mask:
--
--   * spectator bilinearity collapses the alpha-fold to coherentWork(M_k,...);
--   * fourCopies contributes factor 4;
--   * the beta/swap pair contributes factor 2 on the complete output fibre;
--   * R798/R294 converts the masked product-rule fold to the SAME masked R230
--     commutator fold.
--
-- Therefore exactly
--
--   RawB_sep(k) = 8 * W(M_k , C_sep(k)).
--
-- The R763 zero-output mask is intentionally NOT handled here.  R800 routes
-- that exceptional branch while lifting this identity through R39's exact
-- global output-fibre partition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as R106
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFullGramCoherentFoldRound597Exact as R597
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNR650NestedSwapPairProductRuleRound762Exact as R762
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650SeparatedPairedNestedProductRuleRound791Exact as R791
import DASHI.Physics.Closure.NSTriadKNR650SeparatedR230WeightRound798Exact as R798

F : C3.RealField _
F = Rational.rationalRealField

four eight : ℚ
four = 4
eight = 8

module SeparatedBaseCommutator
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Sep =
    R791.SeparatedGlobalPairedNested
      physicalSystem S L H velocityTransverse

  module Pair = Sep.G.P

  system = Field30.finiteSystem physicalSystem
  cutoff = Sep.cutoff
  velocity = Pair.N.Nested.Base.velocity
  forcing = Pair.N.Nested.Base.forcing
  mixedCell = Pair.N.Nested.Base.mixedCell

  maskedProductCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  maskedProductCell beta with R781.ccTouched beta
  ... | true = C3.complex3Zero F
  ... | false =
    R230.productRuleForcingCell S velocity forcing beta

  separatedProductCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  separatedProductCell =
    R294.weightedProductRuleCell
      (R798.separatedWeight F) S velocity forcing

  separatedCommutatorCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  separatedCommutatorCell =
    R294.weightedCommutatorCell
      (R798.separatedWeight F) S velocity forcing

  separatedProductIsMasked :
    (beta : Physical.PhysicalTriadIncidence) →
    separatedProductCell beta ≡ maskedProductCell beta
  separatedProductIsMasked beta
    with R781.ccTouched beta
  ... | true
    rewrite R106.complex3ScaleZeroScalar
              (R230.plusForceMinusVelocity S velocity forcing beta)
          | R106.complex3ScaleZeroScalar
              (R230.plusVelocityMinusForce S velocity forcing beta) =
      Field.complex3AddZeroLeft (C3.complex3Zero F)
  ... | false
    rewrite R106.complex3ScaleOne
              (R230.plusForceMinusVelocity S velocity forcing beta)
          | R106.complex3ScaleOne
              (R230.plusVelocityMinusForce S velocity forcing beta) =
      refl

  maskedPairProductCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  maskedPairProductCell beta =
    C3.complex3Add
      (maskedProductCell beta)
      (maskedProductCell (Symmetry.swapTriad beta))

  maskedPairProductMeaning :
    (beta : Physical.PhysicalTriadIncidence) →
    maskedPairProductCell beta
    ≡
    (case R781.ccTouched beta of λ
      { true → C3.complex3Zero F
      ; false → Pair.Pair.pairedProductRuleCell beta
      })
  maskedPairProductMeaning beta
    rewrite R781.ccTouchedSwapInvariant beta
    with R781.ccTouched beta
  ... | true =
    Field.complex3AddZeroLeft (C3.complex3Zero F)
  ... | false = refl

  mixedFold : Z3.FourierMode → C3.Complex3 F
  mixedFold output =
    R224.foldVector mixedCell (Output.physicalOutputFiber cutoff output)

  productFold : Z3.FourierMode → C3.Complex3 F
  productFold output =
    R224.foldVector separatedProductCell
      (Output.physicalOutputFiber cutoff output)

  commutatorFold : Z3.FourierMode → C3.Complex3 F
  commutatorFold output =
    R224.foldVector separatedCommutatorCell
      (Output.physicalOutputFiber cutoff output)

  rawMaskedPairedBaseRow :
    Physical.PhysicalTriadIncidence → ℚ
  rawMaskedPairedBaseRow beta with R781.ccTouched beta
  ... | true = 0ℚ
  ... | false = Pair.pairedProductRuleOuterRow beta

  rawSeparatedBaseFold : Z3.FourierMode → ℚ
  rawSeparatedBaseFold output =
    Sep.G.P.N.Nested.Base.R38.foldPower
      rawMaskedPairedBaseRow
      (Output.physicalOutputFiber cutoff output)

  workFourCopies :
    (left right : C3.Complex3 F) →
    Work.coherentWork left (R762.fourCopies right)
    ≡ four * Work.coherentWork left right
  workFourCopies left right =
    trans
      (Work.workAddRight left
        (C3.complex3Add right right)
        (C3.complex3Add right right))
      (trans
        (cong₂ _+_
          (Work.workAddRight left right right)
          (Work.workAddRight left right right))
        (solve (Work.coherentWork left right ∷ four ∷ [])))

  outerRowFactors :
    (beta : Physical.PhysicalTriadIncidence) →
    Pair.pairedProductRuleOuterRow beta
    ≡
    Work.coherentWork
      (R224.foldVector mixedCell (Pair.N.Nested.Base.fibre (Physical.k beta)))
      (R762.fourCopies (Pair.Pair.pairedProductRuleCell beta))
  outerRowFactors beta =
    go (Pair.N.Nested.Base.fibre (Physical.k beta))
    where
    right = R762.fourCopies (Pair.Pair.pairedProductRuleCell beta)

    go :
      (items : List Physical.PhysicalTriadIncidence) →
      R762.Pair.NestedSwapPair.pairedProductRuleOuterRow
        physicalSystem S L H velocityTransverse beta
      ≡ Work.coherentWork (R224.foldVector mixedCell items) right
    go items =
      trans
        refl
        (factor items)
      where
      factor :
        (xs : List Physical.PhysicalTriadIncidence) →
        R546.spectatorRow Pair.pairedProductRuleNestedPair beta xs
        ≡ Work.coherentWork (R224.foldVector mixedCell xs) right
      factor [] =
        sym (R597.workZeroLeft right)
      factor (alpha ∷ rest) =
        trans
          (cong
            (Work.coherentWork (mixedCell alpha) right +_)
            (factor rest))
          (sym
            (R597.workAddLeft
              (mixedCell alpha)
              (R224.foldVector mixedCell rest)
              right))

  foldWorkRight :
    (left : C3.Complex3 F) →
    (value : Physical.PhysicalTriadIncidence → C3.Complex3 F) →
    (items : List Physical.PhysicalTriadIncidence) →
    Sep.G.R38.foldPower
      (λ beta → Work.coherentWork left (value beta)) items
    ≡ Work.coherentWork left (R224.foldVector value items)
  foldWorkRight left value [] =
    sym (R597.workZeroRight left)
  foldWorkRight left value (beta ∷ rest) =
    trans
      (cong
        (Work.coherentWork left (value beta) +_)
        (foldWorkRight left value rest))
      (sym
        (Work.workAddRight
          left (value beta) (R224.foldVector value rest)))

  foldMaskedProduct :
    (items : List Physical.PhysicalTriadIncidence) →
    R224.foldVector separatedProductCell items
    ≡ R224.foldVector maskedProductCell items
  foldMaskedProduct [] = refl
  foldMaskedProduct (beta ∷ rest) =
    cong₂ C3.complex3Add
      (separatedProductIsMasked beta)
      (foldMaskedProduct rest)

  pairFoldIsDoubleProductFold :
    (output : Z3.FourierMode) →
    R224.foldVector maskedPairProductCell
      (Output.physicalOutputFiber cutoff output)
    ≡
    C3.complex3Add (productFold output) (productFold output)
  pairFoldIsDoubleProductFold output =
    let
      items = Output.physicalOutputFiber cutoff output

      split :
        R224.foldVector maskedPairProductCell items
        ≡
        C3.complex3Add
          (R224.foldVector maskedProductCell items)
          (R224.foldVector
            (λ beta → maskedProductCell (Symmetry.swapTriad beta)) items)
      split =
        R230.foldAdd
          maskedProductCell
          (λ beta → maskedProductCell (Symmetry.swapTriad beta))
          items

      swapped :
        R224.foldVector
          (λ beta → maskedProductCell (Symmetry.swapTriad beta)) items
        ≡ R224.foldVector maskedProductCell items
      swapped =
        trans
          (sym (R224.foldMap maskedProductCell Symmetry.swapTriad items))
          (R224.foldPermutationInvariant maskedProductCell
            (R224.swapOutputFibrePermutation cutoff output))

      maskedIsProduct :
        R224.foldVector maskedProductCell items
        ≡ productFold output
      maskedIsProduct =
        sym (foldMaskedProduct items)
    in
    trans split
      (trans
        (cong₂ C3.complex3Add refl swapped)
        (cong₂ C3.complex3Add maskedIsProduct maskedIsProduct))

  rawSeparatedBaseIsEightProductWork :
    (output : Z3.FourierMode) →
    rawSeparatedBaseFold output
    ≡ eight * Work.coherentWork (mixedFold output) (productFold output)
  rawSeparatedBaseIsEightProductWork output =
    let
      items = Output.physicalOutputFiber cutoff output
      M = mixedFold output
      P = productFold output

      rowPointwise :
        (beta : Physical.PhysicalTriadIncidence) →
        Physical.k beta ≡ output →
        rawMaskedPairedBaseRow beta
        ≡
        Work.coherentWork M
          (R762.fourCopies (maskedPairProductCell beta))
      rowPointwise beta kEq
        rewrite kEq
        with R781.ccTouched beta
      ... | true =
        trans refl
          (sym
            (trans
              (workFourCopies M (C3.complex3Zero F))
              (solve (four ∷ []))))
      ... | false =
        trans
          (outerRowFactors beta)
          (cong
            (λ selected →
              Work.coherentWork selected
                (R762.fourCopies
                  (Pair.Pair.pairedProductRuleCell beta)))
            refl)

      foldRows :
        Sep.G.R38.foldPower rawMaskedPairedBaseRow items
        ≡
        Sep.G.R38.foldPower
          (λ beta →
            Work.coherentWork M
              (R762.fourCopies (maskedPairProductCell beta)))
          items
      foldRows =
        go items
          (λ beta member → Output.physicalOutputFiberSound member)
        where
        go :
          (xs : List Physical.PhysicalTriadIncidence) →
          ((beta : Physical.PhysicalTriadIncidence) →
            beta DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier.∈ xs →
            Physical.k beta ≡ output) →
          Sep.G.R38.foldPower rawMaskedPairedBaseRow xs
          ≡
          Sep.G.R38.foldPower
            (λ beta →
              Work.coherentWork M
                (R762.fourCopies (maskedPairProductCell beta)))
            xs
        go [] allOutput = refl
        go (beta ∷ rest) allOutput =
          cong₂ _+_
            (rowPointwise beta
              (allOutput beta
                (DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier.here refl)))
            (go rest
              (λ chosen member →
                allOutput chosen
                  (DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier.there
                    member)))

      factorFour :
        Sep.G.R38.foldPower
          (λ beta →
            Work.coherentWork M
              (R762.fourCopies (maskedPairProductCell beta)))
          items
        ≡
        four *
          Sep.G.R38.foldPower
            (λ beta → Work.coherentWork M (maskedPairProductCell beta))
            items
      factorFour =
        go items
        where
        go : (xs : List Physical.PhysicalTriadIncidence) →
          Sep.G.R38.foldPower
            (λ beta →
              Work.coherentWork M
                (R762.fourCopies (maskedPairProductCell beta))) xs
          ≡ four *
            Sep.G.R38.foldPower
              (λ beta → Work.coherentWork M (maskedPairProductCell beta)) xs
        go [] = solve (four ∷ [])
        go (beta ∷ rest) =
          trans
            (cong
              (Work.coherentWork M
                (R762.fourCopies (maskedPairProductCell beta)) +_)
              (go rest))
            (trans
              (cong
                (_+ four *
                  Sep.G.R38.foldPower
                    (λ chosen →
                      Work.coherentWork M (maskedPairProductCell chosen))
                    rest)
                (workFourCopies M (maskedPairProductCell beta)))
              (solve
                ( four
                ∷ Work.coherentWork M (maskedPairProductCell beta)
                ∷ Sep.G.R38.foldPower
                    (λ chosen →
                      Work.coherentWork M (maskedPairProductCell chosen))
                    rest
                ∷ [])))

      pairWork :
        Sep.G.R38.foldPower
          (λ beta → Work.coherentWork M (maskedPairProductCell beta)) items
        ≡
        Work.coherentWork M
          (C3.complex3Add P P)
      pairWork =
        trans
          (foldWorkRight M maskedPairProductCell items)
          (cong (Work.coherentWork M)
            (pairFoldIsDoubleProductFold output))

      doubleWork :
        Work.coherentWork M (C3.complex3Add P P)
        ≡ Work.coherentWork M P + Work.coherentWork M P
      doubleWork = Work.workAddRight M P P
    in
    trans foldRows
      (trans factorFour
        (trans
          (cong (four *_) pairWork)
          (trans
            (cong (four *_) doubleWork)
            (solve (four ∷ eight ∷ Work.coherentWork M P ∷ [])))))

  rawSeparatedBaseIsEightCommutatorWork :
    (output : Z3.FourierMode) →
    rawSeparatedBaseFold output
    ≡ eight * Work.coherentWork (mixedFold output) (commutatorFold output)
  rawSeparatedBaseIsEightCommutatorWork output =
    trans
      (rawSeparatedBaseIsEightProductWork output)
      (cong
        (eight *_)
        (cong
          (Work.coherentWork (mixedFold output))
          (R798.fixedOutputSeparatedProductRuleIsCommutator
            S velocity forcing cutoff output)))

round799RawSeparatedBaseIsEightMaskedR230Work : Bool
round799RawSeparatedBaseIsEightMaskedR230Work = true

round799UsesSIStyleVectorBeforeScalarIdentification : Bool
round799UsesSIStyleVectorBeforeScalarIdentification = true

round799ZeroOutputMaskRoutedSeparately : Bool
round799ZeroOutputMaskRoutedSeparately = true

round799IntroducesEstimate : Bool
round799IntroducesEstimate = false

round799W2Closed : Bool
round799W2Closed = false

round799ClayPromotion : Bool
round799ClayPromotion = false

round799RawSeparatedBaseIsEightMaskedR230WorkIsTrue :
  round799RawSeparatedBaseIsEightMaskedR230Work ≡ true
round799RawSeparatedBaseIsEightMaskedR230WorkIsTrue = refl

round799IntroducesEstimateIsFalse :
  round799IntroducesEstimate ≡ false
round799IntroducesEstimateIsFalse = refl

round799W2ClosedIsFalse :
  round799W2Closed ≡ false
round799W2ClosedIsFalse = refl

round799ClayPromotionIsFalse :
  round799ClayPromotion ≡ false
round799ClayPromotionIsFalse = refl
