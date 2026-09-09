module DASHI.Physics.Closure.NSTriadKNGlobalDiagonalReducedNormalFormRound555Exact where

------------------------------------------------------------------------
-- ROUND555 / GLOBAL OUTPUT AGGREGATION OF THE DIAGONAL-REDUCED NORMAL FORM
--
-- R398's global pair list is literally the concatenation of R397/R396 output
-- pair lists.  Consume the SAME local positivity witnesses stored by R398 and
-- aggregate the R547+R550 fixed-output identity over a finite list of nonzero
-- outputs.  No proof-irrelevance step and no analytic estimate is used.
--
-- Result:
--
--   2 * globalWeightedRemainder
--     = (globalFactoredFull - globalSelfGram) - globalSelfFluxTangent.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (_++_)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNFibreLocalR378GlobalInstantaneousGramFluxRound398Exact as R398
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNLiteralR406CommutatorDiagonalNormalFormRound547Exact as R547
import DASHI.Physics.Closure.NSTriadKNLiteralDiagonalSumDecompositionRound550Exact as R550

F : C3.RealField _
F = Rational.rationalRealField

module GlobalReduced
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (P : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.velocityAt
        (Field30.finiteSystem physicalSystem)))
    (viscosityPositive : Positive (Field30.viscosity physicalSystem)) where

  module G = R398.GlobalFluxLocal physicalSystem S L H P
  module NF = R547.NormalForm physicalSystem S

  data OutputsNonzero : List Z3.FourierMode → Set where
    nonzeroNil : OutputsNonzero []
    nonzeroCons :
      ∀ {output outputs} →
      Z3.NonZeroMode output →
      OutputsNonzero outputs →
      OutputsNonzero (output ∷ outputs)

  globalFactoredFull :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    OutputsNonzero outputs → ℚ
  globalFactoredFull cutoff [] nonzeroNil = 0ℚ
  globalFactoredFull cutoff (output ∷ outputs)
      (nonzeroCons outputNonzero tailNonzero) =
    NF.factoredFull output
      (DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber.physicalOutputFiber
        cutoff output)
    + globalFactoredFull cutoff outputs tailNonzero

  globalSelfGram :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    OutputsNonzero outputs → ℚ
  globalSelfGram cutoff [] nonzeroNil = 0ℚ
  globalSelfGram cutoff (output ∷ outputs)
      (nonzeroCons outputNonzero tailNonzero) =
    let
      module D = R550.LiteralDiagonal
        physicalSystem S viscosityPositive cutoff output outputNonzero
    in
    D.literalSelfGramSum + globalSelfGram cutoff outputs tailNonzero

  globalSelfFluxTangent :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    OutputsNonzero outputs → ℚ
  globalSelfFluxTangent cutoff [] nonzeroNil = 0ℚ
  globalSelfFluxTangent cutoff (output ∷ outputs)
      (nonzeroCons outputNonzero tailNonzero) =
    let
      module D = R550.LiteralDiagonal
        physicalSystem S viscosityPositive cutoff output outputNonzero
    in
    D.literalSelfFluxTangentSum
      + globalSelfFluxTangent cutoff outputs tailNonzero

  globalRemainderAppend :
    (left right : List DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact.DampedGramPair) →
    R385.sumWeightedRemainder (left ++ right)
    ≡ R385.sumWeightedRemainder left + R385.sumWeightedRemainder right
  globalRemainderAppend [] right = refl
  globalRemainderAppend (pair ∷ rest) right
    rewrite globalRemainderAppend rest right = refl

  globalDiagonalReducedNormalForm :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    (positive : G.OutputFibresPositiveOn cutoff outputs) →
    (nonzero : OutputsNonzero outputs) →
    R539.two * R385.sumWeightedRemainder
      (G.globalPairs cutoff outputs positive)
    ≡
    (globalFactoredFull cutoff outputs nonzero
      - globalSelfGram cutoff outputs nonzero)
      - globalSelfFluxTangent cutoff outputs nonzero
  globalDiagonalReducedNormalForm cutoff [] G.positiveOutputsNil nonzeroNil =
    solve []
  globalDiagonalReducedNormalForm cutoff (output ∷ outputs)
      (G.positiveOutputsCons headPositive tailPositive)
      (nonzeroCons outputNonzero tailNonzero) =
    let
      module D = R550.LiteralDiagonal
        physicalSystem S viscosityPositive cutoff output outputNonzero

      headRemainder =
        R385.sumWeightedRemainder
          (NF.O.E.allR290Pairs D.fibre headPositive)

      headNormal :
        R539.two * headRemainder
        ≡
        (NF.factoredFull output D.fibre - D.literalSelfGramSum)
          - D.literalSelfFluxTangentSum
      headNormal
        rewrite NF.factoredFullIsDiagonalPlusTwoLiteralRemainder
          output headPositive
              | D.literalDiagonalSumDecomposes =
        solve
          (D.literalSelfGramSum
            ∷ D.literalSelfFluxTangentSum
            ∷ headRemainder
            ∷ [])

      tailNormal =
        globalDiagonalReducedNormalForm
          cutoff outputs tailPositive tailNonzero
    in
    trans
      (cong
        (R539.two *_)
        (globalRemainderAppend
          (NF.O.E.allR290Pairs D.fibre headPositive)
          (G.globalPairs cutoff outputs tailPositive)))
      (trans
        (solve
          (headRemainder
            ∷ R385.sumWeightedRemainder
              (G.globalPairs cutoff outputs tailPositive)
            ∷ []))
        (trans
          (cong₂ _+_ headNormal tailNormal)
          (solve
            (NF.factoredFull output D.fibre
              ∷ D.literalSelfGramSum
              ∷ D.literalSelfFluxTangentSum
              ∷ globalFactoredFull cutoff outputs tailNonzero
              ∷ globalSelfGram cutoff outputs tailNonzero
              ∷ globalSelfFluxTangent cutoff outputs tailNonzero
              ∷ []))))
    where
    cong : ∀ {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
    cong f refl = refl

round555GlobalOutputAggregationClosed : Bool
round555GlobalOutputAggregationClosed = true

round555UsesSameR398PositivityWitnesses : Bool
round555UsesSameR398PositivityWitnesses = true

round555IntroducesAnyAnalyticEstimate : Bool
round555IntroducesAnyAnalyticEstimate = false

round555TrajectorySliceWeldClosed : Bool
round555TrajectorySliceWeldClosed = false

round555FactoredFullSpacetimeBoundClosed : Bool
round555FactoredFullSpacetimeBoundClosed = false

round555ClayPromotion : Bool
round555ClayPromotion = false

round555GlobalOutputAggregationClosedIsTrue :
  round555GlobalOutputAggregationClosed ≡ true
round555GlobalOutputAggregationClosedIsTrue = refl

round555ClayPromotionIsFalse : round555ClayPromotion ≡ false
round555ClayPromotionIsFalse = refl
