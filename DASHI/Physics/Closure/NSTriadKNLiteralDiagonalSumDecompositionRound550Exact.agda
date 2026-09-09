module DASHI.Physics.Closure.NSTriadKNLiteralDiagonalSumDecompositionRound550Exact where

------------------------------------------------------------------------
-- ROUND550 / R547 DIAGONAL SUM -> SELF-GRAM SUM + SELF-FLUX-TANGENT SUM
--
-- R548 proves the diagonal identity pointwise.  R547, however, subtracts the
-- generic R543 diagonalSum of R538's symmetric physical pair scalar.  This
-- owner closes that finite same-object seam over one literal nonzero physical
-- output fibre.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; Positive; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538
import DASHI.Physics.Closure.NSTriadKNFullSquareDiagonalOffDiagonalRound543Exact as R543
import DASHI.Physics.Closure.NSTriadKNDiagonalWeightedRemainderDecompositionRound548Exact as R548

F : C3.RealField _
F = Rational.rationalRealField

module LiteralDiagonal
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module Pair = R389.DoubleMixedPair physicalSystem S
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive
  module Swap = R538.PairSwap physicalSystem S
  module Diag = R548.PhysicalDiagonal physicalSystem S

  fibre : List Physical.PhysicalTriadIncidence
  fibre = Output.physicalOutputFiber cutoff output

  selfPositive :
    (alpha : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    Positive (R291.pairRate (Pair.physicalDoubleMixedPair alpha alpha))
  selfPositive alpha outputExact =
    let
      cellPositive = Rate.cellRatePositiveFromNonzeroOutput
        output outputNonzero alpha outputExact
    in
    Rate.pairRatePositiveFromCellRates alpha alpha cellPositive cellPositive

  sumSelfGram :
    (items : List Physical.PhysicalTriadIncidence) →
    ((alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) → ℚ
  sumSelfGram [] allOutput = 0ℚ
  sumSelfGram (alpha ∷ rest) allOutput =
    Diag.diagonalGram alpha (selfPositive alpha (allOutput alpha R396.here))
    + sumSelfGram rest
        (λ beta member → allOutput beta (R396.there member))

  sumSelfFluxTangent :
    (items : List Physical.PhysicalTriadIncidence) →
    ((alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) → ℚ
  sumSelfFluxTangent [] allOutput = 0ℚ
  sumSelfFluxTangent (alpha ∷ rest) allOutput =
    Diag.diagonalFluxTangent alpha
      (selfPositive alpha (allOutput alpha R396.here))
    + sumSelfFluxTangent rest
        (λ beta member → allOutput beta (R396.there member))

  diagonalSumDecomposes :
    (items : List Physical.PhysicalTriadIncidence) →
    (allOutput :
      (alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) →
    R543.diagonalSum Swap.symmetricWeightedRemainder items
    ≡ sumSelfGram items allOutput + sumSelfFluxTangent items allOutput
  diagonalSumDecomposes [] allOutput = refl
  diagonalSumDecomposes (alpha ∷ rest) allOutput =
    trans
      (cong₂ _+_
        (Diag.diagonalScalarDecomposition
          alpha (selfPositive alpha (allOutput alpha R396.here)))
        (diagonalSumDecomposes rest
          (λ beta member → allOutput beta (R396.there member))))
      (reassociate
        (Diag.diagonalGram alpha
          (selfPositive alpha (allOutput alpha R396.here)))
        (Diag.diagonalFluxTangent alpha
          (selfPositive alpha (allOutput alpha R396.here)))
        (sumSelfGram rest
          (λ beta member → allOutput beta (R396.there member)))
        (sumSelfFluxTangent rest
          (λ beta member → allOutput beta (R396.there member))))
    where
    reassociate : (a b c d : ℚ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
    reassociate a b c d = solve (a ∷ b ∷ c ∷ d ∷ [])

  literalDiagonalSum : ℚ
  literalDiagonalSum = R543.diagonalSum Swap.symmetricWeightedRemainder fibre

  literalSelfGramSum : ℚ
  literalSelfGramSum =
    sumSelfGram fibre (Rate.allElementsHaveOutput cutoff output)

  literalSelfFluxTangentSum : ℚ
  literalSelfFluxTangentSum =
    sumSelfFluxTangent fibre (Rate.allElementsHaveOutput cutoff output)

  literalDiagonalSumDecomposes :
    literalDiagonalSum ≡ literalSelfGramSum + literalSelfFluxTangentSum
  literalDiagonalSumDecomposes =
    diagonalSumDecomposes fibre (Rate.allElementsHaveOutput cutoff output)

round550LiteralR547DiagonalSameObjectWeldClosed : Bool
round550LiteralR547DiagonalSameObjectWeldClosed = true

round550DiagonalSumDecompositionClosed : Bool
round550DiagonalSumDecompositionClosed = true

round550ActualTemporalDerivativeReceiptClosed : Bool
round550ActualTemporalDerivativeReceiptClosed = false

round550SignedSpacetimeEstimateClosed : Bool
round550SignedSpacetimeEstimateClosed = false

round550ClayPromotion : Bool
round550ClayPromotion = false

round550DiagonalSumDecompositionClosedIsTrue :
  round550DiagonalSumDecompositionClosed ≡ true
round550DiagonalSumDecompositionClosedIsTrue = refl

round550ClayPromotionIsFalse : round550ClayPromotion ≡ false
round550ClayPromotionIsFalse = refl
