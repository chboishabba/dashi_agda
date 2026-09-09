module DASHI.Physics.Closure.NSTriadKNDiagonalSelfFluxToR447Round549Exact where

------------------------------------------------------------------------
-- ROUND549 / DIAGONAL R290 SELF-FLUX = TWICE THE R447 CAUCHY DIAGONAL
--
-- R548 decomposes the nonlinear diagonal as
--
--   weighted remainder = self Gram + weighted self-Gram flux tangent.
--
-- The weighted self-Gram flux itself is
--
--   [1/(lambda+lambda)] * 2 Re<D,D>,
--
-- while R447's Cauchy diagonal cell is
--
--   [1/(lambda+lambda)] * Re<D,D>.
--
-- Hence the exact normalization is a factor two.  This owner proves that
-- pointwise and then over the literal nonzero physical output fibre, so R457's
-- existing Cauchy-diagonal endpoint estimate can be reused for the diagonal
-- self-flux endpoint without changing carriers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; Positive; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact as R446
import DASHI.Physics.Closure.NSTriadKNPhysicalCauchyResolventCompletionRound447Exact as R447
import DASHI.Physics.Closure.NSTriadKNDiagonalWeightedRemainderDecompositionRound548Exact as R548

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1 + 1

module PhysicalSelfFlux
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module Pair = R389.DoubleMixedPair physicalSystem S
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive
  module Diag = R548.PhysicalDiagonal physicalSystem S
  module Completion = R447.PhysicalOutputCauchy
    physicalSystem S viscosityPositive cutoff output outputNonzero

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

  physicalCell :
    (alpha : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    R446.PositiveRateComplex3Cell
  physicalCell alpha outputExact =
    R446.positive-rate-complex3-cell
      (Pair.D.Pair.cellRate alpha)
      (R225.doubleMixedCell S Pair.D.Pair.velocity alpha)
      (Rate.cellRatePositiveFromNonzeroOutput
        output outputNonzero alpha outputExact)

  selfFluxIsTwiceCauchyDiagonalCell :
    (alpha : Physical.PhysicalTriadIncidence) →
    (outputExact : Physical.k alpha ≡ output) →
    Diag.diagonalFlux alpha (selfPositive alpha outputExact)
    ≡ two *
      (R446.cauchyKernel
        (physicalCell alpha outputExact)
        (physicalCell alpha outputExact)
       * R179.realHermitianCross
          (R446.value (physicalCell alpha outputExact))
          (R446.value (physicalCell alpha outputExact)))
  selfFluxIsTwiceCauchyDiagonalCell alpha outputExact =
    solve
      (R446.cauchyKernel
          (physicalCell alpha outputExact)
          (physicalCell alpha outputExact)
        ∷ R179.realHermitianCross
          (R446.value (physicalCell alpha outputExact))
          (R446.value (physicalCell alpha outputExact))
        ∷ [])

  sumSelfFlux :
    (items : List Physical.PhysicalTriadIncidence) →
    ((alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) → ℚ
  sumSelfFlux [] allOutput = 0
  sumSelfFlux (alpha ∷ rest) allOutput =
    Diag.diagonalFlux alpha (selfPositive alpha (allOutput alpha R396.here))
    + sumSelfFlux rest
        (λ beta member → allOutput beta (R396.there member))

  sumSelfFluxIsTwiceBuiltR447Diagonal :
    (items : List Physical.PhysicalTriadIncidence) →
    (allOutput :
      (alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) →
    sumSelfFlux items allOutput
    ≡ two * R447.diagonalForm (Completion.buildCells items allOutput)
  sumSelfFluxIsTwiceBuiltR447Diagonal [] allOutput = refl
  sumSelfFluxIsTwiceBuiltR447Diagonal (alpha ∷ rest) allOutput =
    trans
      (cong₂ _+_
        (selfFluxIsTwiceCauchyDiagonalCell alpha (allOutput alpha R396.here))
        (sumSelfFluxIsTwiceBuiltR447Diagonal rest
          (λ beta member → allOutput beta (R396.there member))))
      (solve
        (R446.cauchyKernel
            (physicalCell alpha (allOutput alpha R396.here))
            (physicalCell alpha (allOutput alpha R396.here))
          ∷ R179.realHermitianCross
            (R446.value (physicalCell alpha (allOutput alpha R396.here)))
            (R446.value (physicalCell alpha (allOutput alpha R396.here)))
          ∷ R447.diagonalForm
            (Completion.buildCells rest
              (λ beta member → allOutput beta (R396.there member)))
          ∷ []))

  literalSelfFluxSum : ℚ
  literalSelfFluxSum =
    sumSelfFlux Completion.fibre
      (Rate.allElementsHaveOutput cutoff output)

  literalSelfFluxIsTwiceR447Diagonal :
    literalSelfFluxSum ≡ two * Completion.diagonal
  literalSelfFluxIsTwiceR447Diagonal =
    sumSelfFluxIsTwiceBuiltR447Diagonal
      Completion.fibre (Rate.allElementsHaveOutput cutoff output)

round549PointwiseSelfFluxNormalizationClosed : Bool
round549PointwiseSelfFluxNormalizationClosed = true

round549LiteralSelfFluxEqualsTwiceR447Diagonal : Bool
round549LiteralSelfFluxEqualsTwiceR447Diagonal = true

round549IntroducesAnyAnalyticEstimate : Bool
round549IntroducesAnyAnalyticEstimate = false

round549DiagonalEndpointReusableFromR457 : Bool
round549DiagonalEndpointReusableFromR457 = true

round549ClayPromotion : Bool
round549ClayPromotion = false

round549LiteralSelfFluxEqualsTwiceR447DiagonalIsTrue :
  round549LiteralSelfFluxEqualsTwiceR447Diagonal ≡ true
round549LiteralSelfFluxEqualsTwiceR447DiagonalIsTrue = refl

round549ClayPromotionIsFalse : round549ClayPromotion ≡ false
round549ClayPromotionIsFalse = refl
