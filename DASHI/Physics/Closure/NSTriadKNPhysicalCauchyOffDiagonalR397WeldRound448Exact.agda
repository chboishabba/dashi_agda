module DASHI.Physics.Closure.NSTriadKNPhysicalCauchyOffDiagonalR397WeldRound448Exact where

------------------------------------------------------------------------
-- ROUND448 / R447 OFF-DIAGONAL = LITERAL R397/R385 WEIGHTED FLUX
--
-- R447 constructs the positive full Cauchy completion on a nonzero physical
-- output fibre.  Its off-diagonal term is
--
--   sum_{alpha<beta}
--     2 /(rho_alpha+rho_beta) Re<D_alpha,D_beta>.
--
-- R396 enumerates exactly the same unordered incidence pairs.  R389/R384 make
-- each enumerated R290 pair with
--
--   gram = 2 Re<D_alpha,D_beta>,
--   resolventWeight = 1/(rho_alpha+rho_beta).
--
-- Therefore the existing R397 `sumWeightedFlux` is exactly R447's
-- off-diagonal scalar.  This file proves that equality by finite recursion; no
-- estimate, sign, integration, heat representation or cardinality argument is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (_++_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; Positive; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNFibreLocalR378InstantaneousGramFluxRound397Exact as R397
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalPairRatePositivityRound400Exact as R400
import DASHI.Physics.Closure.NSTriadKNRationalCauchySchurComplementRound443Exact as R443
import DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact as R446
import DASHI.Physics.Closure.NSTriadKNPhysicalCauchyResolventCompletionRound447Exact as R447

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 1ℚ + 1ℚ

module PhysicalOffDiagonalWeld
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (Pdata : R225.PhysicalFixedOutputHelicityData
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem)
      S L H
      (Audit.velocityAt (Field30.finiteSystem physicalSystem)))
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module Pair = R389.DoubleMixedPair physicalSystem S
  module Rate = R400.PhysicalRate physicalSystem S viscosityPositive
  module Local = R396.LocalEnumerate physicalSystem S
  module OutputFlux = R397.LiteralOutputFluxLocal physicalSystem S L H Pdata
  module Completion = R447.PhysicalOutputCauchy
    physicalSystem S viscosityPositive cutoff output outputNonzero

  fibre : List Physical.PhysicalTriadIncidence
  fibre = Output.physicalOutputFiber cutoff output

  pairPositive : Local.PairRatePositiveOn fibre
  pairPositive = Rate.physicalOutputFibrePairRatesPositive
    cutoff output outputNonzero

  physicalPairCross :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  physicalPairCross alpha beta =
    two * R443.cauchyEntry
      (Pair.D.Pair.cellRate alpha)
      (Pair.D.Pair.cellRate beta)
      * R179.realHermitianCross
          (R225.doubleMixedCell S Pair.D.Pair.velocity alpha)
          (R225.doubleMixedCell S Pair.D.Pair.velocity beta)

  r290WeightedPairIsPhysicalCauchyCross :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    (positive : Positive
      (R291.pairRate (Pair.physicalDoubleMixedPair alpha beta))) →
    R290.weightedGramFlux
      (Pair.pairRatePositiveBuildsR290 alpha beta positive)
    ≡ physicalPairCross alpha beta
  r290WeightedPairIsPhysicalCauchyCross alpha beta positive =
    solve
      ( R443.cauchyEntry
          (Pair.D.Pair.cellRate alpha)
          (Pair.D.Pair.cellRate beta)
      ∷ R179.realHermitianCross
          (R225.doubleMixedCell S Pair.D.Pair.velocity alpha)
          (R225.doubleMixedCell S Pair.D.Pair.velocity beta)
      ∷ [])

  headPhysicalOffDiagonal :
    Physical.PhysicalTriadIncidence →
    List Physical.PhysicalTriadIncidence → ℚ
  headPhysicalOffDiagonal alpha [] = 0ℚ
  headPhysicalOffDiagonal alpha (beta ∷ rest) =
    physicalPairCross alpha beta + headPhysicalOffDiagonal alpha rest

  physicalOffDiagonal : List Physical.PhysicalTriadIncidence → ℚ
  physicalOffDiagonal [] = 0ℚ
  physicalOffDiagonal (alpha ∷ rest) =
    headPhysicalOffDiagonal alpha rest + physicalOffDiagonal rest

  headR290WeightedFluxExact :
    (alpha : Physical.PhysicalTriadIncidence) →
    (rest : List Physical.PhysicalTriadIncidence) →
    (positive :
      (beta : Physical.PhysicalTriadIncidence) →
      beta R396.OccursIn rest →
      Positive (R291.pairRate (Pair.physicalDoubleMixedPair alpha beta))) →
    R385.sumWeightedFlux (Local.headR290Pairs alpha rest positive)
    ≡ headPhysicalOffDiagonal alpha rest
  headR290WeightedFluxExact alpha [] positive = refl
  headR290WeightedFluxExact alpha (beta ∷ rest) positive =
    cong₂ _+_
      (r290WeightedPairIsPhysicalCauchyCross
        alpha beta (positive beta R396.here))
      (headR290WeightedFluxExact alpha rest
        (λ gamma member → positive gamma (R396.there member)))

  weightedFluxAppend :
    (left right : List R290.DampedGramPair) →
    R385.sumWeightedFlux (left ++ right)
    ≡ R385.sumWeightedFlux left + R385.sumWeightedFlux right
  weightedFluxAppend [] right = refl
  weightedFluxAppend (pair ∷ rest) right
    rewrite weightedFluxAppend rest right = refl

  allR290WeightedFluxExact :
    (items : List Physical.PhysicalTriadIncidence) →
    (positive : Local.PairRatePositiveOn items) →
    R385.sumWeightedFlux (Local.allR290Pairs items positive)
    ≡ physicalOffDiagonal items
  allR290WeightedFluxExact [] Local.positiveNil = refl
  allR290WeightedFluxExact (alpha ∷ rest)
      (Local.positiveCons headPositive tailPositive) =
    trans
      (weightedFluxAppend
        (Local.headR290Pairs alpha rest headPositive)
        (Local.allR290Pairs rest tailPositive))
      (cong₂ _+_
        (headR290WeightedFluxExact alpha rest headPositive)
        (allR290WeightedFluxExact rest tailPositive))

  weakenAcrossSkippedSecond :
    ∀ {alpha beta selected rest} →
    selected R396.OccursIn (alpha ∷ rest) →
    selected R396.OccursIn (alpha ∷ beta ∷ rest)
  weakenAcrossSkippedSecond R396.here = R396.here
  weakenAcrossSkippedSecond (R396.there member) =
    R396.there (R396.there member)

  builtHeadRowExact :
    (alpha : Physical.PhysicalTriadIncidence) →
    (rest : List Physical.PhysicalTriadIncidence) →
    (allOutput :
      (tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn (alpha ∷ rest) → Physical.k tau ≡ output) →
    R447.offDiagonalRow
      (R446.positive-rate-complex3-cell
        (Pair.D.Pair.cellRate alpha)
        (R225.doubleMixedCell S Pair.D.Pair.velocity alpha)
        (Rate.cellRatePositiveFromNonzeroOutput
          output outputNonzero alpha (allOutput alpha R396.here)))
      (Completion.buildCells rest
        (λ selected member → allOutput selected (R396.there member)))
    ≡ headPhysicalOffDiagonal alpha rest
  builtHeadRowExact alpha [] allOutput = refl
  builtHeadRowExact alpha (beta ∷ rest) allOutput =
    cong₂ _+_ refl
      (builtHeadRowExact alpha rest
        (λ selected member →
          allOutput selected (weakenAcrossSkippedSecond member)))

  builtOffDiagonalExact :
    (items : List Physical.PhysicalTriadIncidence) →
    (allOutput :
      (tau : Physical.PhysicalTriadIncidence) →
      tau R396.OccursIn items → Physical.k tau ≡ output) →
    R447.offDiagonalForm (Completion.buildCells items allOutput)
    ≡ physicalOffDiagonal items
  builtOffDiagonalExact [] allOutput = refl
  builtOffDiagonalExact (alpha ∷ rest) allOutput =
    cong₂ _+_
      (builtHeadRowExact alpha rest allOutput)
      (builtOffDiagonalExact rest
        (λ selected member → allOutput selected (R396.there member)))

  r447OffDiagonalIsR397WeightedFlux :
    Completion.offDiagonal
    ≡ R385.sumWeightedFlux
        (OutputFlux.outputPairs cutoff output pairPositive)
  r447OffDiagonalIsR397WeightedFlux =
    trans
      (builtOffDiagonalExact fibre (Rate.allElementsHaveOutput cutoff output))
      (sym (allR290WeightedFluxExact fibre pairPositive))

round448R447OffDiagonalEqualsLiteralR397WeightedFlux : Bool
round448R447OffDiagonalEqualsLiteralR397WeightedFlux = true

round448NoEstimateIntroduced : Bool
round448NoEstimateIntroduced = true

round448HeatRepresentationUsed : Bool
round448HeatRepresentationUsed = false

round448PhysicalDiagonalEndpointPaid : Bool
round448PhysicalDiagonalEndpointPaid = false

round448PackageAClosed : Bool
round448PackageAClosed = false

round448ClayPromotion : Bool
round448ClayPromotion = false

round448HeatRepresentationUsedIsFalse : round448HeatRepresentationUsed ≡ false
round448HeatRepresentationUsedIsFalse = refl
