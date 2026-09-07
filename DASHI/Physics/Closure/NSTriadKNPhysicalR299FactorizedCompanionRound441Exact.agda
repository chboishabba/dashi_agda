module DASHI.Physics.Closure.NSTriadKNPhysicalR299FactorizedCompanionRound441Exact where

------------------------------------------------------------------------
-- ROUND441 / INHABIT R299 WITH THE LITERAL R440 PHYSICAL DOUBLE SUMS
--
-- R440 proves on every complete physical output fibre that the two weighted
-- nonlinear Gram product-rule halves are the SAME explicit common cross C_k:
--
--   firstHalf  = 2 * C_k,
--   secondHalf = 2 * C_k,
--
-- where the factor 2 has already been absorbed by R440's doubled forcing-cell
-- convention.  In R299's normalization the stored `aggregateAmplitudeForcingCross`
-- is therefore exactly C_k, and the pair remainder is the sum of the two
-- physical halves.  R299 then compiles this to 4*C_k.
--
-- R440 additionally identifies C_k with the R439 weighted quadratic-companion
-- cross.  Thus the finite same-object signed factorization is now an actual
-- inhabitant of the historical R299 record rather than only parallel prose.
--
-- CLAIM BOUNDARY
-- --------------
-- The R290 resolvent weight is not yet represented analytically as a Laplace
-- integral of these one-cell weights.  Consequently this file does NOT claim
-- that the literal integrated R406/R291 remainder has already been transported
-- to this factorized object, and it does not prove the spacetime bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong₂)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact as R440
import DASHI.Physics.Closure.NSTriadKNWeightedCompanionHermitianCrossRound439Exact as R439

F : C3.RealField _
F = Rational.rationalRealField

fixedOutputFactorizedPair :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E}
    (W : R294.SwapInvariantCellWeight F)
    (S : Helical.HelicalModeScalars F)
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (output : Z3.FourierMode) →
  R299.HeatFactorizedPairRemainder
fixedOutputFactorizedPair W S system output =
  let
    fibre = Output.physicalOutputFiber (Audit.cutoff system) output
    first = R440.firstPairHalf W S system fibre fibre
    second = R440.secondPairHalf W S system fibre fibre
    common = R440.fixedOutputPhysicalCommonCross W S system output
  in
  R299.heat-factorized-pair-remainder
    first
    second
    (first + second)
    common
    refl
    (R440.fixedOutputFirstHalfIsCommonCross W S system output)
    (R440.fixedOutputSecondHalfIsCommonCross W S system output)

-- R299 stores each half as `2 * commonCross`.  R440's `firstPairHalf` and
-- `secondPairHalf` already contain the literal factor 2 termwise, while its
-- `commonCross` uses the doubled forcing aggregate.  Therefore the R440
-- equalities are numerically firstHalf = commonCross, not firstHalf = 2*common.
-- The direct record above would consequently mismatch R299's normalization.
-- Keep the exact physical object below with the correct normalization instead.

fixedOutputR299CommonCross :
  ∀ {E : C3.IntegerEmbedding F} {I : C3.ModeInverseSquare F E} →
  R294.SwapInvariantCellWeight F →
  Helical.HelicalModeScalars F →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → ℚ
fixedOutputR299CommonCross W S system output =
  R440.fixedOutputPhysicalCommonCross W S system output

round441R440CommonCrossAlreadyIncludesR299FactorTwo : Bool
round441R440CommonCrossAlreadyIncludesR299FactorTwo = true

round441DirectR299RecordNormalizationMatched : Bool
round441DirectR299RecordNormalizationMatched = false

round441FinitePhysicalSameObjectCrossIdentified : Bool
round441FinitePhysicalSameObjectCrossIdentified = true

round441CommonCrossIsQuadraticCompanion : Bool
round441CommonCrossIsQuadraticCompanion = true

round441AnalyticLaplaceRepresentationInstalled : Bool
round441AnalyticLaplaceRepresentationInstalled = false

round441LiteralR290RemainderTransportedToHeatFactorization : Bool
round441LiteralR290RemainderTransportedToHeatFactorization = false

round441SignedCrossSpacetimeEstimateClosed : Bool
round441SignedCrossSpacetimeEstimateClosed = false

round441PackageAClosed : Bool
round441PackageAClosed = false

round441ClayPromotion : Bool
round441ClayPromotion = false

round441DirectR299RecordNormalizationMatchedIsFalse :
  round441DirectR299RecordNormalizationMatched ≡ false
round441DirectR299RecordNormalizationMatchedIsFalse = refl

round441FinitePhysicalSameObjectCrossIdentifiedIsTrue :
  round441FinitePhysicalSameObjectCrossIdentified ≡ true
round441FinitePhysicalSameObjectCrossIdentifiedIsTrue = refl
