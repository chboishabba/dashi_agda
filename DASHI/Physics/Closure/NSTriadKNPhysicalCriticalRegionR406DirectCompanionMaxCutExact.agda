module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DirectCompanionMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B7 / LITERAL R406 SAME-OBJECT MAX-CUT
--
-- R498 already proves on the exact R398 global pair list:
--
--   literal weighted remainder = 4 * global direct companion.
--
-- B7 asks for the same literal weighted remainder to be four times the sum of
-- the live fixed-output coherent covariances.  Therefore finite output
-- aggregation is not a research leaf.  The only remaining semantic content is
-- one per-output same-object equality:
--
--   directFibreCompanion(output) = coherentCovarianceNumerator(output).
--
-- This owner makes that cut exact.  Given those local equalities for the
-- selected output list, it constructs the R406 same-object equality consumed
-- by the existing critical-region decomposition owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFiniteWeightedGramFluxAggregationRound385Exact as R385
import DASHI.Physics.Closure.NSTriadKNFibreLocalR378GlobalInstantaneousGramFluxRound398Exact as R398
import DASHI.Physics.Closure.NSTriadKNDirectResolventGlobalCompanionRound498Exact as R498
import DASHI.Physics.Closure.NSTriadKNDirectResolventFibreCompanionRound497Exact as R497
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DecompositionExact as B7

F : C3.RealField _
F = Rational.rationalRealField

module DirectCompanionMaxCut
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
      (Audit.velocityAt (Field30.finiteSystem physicalSystem))) where

  module Global = R398.GlobalFluxLocal physicalSystem S L H P
  module Direct = R498.DirectGlobal physicalSystem S L H P
  module Fibre = R497.DirectFibre physicalSystem S
  module Live = LiveOwner.Live physicalSystem S
  module Decomp = B7.Decomposition physicalSystem S

  data LocalCompanionCovarianceWeld
      (cutoff : Nat) :
      (outputs : List Z3.FourierMode) →
      Global.OutputFibresPositiveOn cutoff outputs → Set where
    localWeldNil :
      LocalCompanionCovarianceWeld cutoff [] Global.positiveOutputsNil
    localWeldCons :
      ∀ {output outputs headPositive tailPositive} →
      Fibre.directFibreCompanion
          (Output.physicalOutputFiber cutoff output) headPositive
        ≡ Live.coherentCovarianceNumerator output →
      LocalCompanionCovarianceWeld cutoff outputs tailPositive →
      LocalCompanionCovarianceWeld cutoff (output ∷ outputs)
        (Global.positiveOutputsCons headPositive tailPositive)

  globalDirectCompanionIsCovarianceSum :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    (positive : Global.OutputFibresPositiveOn cutoff outputs) →
    LocalCompanionCovarianceWeld cutoff outputs positive →
    Direct.globalDirectCompanion cutoff outputs positive
    ≡ Decomp.sumCovariance outputs
  globalDirectCompanionIsCovarianceSum cutoff []
      Global.positiveOutputsNil localWeldNil = refl
  globalDirectCompanionIsCovarianceSum cutoff (output ∷ outputs)
      (Global.positiveOutputsCons headPositive tailPositive)
      (localWeldCons head tail) =
    cong₂ _+_ head
      (globalDirectCompanionIsCovarianceSum
        cutoff outputs tailPositive tail)

  literalR406RemainderIsFourCovariances :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    (positive : Global.OutputFibresPositiveOn cutoff outputs) →
    LocalCompanionCovarianceWeld cutoff outputs positive →
    R385.sumWeightedRemainder
      (Global.globalPairs cutoff outputs positive)
    ≡ R299.four * Decomp.sumCovariance outputs
  literalR406RemainderIsFourCovariances cutoff outputs positive weld =
    trans
      (Direct.globalRemainderIsFourDirectCompanion cutoff outputs positive)
      (cong
        (R299.four *_)
        (globalDirectCompanionIsCovarianceSum
          cutoff outputs positive weld))
    where
    cong : ∀ {A B : Set} {x y : A} →
      (f : A → B) → x ≡ y → f x ≡ f y
    cong f refl = refl

  literalR406SameObjectData :
    (cutoff : Nat) →
    (outputs : List Z3.FourierMode) →
    (positive : Global.OutputFibresPositiveOn cutoff outputs) →
    LocalCompanionCovarianceWeld cutoff outputs positive →
    {paymentAt : (output : Z3.FourierMode) → Decomp.PaymentAt output} →
    Decomp.LiteralR406SameObjectData paymentAt
  literalR406SameObjectData cutoff outputs positive weld {paymentAt} = record
    { Decomp.outputs = outputs
    ; Decomp.globalWeightedRemainder =
        R385.sumWeightedRemainder
          (Global.globalPairs cutoff outputs positive)
    ; Decomp.globalRemainderIsFourCovariances =
        literalR406RemainderIsFourCovariances
          cutoff outputs positive weld
    }

------------------------------------------------------------------------
-- Status: global aggregation is closed; one local same-object weld remains.
------------------------------------------------------------------------

b7R406GlobalAggregationClosed : Bool
b7R406GlobalAggregationClosed = true

b7R498LiteralRemainderCarrierReused : Bool
b7R498LiteralRemainderCarrierReused = true

b7PerOutputDirectCompanionCovarianceWeldClosed : Bool
b7PerOutputDirectCompanionCovarianceWeldClosed = false

b7IntroducesEstimate : Bool
b7IntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false
