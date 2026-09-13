module DASHI.Physics.Closure.NSTriadKNLiveCriticalConePaymentCompilerRound589Exact where

------------------------------------------------------------------------
-- ROUND589 / REMOVE THE OPAQUE HISTORICAL-DECOMPOSITION SOCKET
--
-- R588 correctly required an exact same-object weld from the live R440 signed
-- common cross into R434's historical conditional compiler.  But asking proof
-- search to construct an arbitrary R434.FixedOutputCriticalConeDecomposition is
-- still stronger than necessary.
--
-- Once a genuine R284 physical payment P exists, the ONLY additional identity
-- needed by R434 is
--
--   live R440 cross = paidDeepMass(P) + coreGramDebt(P).
--
-- This module makes that the literal producer surface.  R434's decomposition and
-- R588's weld are compiler output.  Therefore the surviving nonanalytic seam is
-- one exact scalar decomposition identity; all hard inequalities remain visibly
-- inside the R284 payment (deep FL, deep HH, critical-core covariance theta<1).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (_+_; _*_; _≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNPhysicalHeatDoubleSumFactorizationRound440Exact as R440
import DASHI.Physics.Closure.NSTriadKNCriticalConeRelativeCovarianceTargetRound284Exact as R284
import DASHI.Physics.Closure.NSTriadKNFixedOutputCriticalConeCompilerRound434Exact as R434
import DASHI.Physics.Closure.NSTriadKNModernCriticalConeSameObjectBidiRound588Exact as R588
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

record LiveCriticalConePayment589
    {E : C3.IntegerEmbedding R440.F}
    {I : C3.ModeInverseSquare R440.F E}
    (W : R294.SwapInvariantCellWeight R440.F)
    (S : Helical.HelicalModeScalars R440.F)
    (system : Audit.FiniteComplex3GalerkinSystem R440.F E I)
    (output : Z3.FourierMode) : Set where
  constructor live-critical-cone-payment-589
  field
    payment589 : R284.CriticalConeRelativeCovariancePayment
    liveCrossDecomposition589 :
      R440.fixedOutputPhysicalCommonCross W S system output
      ≡ R284.paidDeepMass payment589 + R284.coreGramDebt payment589

open LiveCriticalConePayment589 public

historicalDecompositionFromLivePayment589 :
  ∀ {E : C3.IntegerEmbedding R440.F}
    {I : C3.ModeInverseSquare R440.F E}
    (W : R294.SwapInvariantCellWeight R440.F)
    (S : Helical.HelicalModeScalars R440.F)
    (system : Audit.FiniteComplex3GalerkinSystem R440.F E I)
    (output : Z3.FourierMode) →
  LiveCriticalConePayment589 W S system output →
  R434.FixedOutputCriticalConeDecomposition
historicalDecompositionFromLivePayment589 W S system output live =
  R434.fixed-output-critical-cone-decomposition
    (payment589 live)
    (R440.fixedOutputPhysicalCommonCross W S system output)
    (liveCrossDecomposition589 live)

sameObjectWeldFromLivePayment589 :
  ∀ {E : C3.IntegerEmbedding R440.F}
    {I : C3.ModeInverseSquare R440.F E}
    (W : R294.SwapInvariantCellWeight R440.F)
    (S : Helical.HelicalModeScalars R440.F)
    (system : Audit.FiniteComplex3GalerkinSystem R440.F E I)
    (output : Z3.FourierMode) →
  LiveCriticalConePayment589 W S system output →
  R588.HistoricalCriticalConeSameObjectWeld588
    (R440.fixedOutputPhysicalCommonCross W S system output)
sameObjectWeldFromLivePayment589 W S system output live =
  R588.historical-critical-cone-same-object-weld-588
    (historicalDecompositionFromLivePayment589 W S system output live)
    refl

liveR440CrossBelowCriticalBudget589 :
  ∀ {E : C3.IntegerEmbedding R440.F}
    {I : C3.ModeInverseSquare R440.F E}
    (W : R294.SwapInvariantCellWeight R440.F)
    (S : Helical.HelicalModeScalars R440.F)
    (system : Audit.FiniteComplex3GalerkinSystem R440.F E I)
    (output : Z3.FourierMode)
    (live : LiveCriticalConePayment589 W S system output) →
  R440.fixedOutputPhysicalCommonCross W S system output
  ≤ R284.theta (payment589 live) * R284.coreCompanionMass (payment589 live)
    + (R284.paidDeepCoefficient (payment589 live)
      + R284.coreEDCoefficient (payment589 live))
      * R284.energyDissipation (payment589 live)
liveR440CrossBelowCriticalBudget589 W S system output live =
  R588.liveR440CommonCrossBelowHistoricalCriticalBudget588
    W S system output
    (sameObjectWeldFromLivePayment589 W S system output live)

round589OpaqueHistoricalDecompositionIsProducerDebt : Bool
round589OpaqueHistoricalDecompositionIsProducerDebt = false

round589ExactLiveScalarDecompositionIsOnlyExtraWeld : Bool
round589ExactLiveScalarDecompositionIsOnlyExtraWeld = true

round589R434DecompositionCompilerOwned : Bool
round589R434DecompositionCompilerOwned = true

round589R588SameObjectWeldCompilerOwned : Bool
round589R588SameObjectWeldCompilerOwned = true

round589PhysicalR284PaymentConstructed : Bool
round589PhysicalR284PaymentConstructed = false

round589LiveScalarDecompositionConstructed : Bool
round589LiveScalarDecompositionConstructed = false

round589CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round589CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round589ClayPromotion : Bool
round589ClayPromotion = false
