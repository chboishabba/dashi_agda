module DASHI.Physics.Closure.NSTriadKNLiteralSelfFluxDerivativeClosedRound563Exact where

------------------------------------------------------------------------
-- ROUND563 / CLOSE THE ACTUAL LITERAL SELF-FLUX DERIVATIVE
--
-- R559 supplies the finite derivative compiler. R561 constructs one literal
-- live self-pair derivative. R562 enumerates those data on the exact physical
-- output fibre and proves the finite sums are literally the R549/R550 self-flux
-- and self-flux-tangent observables. Therefore the derivative theorem itself is
-- now compiler-owned.
--
-- What remains in the diagonal temporal lane is ordinary scalar FTC/integration
-- authority for this already-fixed derivative pair. No NS-specific derivative
-- selection or same-object enumeration remains.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNLiteralSelfFluxFiniteDerivativeCompilerRound559Exact as R559
import DASHI.Physics.Closure.NSTriadKNLiteralSelfFluxPairFamilyRound562Exact as R562
import DASHI.Physics.Closure.NSTriadKNLiteralR406ClayTerminalCutsetRound504Exact as R504

F : C3.RealField _
F = Rational.rationalRealField

module ClosedDerivative
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) →
      (Time → ℚ) → Set)
    (projectedCrossCalculus :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra : R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarAlgebra : R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo VectorDerivativeOf)
    (R : R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
      Time initialTime integrateTo VectorDerivativeOf
      (R408.LiteralDynamics.literalPhysicalTrajectory
        Time initialTime integrateTo VectorDerivativeOf D))
    (cutoff : Nat)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output) where

  module Family = R562.LiteralSelfFluxFamily
    Time initialTime integrateTo VectorDerivativeOf
    projectedCrossCalculus vectorAlgebra D R cutoff output outputNonzero

  module Compile = R559.Compile
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    hermitianCalculus constantCalculus scalarAlgebra

  literalSelfFluxDerivative :
    ScalarDerivativeOf Family.selfFlux Family.selfFluxTangent
  literalSelfFluxDerivative =
    Compile.literalSelfFluxFamilyBuildsExactDerivative559
      Family.selfFlux Family.selfFluxTangent Family.literalSelfFluxFamily

round563LiteralSelfFluxDerivativeClosed : Bool
round563LiteralSelfFluxDerivativeClosed = true

round563LiteralSelfPairEnumerationStillOpen : Bool
round563LiteralSelfPairEnumerationStillOpen = false

round563CallerSelectedFluxOrTangent : Bool
round563CallerSelectedFluxOrTangent = false

round563OrdinaryScalarFTCStillRequired : Bool
round563OrdinaryScalarFTCStillRequired = true

round563FactoredFullSpacetimeBoundClosed : Bool
round563FactoredFullSpacetimeBoundClosed = false

round563LiteralR406SignedCrossPaymentClosed : Bool
round563LiteralR406SignedCrossPaymentClosed = false

round563CurrentGlobalFirstResidualStillLeafA :
  R504.firstTerminalResidual R504.currentTerminalStatus
  ≡ R504.missingLiteralR406SignedCrossPayment
round563CurrentGlobalFirstResidualStillLeafA = R504.currentFirstTerminalResidual

round563ClayPromotion : Bool
round563ClayPromotion = false

round563LiteralSelfFluxDerivativeClosedIsTrue :
  round563LiteralSelfFluxDerivativeClosed ≡ true
round563LiteralSelfFluxDerivativeClosedIsTrue = refl

round563LiteralSelfPairEnumerationStillOpenIsFalse :
  round563LiteralSelfPairEnumerationStillOpen ≡ false
round563LiteralSelfPairEnumerationStillOpenIsFalse = refl

round563ClayPromotionIsFalse : round563ClayPromotion ≡ false
round563ClayPromotionIsFalse = refl
