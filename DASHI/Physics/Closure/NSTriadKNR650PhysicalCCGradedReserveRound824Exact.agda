{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650PhysicalCCGradedReserveRound824Exact where

------------------------------------------------------------------------
-- R824 / LITERAL CC ORIGINAL-INCIDENCE DEGREE COMPONENTS
--
-- R760 has the exact signed row identity
--     cell(beta) = 3 * [nested(beta)+nested(swap beta)]
--                  - 2 * pairedDyadicProduction(beta).
-- R822 keeps ORIGINAL beta, and attaches a separate comparable witness.
-- This file folds the two components over those original R822 rows, then
-- recombines them with R813 into the entire R823 signed rate.
-- It proves exact physical equalities, NOT velocity-amplitude scaling laws,
-- a sign, Gram debt payment, or a nonzero witness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNR650SeparatedNestedFourHelicityWallRound813Exact as R813
import DASHI.Physics.Closure.NSTriadKNR650CompleteSignedFourHelicityBarrierRound821Exact as R821
import DASHI.Physics.Closure.NSTriadKNR650CCTouchedSignedRowsRound822Exact as R822
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700

F : C3.RealField _
F = Rational.rationalRealField

import DASHI.Physics.Closure.NSTriadKNR650SignedComparableReserveRound823Exact as R823
import DASHI.Physics.Closure.NSTriadKNR650SwapPairedResidualCarrierRound760Exact as R760
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781

module PhysicalCCGradedReserve
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra :
      R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (zeroCalculus :
      Endpoint.VectorZeroDerivative Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf)
    (C :
      ModeCarrier.LiteralModeCarrier.LiteralCutoffModeCarrier
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D))
    (R :
      R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D)) where







  module Live =
    R823.SignedComparableReserve
      Time initialTime integrateTo
      VectorDerivativeOf ScalarDerivativeOf
      projectedCross vectorAlgebra zeroCalculus
      hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
      FTC integrationLinearity integrationTransport D C R

  module Packet = Live.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module B = Live.At cutoff time S
    module Cc = B.Cc

    -- All rows are the R822 original incidences, not R818 comparable proxies.
    ccHighCell : R822.SignedComparableRow → ℚ
    ccHighCell row =
      R744.three *
        (Cc.P.P.Base.Base.nestedOrbitCell
           (R822.originalIncidence row)
        + Cc.P.P.Base.Base.nestedOrbitCell
           (Symmetry.swapTriad (R822.originalIncidence row)))

    ccLowCell : R822.SignedComparableRow → ℚ
    ccLowCell row =
      Fold.two * Cc.P.P.Base.pairedTwoDifferenceCell
        (R822.originalIncidence row)

    originalRowIsHighMinusLow :
      (row : R822.SignedComparableRow) →
      Cc.originalSignedCell (R822.originalIncidence row)
        ≡ ccHighCell row - ccLowCell row
    originalRowIsHighMinusLow row =
      Cc.P.P.swapPairedResidualNormalForm (R822.originalIncidence row)

    foldRows :
      (f : R822.SignedComparableRow → ℚ) →
      List R822.SignedComparableRow → ℚ
    foldRows f [] = 0ℚ
    foldRows f (row ∷ rest) = f row + foldRows f rest

    ccHighFold : ℚ
    ccHighFold = foldRows ccHighCell Cc.comparableRows

    ccLowFold : ℚ
    ccLowFold = foldRows ccLowCell Cc.comparableRows

    rowFoldGraded :
      (rows : List R822.SignedComparableRow) →
      R822.signedRowFold Cc.originalSignedCell rows
        ≡ foldRows ccHighCell rows - foldRows ccLowCell rows
    rowFoldGraded [] = solve []
    rowFoldGraded (row ∷ rest) =
      trans
        (cong
          (Cc.originalSignedCell (R822.originalIncidence row) +_)
          (rowFoldGraded rest))
        (trans
          (cong
            (λ value →
              value +
                (foldRows ccHighCell rest - foldRows ccLowCell rest))
            (originalRowIsHighMinusLow row))
          (solve
            ( ccHighCell row
            ∷ ccLowCell row
            ∷ foldRows ccHighCell rest
            ∷ foldRows ccLowCell rest
            ∷ [])))

    ccOriginalSignedFoldGraded :
      B.signedComparableCC ≡ ccHighFold - ccLowFold
    ccOriginalSignedFoldGraded =
      rowFoldGraded Cc.comparableRows

    -- These are physical expressions; the degree labels refer to the
    -- existing R166/R289 audits, NOT newly established state-scaling laws.
    fullHigh : ℚ
    fullHigh =
      ccHighFold +
        Fold.two * R813.nine * B.H.N.globalNestedFourHelicityWork

    fullLow : ℚ
    fullLow =
      ccLowFold + Fold.two * B.H.N.Qsep

    fullQuadratic : ℚ
    fullQuadratic = B.viscousReserve

    actualCompleteRateGraded :
      B.completePhysicalRate ≡
        fullQuadratic + fullHigh - fullLow
    actualCompleteRateGraded =
      trans B.actualFullRateIsReserveMinusDemand
        (trans
          (cong
            (λ cc →
              (cc + fullQuadratic) - B.cubicQuinticDemand)
            ccOriginalSignedFoldGraded)
          (solve
            ( ccHighFold
            ∷ ccLowFold
            ∷ Fold.two
            ∷ R813.nine
            ∷ B.H.N.globalNestedFourHelicityWork
            ∷ B.H.N.Qsep
            ∷ fullQuadratic
            ∷ [])))

    -- The CC term cannot be paid by its R818 localization receipt alone:
    -- high and low components retain the ORIGINAL R760 signed incidence.
    comparableCertificatesPreserveOriginalHighAndLow :
      B.signedComparableCC ≡ ccHighFold - ccLowFold
    comparableCertificatesPreserveOriginalHighAndLow =
      ccOriginalSignedFoldGraded

round824CCTouchedOriginalRowsDecomposed : Bool
round824CCTouchedOriginalRowsDecomposed = true

round824CCPhysicalCubicQuinticExpressionExposed : Bool
round824CCPhysicalCubicQuinticExpressionExposed = true

round824ExactFullSignedRateHasQuadraticHighLowForm : Bool
round824ExactFullSignedRateHasQuadraticHighLowForm = true

round824ActualCarrierScalingLawsEstablished : Bool
round824ActualCarrierScalingLawsEstablished = false

round824PhysicalNonzeroCounterexampleConstructed : Bool
round824PhysicalNonzeroCounterexampleConstructed = false

round824IntegratedReservePaid : Bool
round824IntegratedReservePaid = false

round824W1Paid : Bool
round824W1Paid = false

round824ClayPromotion : Bool
round824ClayPromotion = false
