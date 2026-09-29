{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedPhysicalDefectNormalFormRound806Exact where

------------------------------------------------------------------------
-- ROUND806 / FINAL EXACT PHYSICAL RECUT OF THE SEPARATED QUOTIENT WALL
--
-- R801:
--
--   D_sep = 2 (36 C_sep - Q_sep),
--   D_sep = 0  <->  Q_sep = 36 C_sep.
--
-- R802:
--
--   C_sep = C_self,sep + C_ext,sep.
--
-- R803/R804:
--
--   C_self,sep = C_zero-safe,sep + C_p=0,sep.
--
-- R805:
--
--   M_self,sep = 2 C_zero-safe,sep,
--
-- where M_self,sep is the literal separated R625 four-helicity
-- multiplier-difference work.
--
-- Therefore exactly
--
--   36 C_sep
--     = 18 M_self,sep
--       + 36 C_p=0,sep
--       + 36 C_ext,sep,
--
-- and
--
--   D_sep
--     = 2 [
--         18 M_self,sep
--         + 36 C_p=0,sep
--         + 36 C_ext,sep
--         - Q_sep
--       ].
--
-- Hence the separated cancellation problem is now exactly:
--
--   D_sep = 0
--     <->
--   Q_sep
--     = 18 M_self,sep
--       + 36 C_p=0,sep
--       + 36 C_ext,sep.
--
-- The three surviving currencies are all literal physical objects:
--   * R625 four-helicity selected-self multiplier work,
--   * the explicitly isolated p=0 provenance branch,
--   * the explicitly retained R599 external-network branch.
--
-- No estimate, norm, absolute value, or unproved cross-carrier identification
-- is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

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
import DASHI.Physics.Closure.NSTriadKNR650SeparatedQuotientR230BalanceRound801Exact as R801
import DASHI.Physics.Closure.NSTriadKNR650SeparatedR230SelfExternalRound802Exact as R802
import DASHI.Physics.Closure.NSTriadKNR650SeparatedSelfCommutatorRound803Exact as R803
import DASHI.Physics.Closure.NSTriadKNR650SeparatedSelfZeroSafeSplitRound804Exact as R804
import DASHI.Physics.Closure.NSTriadKNR650SeparatedSelfMultiplierRound805Exact as R805

F : C3.RealField _
F = Rational.rationalRealField

eighteen thirtySix seventyTwo : ℚ
eighteen = 18
thirtySix = 36
seventyTwo = 72

module SeparatedPhysicalDefect
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

  module Base =
    R801.SeparatedR230Balance
      Time initialTime integrateTo
      VectorDerivativeOf ScalarDerivativeOf
      projectedCross vectorAlgebra zeroCalculus
      hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
      FTC integrationLinearity integrationTransport D C R

  module Packet = Base.Packet

  module At
      (cutoff : Nat)
      (time : Time)
      (S : Packet.LivePhysicalPacketStructure D C cutoff) where

    module B = Base.At cutoff time S
    module W = B.W
    module Live = B.Live

    physicalSystem =
      Live.P.Base.Base.NestedAt.physicalSystem

    helicalScalars =
      Base.Wall.Prev.Prev.Residual.Average.Three.Two.Paired.Local.O.Combined.Nested.S

    projectorLaws =
      Base.Wall.Prev.Prev.Residual.Average.Three.Two.Paired.Local.O.Combined.Nested.L

    halfCalibration =
      Base.Wall.Prev.Prev.Residual.Average.Three.Two.Paired.Local.O.Combined.Nested.H

    transverse =
      Live.P.Base.Base.NestedAt.allModeTransverse

    module Split =
      R802.SeparatedR230SelfExternal
        physicalSystem
        helicalScalars
        projectorLaws
        halfCalibration
        transverse

    module Self =
      R803.SeparatedSelfCommutator
        physicalSystem
        helicalScalars
        projectorLaws
        halfCalibration
        transverse

    module Zero =
      R804.SeparatedSelfZeroSafe
        physicalSystem
        helicalScalars
        projectorLaws
        halfCalibration
        transverse

    module Mult =
      R805.SeparatedSelfMultiplier
        physicalSystem
        helicalScalars
        projectorLaws
        halfCalibration
        transverse
        (Packet.realityAt S time)

    Dsep : ℚ
    Dsep = B.Dsep

    Qsep : ℚ
    Qsep = B.Qsep

    Csep : ℚ
    Csep = B.Csep

    Mself : ℚ
    Mself = Mult.globalMultiplierWork

    PZero : ℚ
    PZero = Zero.globalPZeroSelfDefectWork

    External : ℚ
    External = Split.globalExternalWork

    splitSamePhysicalCurrency :
      Csep ≡ Split.Base.globalSeparatedCommutatorWork
    splitSamePhysicalCurrency = refl

    selfSamePhysicalCurrency :
      Split.globalSelfWork ≡ Self.Split.globalSelfWork
    selfSamePhysicalCurrency = refl

    selfCommutatorSamePhysicalCurrency :
      Self.globalMaskedSelfWork ≡ Zero.Sep.globalMaskedSelfWork
    selfCommutatorSamePhysicalCurrency = refl

    zeroSafeSamePhysicalCurrency :
      Zero.globalZeroSafeSelfWork ≡ Mult.Sep.globalZeroSafeSelfWork
    zeroSafeSamePhysicalCurrency = refl

    csepSplitsZeroSafePZeroExternal :
      Csep
      ≡
      Zero.globalZeroSafeSelfWork
        + PZero
        + External
    csepSplitsZeroSafePZeroExternal =
      trans
        splitSamePhysicalCurrency
        (trans
          Split.globalWorkSplitsSelfExternal
          (trans
            (cong
              (_+ External)
              (trans
                selfSamePhysicalCurrency
                (trans
                  Self.globalSelfWorkIsMaskedCommutatorWork
                  (trans
                    selfCommutatorSamePhysicalCurrency
                    Zero.globalMaskedSelfWorkSplits))))
            (solve
              ( Zero.globalZeroSafeSelfWork
              ∷ PZero
              ∷ External
              ∷ []))))

    thirtySixCsepPhysicalNormalForm :
      thirtySix * Csep
      ≡
      eighteen * Mself
        + thirtySix * PZero
        + thirtySix * External
    thirtySixCsepPhysicalNormalForm =
      trans
        (cong (thirtySix *_) csepSplitsZeroSafePZeroExternal)
        (trans
          (cong
            (λ zeroSafe →
              thirtySix * zeroSafe
                + thirtySix * PZero
                + thirtySix * External)
            zeroSafeSamePhysicalCurrency)
          (trans
            (solve
              ( eighteen
              ∷ thirtySix
              ∷ R805.two
              ∷ Mult.Sep.globalZeroSafeSelfWork
              ∷ PZero
              ∷ External
              ∷ []))
            (cong
              (λ multiplier →
                eighteen * multiplier
                  + thirtySix * PZero
                  + thirtySix * External)
              (sym Mult.globalMultiplierWorkIsDoubleZeroSafe))))

    separatedPhysicalDefectNormalForm :
      Dsep
      ≡
      Fold.two *
        ( eighteen * Mself
        + thirtySix * PZero
        + thirtySix * External
        - Qsep )
    separatedPhysicalDefectNormalForm =
      trans
        B.separatedR230FactorTwoNormalForm
        (cong
          (Fold.two *_)
          (trans
            (cong (_- Qsep) thirtySixCsepPhysicalNormalForm)
            refl))

    physicalBalanceImpliesSeparatedCancellation :
      Qsep
      ≡
      eighteen * Mself
        + thirtySix * PZero
        + thirtySix * External →
      Dsep ≡ 0ℚ
    physicalBalanceImpliesSeparatedCancellation balance =
      trans
        separatedPhysicalDefectNormalForm
        (trans
          (cong
            (Fold.two *_)
            (cong
              ( eighteen * Mself
              + thirtySix * PZero
              + thirtySix * External
              -_)
              balance))
          (solve
            ( Fold.two
            ∷ eighteen
            ∷ Mself
            ∷ thirtySix
            ∷ PZero
            ∷ External
            ∷ [])))

    separatedCancellationImpliesPhysicalBalance :
      Dsep ≡ 0ℚ →
      Qsep
      ≡
      eighteen * Mself
        + thirtySix * PZero
        + thirtySix * External
    separatedCancellationImpliesPhysicalBalance cancelled =
      trans
        (B.separatedCancellationImpliesR230Balance cancelled)
        thirtySixCsepPhysicalNormalForm

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round806AbstractR230CurrencyFullyDecomposed : Bool
round806AbstractR230CurrencyFullyDecomposed = true

round806ZeroSafeSelfOnR625MultiplierCarrier : Bool
round806ZeroSafeSelfOnR625MultiplierCarrier = true

round806PZeroProvenanceDefectExplicit : Bool
round806PZeroProvenanceDefectExplicit = true

round806ExternalNetworkDefectExplicit : Bool
round806ExternalNetworkDefectExplicit = true

round806CancellationEquivalentToPhysicalThreeCurrencyBalance : Bool
round806CancellationEquivalentToPhysicalThreeCurrencyBalance = true

round806IntroducesEstimate : Bool
round806IntroducesEstimate = false

round806PZeroDefectClosed : Bool
round806PZeroDefectClosed = false

round806ExternalDefectClosed : Bool
round806ExternalDefectClosed = false

round806W2Closed : Bool
round806W2Closed = false

round806ClayPromotion : Bool
round806ClayPromotion = false

round806AbstractR230CurrencyFullyDecomposedIsTrue :
  round806AbstractR230CurrencyFullyDecomposed ≡ true
round806AbstractR230CurrencyFullyDecomposedIsTrue = refl

round806ZeroSafeSelfOnR625MultiplierCarrierIsTrue :
  round806ZeroSafeSelfOnR625MultiplierCarrier ≡ true
round806ZeroSafeSelfOnR625MultiplierCarrierIsTrue = refl

round806PZeroProvenanceDefectExplicitIsTrue :
  round806PZeroProvenanceDefectExplicit ≡ true
round806PZeroProvenanceDefectExplicitIsTrue = refl

round806ExternalNetworkDefectExplicitIsTrue :
  round806ExternalNetworkDefectExplicit ≡ true
round806ExternalNetworkDefectExplicitIsTrue = refl

round806CancellationEquivalentToPhysicalThreeCurrencyBalanceIsTrue :
  round806CancellationEquivalentToPhysicalThreeCurrencyBalance ≡ true
round806CancellationEquivalentToPhysicalThreeCurrencyBalanceIsTrue = refl

round806IntroducesEstimateIsFalse :
  round806IntroducesEstimate ≡ false
round806IntroducesEstimateIsFalse = refl

round806PZeroDefectClosedIsFalse :
  round806PZeroDefectClosed ≡ false
round806PZeroDefectClosedIsFalse = refl

round806ExternalDefectClosedIsFalse :
  round806ExternalDefectClosed ≡ false
round806ExternalDefectClosedIsFalse = refl

round806W2ClosedIsFalse :
  round806W2Closed ≡ false
round806W2ClosedIsFalse = refl

round806ClayPromotionIsFalse :
  round806ClayPromotion ≡ false
round806ClayPromotionIsFalse = refl
