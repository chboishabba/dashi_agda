module DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedCurlHOneFiniteSumRound247Exact where

------------------------------------------------------------------------
-- ROUND247 / LIFT ROUND246 TO THE LITERAL FINITE GALERKIN MODE LIST
--
-- Round246 proves the physical homogeneous H^1 energy equality mode by mode:
--
--   |k|^2 <H u_k, H u_k> = |k|^2 <u_k,u_k>
--
-- for every transverse mode on the literal helical Fourier carrier.
--
-- This file performs only finite-sum congruence.  In particular, it evaluates
-- the equality on `Audit.modes (systemAt cutoff t)`, the actual mode list of
-- the Round240 physical Galerkin state.  No support surrogate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedCurlHOneModeIsometryRound246Exact as R246
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240

F : C3.RealField _
F = Rational.rationalRealField

finitePhysicalHOneEnergy :
  (I : C3.ModeInverseSquare F _) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  List Z3.FourierMode → ℚ
finitePhysicalHOneEnergy I velocity [] = 0ℚ
finitePhysicalHOneEnergy I velocity (k ∷ rest) =
  R246.physicalModeHOneEnergy I k (velocity k)
  + finitePhysicalHOneEnergy I velocity rest

finiteNormalizedCurlHOneEnergy :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  List Z3.FourierMode → ℚ
finiteNormalizedCurlHOneEnergy E I S velocity [] = 0ℚ
finiteNormalizedCurlHOneEnergy E I S velocity (k ∷ rest) =
  R246.physicalModeHOneEnergy I k (R142.normalizedCurl E S k (velocity k))
  + finiteNormalizedCurlHOneEnergy E I S velocity rest

finiteNormalizedCurlHOneIsometry :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (S : Helical.HelicalModeScalars F) →
  (L : Helical.PeriodicHelicalProjectorLaws F E I S) →
  (H : R142.HelicalHalfCalibration S) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (modes : List Z3.FourierMode) →
  ((k : Z3.FourierMode) → Helical.Transverse E k (velocity k)) →
  finiteNormalizedCurlHOneEnergy E I S velocity modes
  ≡ finitePhysicalHOneEnergy I velocity modes
finiteNormalizedCurlHOneIsometry E I S L H velocity [] transverse = refl
finiteNormalizedCurlHOneIsometry E I S L H velocity (k ∷ rest) transverse
  rewrite R246.normalizedCurlModeHOneIsometry
            E I S L H k (velocity k) (transverse k)
        | finiteNormalizedCurlHOneIsometry
            E I S L H velocity rest transverse = refl

module PhysicalTrajectoryFiniteHOne
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn =
    R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Base = Dyn.Base

  trajectoryPhysicalHOneEnergy :
    (T : Dyn.PhysicalNSGalerkinTrajectory) → Nat → Time → ℚ
  trajectoryPhysicalHOneEnergy T cutoff t =
    let
      B = Dyn.forgetDynamics T
      system = Base.systemAt B cutoff t
    in
    finitePhysicalHOneEnergy
      (Base.I B)
      (Audit.velocity system)
      (Audit.modes system)

  trajectoryNormalizedCurlHOneEnergy :
    (T : Dyn.PhysicalNSGalerkinTrajectory) → Nat → Time → ℚ
  trajectoryNormalizedCurlHOneEnergy T cutoff t =
    let
      B = Dyn.forgetDynamics T
      system = Base.systemAt B cutoff t
    in
    finiteNormalizedCurlHOneEnergy
      (Base.E B) (Base.I B) (Base.S B)
      (Audit.velocity system)
      (Audit.modes system)

  trajectoryNormalizedCurlHOneIsometry :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (cutoff : Nat) (t : Time) →
    trajectoryNormalizedCurlHOneEnergy T cutoff t
    ≡ trajectoryPhysicalHOneEnergy T cutoff t
  trajectoryNormalizedCurlHOneIsometry T cutoff t =
    let
      B = Dyn.forgetDynamics T
      system = Base.systemAt B cutoff t
    in
    finiteNormalizedCurlHOneIsometry
      (Base.E B) (Base.I B) (Base.S B) (Base.L B) (Base.H B)
      (Audit.velocity system)
      (Audit.modes system)
      (Base.velocityTransverse B cutoff t)

round247FiniteGalerkinNormalizedCurlHOneIsometryClosed : Bool
round247FiniteGalerkinNormalizedCurlHOneIsometryClosed = true

round247UsesLiteralSystemModeList : Bool
round247UsesLiteralSystemModeList = true

round247RepoSpecificW1IsometryClosed : Bool
round247RepoSpecificW1IsometryClosed = true

round247StandardTorusSobolevEmbeddingsInstalled : Bool
round247StandardTorusSobolevEmbeddingsInstalled = false

round247W1PhysicalInterpolationInstalled : Bool
round247W1PhysicalInterpolationInstalled = false

round247PackageAClosed : Bool
round247PackageAClosed = false

round247ClayPromotion : Bool
round247ClayPromotion = false

round247FiniteGalerkinNormalizedCurlHOneIsometryClosedIsTrue :
  round247FiniteGalerkinNormalizedCurlHOneIsometryClosed ≡ true
round247FiniteGalerkinNormalizedCurlHOneIsometryClosedIsTrue = refl

round247UsesLiteralSystemModeListIsTrue :
  round247UsesLiteralSystemModeList ≡ true
round247UsesLiteralSystemModeListIsTrue = refl

round247RepoSpecificW1IsometryClosedIsTrue :
  round247RepoSpecificW1IsometryClosed ≡ true
round247RepoSpecificW1IsometryClosedIsTrue = refl

round247PackageAClosedIsFalse : round247PackageAClosed ≡ false
round247PackageAClosedIsFalse = refl

round247ClayPromotionIsFalse : round247ClayPromotion ≡ false
round247ClayPromotionIsFalse = refl
