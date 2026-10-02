{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345CriticalFoldsRound847Exact where

------------------------------------------------------------------------
-- R847 / ACTUAL CRITICAL PRODUCTION AND DISSIPATION FOLDS
--
-- Both literal critical summands contain the current velocity.  Therefore all
-- 722 inactive nonzero cutoff modes vanish exactly, without any theorem about
-- their projected nonlinear forcing.  The two 728-mode folds reduce to the
-- six nonzero velocity rows and can consume R844 + R842 directly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNR650Rational345SparseSnapshotRound836Exact as Snapshot
import DASHI.Physics.Closure.NSTriadKNR650Rational345ActiveHelicalScalarsRound835Exact as Active
import DASHI.Physics.Closure.NSTriadKNR650Rational345DirectPhysicalSnapshotRound841Exact as Direct
import DASHI.Physics.Closure.NSTriadKNR650Rational345GeometryCalibrationRound842Exact as Geometry
import DASHI.Physics.Closure.NSTriadKNR650Rational345ForcingRowsRound844Exact as Rows
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit

F : C3.RealField _
F = Rational.rationalRealField

filterModes :
  (Z3.FourierMode → Bool) →
  List Z3.FourierMode → List Z3.FourierMode
filterModes select [] = []
filterModes select (mode ∷ rest) with select mode
... | true = mode ∷ filterModes select rest
... | false = filterModes select rest

module Evaluate
    {E : C3.IntegerEmbedding F}
    (unit : Unit.UnitPreservingIntegerEmbedding F E)
    (I : C3.ModeInverseSquare F E) where

  system = Direct.directAuditSystem E I
  module G = Geometry.Geometry unit I
  module R = Rows.Evaluate unit I

  velocityZero :
    (mode : Z3.FourierMode) →
    Snapshot.velocityActive mode ≡ false →
    Audit.velocity system mode ≡ C3.complex3Zero F
  velocityZero mode inactive =
    Snapshot.velocityInactiveZero mode inactive

  productionFoldPrune :
    (items : List Z3.FourierMode) →
    Fold.weightedProjectedNonlinearProduction system items
    ≡
    Fold.weightedProjectedNonlinearProduction system
      (filterModes Snapshot.velocityActive items)
  productionFoldPrune [] = refl
  productionFoldPrune (mode ∷ rest)
    with Snapshot.velocityActive mode in active
  ... | true =
    cong
      (λ tail →
        Fold.dyadicCriticalWeight mode
          * Fold.realHermitianPairing
              (Audit.projectedNonlinearity system mode)
              (Audit.velocity system mode)
        + tail)
      (productionFoldPrune rest)
  ... | false =
    trans
      (cong₂ _+_
        headZero
        (productionFoldPrune rest))
      (solve
        (Fold.weightedProjectedNonlinearProduction system
          (filterModes Snapshot.velocityActive rest) ∷ []))
    where
    headZero :
      Fold.dyadicCriticalWeight mode
        * Fold.realHermitianPairing
            (Audit.projectedNonlinearity system mode)
            (Audit.velocity system mode)
      ≡ 0ℚ
    headZero rewrite velocityZero mode active = refl

  dissipationFoldPrune :
    (items : List Z3.FourierMode) →
    Fold.criticalViscousMass system items
    ≡
    Fold.criticalViscousMass system
      (filterModes Snapshot.velocityActive items)
  dissipationFoldPrune [] = refl
  dissipationFoldPrune (mode ∷ rest)
    with Snapshot.velocityActive mode in active
  ... | true =
    cong
      (λ tail →
        (Fold.dyadicCriticalWeight mode * C3.normSquared I mode)
          * L2.complex3NormSquared
              (Audit.velocity system mode)
        + tail)
      (dissipationFoldPrune rest)
  ... | false =
    trans
      (cong₂ _+_
        headZero
        (dissipationFoldPrune rest))
      (solve
        (Fold.criticalViscousMass system
          (filterModes Snapshot.velocityActive rest) ∷ []))
    where
    headZero :
      (Fold.dyadicCriticalWeight mode * C3.normSquared I mode)
        * L2.complex3NormSquared
            (Audit.velocity system mode)
      ≡ 0ℚ
    headZero rewrite velocityZero mode active = refl

  activeModesExact :
    filterModes Snapshot.velocityActive (Audit.modes system)
    ≡ Active.k₁ ∷ Active.k₂ ∷ Active.k₈ ∷ Active.k₇
      ∷ Active.k₄ ∷ Active.k₅ ∷ []
  activeModesExact = refl

  criticalProductionExact :
    Fold.criticalProductionRate system ≡ 0ℚ
  criticalProductionExact
    rewrite productionFoldPrune (Audit.modes system)
          | activeModesExact
          | R.forcing₁ | R.forcing₂ | R.forcing₈
          | R.forcing₇ | R.forcing₄ | R.forcing₅ =
    solve []

  criticalDissipationExact :
    Fold.criticalDissipationRate system ≡ 15834
  criticalDissipationExact
    rewrite dissipationFoldPrune (Audit.modes system)
          | activeModesExact
          | G.norm₁ | G.norm₂ | G.norm₈
          | G.norm₇ | G.norm₄ | G.norm₅ =
    solve []

round847CriticalProductionActualFoldClosed : Bool
round847CriticalProductionActualFoldClosed = true

round847CriticalDissipationActualFoldClosed : Bool
round847CriticalDissipationActualFoldClosed = true

round847InactiveForcingEvaluationRequired : Bool
round847InactiveForcingEvaluationRequired = false

round847ClayPromotion : Bool
round847ClayPromotion = false
