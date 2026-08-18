module DASHI.Physics.Closure.NSTriadKNClusterProjectorDirectionalObservableNoGoRound80Exact where

------------------------------------------------------------------------
-- ROUND80 / PROJECTOR-QUOTIENT INFORMATION-LOSS THEOREM
--
-- A cluster projector is invariant under changes of basis inside its range.
-- That is precisely why it remains well-defined at internal eigenvalue
-- degeneracy.  The price is equally precise: observables depending on a
-- distinguished line INSIDE the cluster do not automatically descend to the
-- projector quotient.
--
-- This is the NS instance of the repo-wide quotient/observer discipline seen
-- independently in the observer-refinement PRs: removing a noncanonical fine
-- coordinate is safe only for observables constant on the resulting fibre.
--
-- The exact witness below uses the plane projector P12.  Both e1 and e2 lie in
-- the same projected plane, while the e1-direction weight x^2 is 1 on e1 and
-- 0 on e2.  Thus the plane projector cannot determine that directional
-- coordinate.  For C4 this means a degenerate cluster projector is useful only
-- if the depletion/rotation observable is reformulated as a cluster-invariant
-- quantity or supplied with an explicit internal residual coordinate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as M
import DASHI.Physics.Closure.NSTriadKNCorrectedFourierAngularStrainExact as A

plane12 : M.Matrix3
plane12 = M.matrix3
  1ℚ 0ℚ 0ℚ
  0ℚ 1ℚ 0ℚ
  0ℚ 0ℚ 0ℚ

e1 e2 : V.Vector3
e1 = V.v3 1ℚ 0ℚ 0ℚ
e2 = V.v3 0ℚ 1ℚ 0ℚ

p12FixesE1 : A.apply plane12 e1 ≡ e1
p12FixesE1 = refl

p12FixesE2 : A.apply plane12 e2 ≡ e2
p12FixesE2 = refl

-- A fine directional observable that is meaningful only after selecting an
-- internal line/basis coordinate.
directionalE1Weight : V.Vector3 → ℚ
directionalE1Weight value = V.x value * V.x value

e1DirectionalWeight : directionalE1Weight e1 ≡ 1ℚ
e1DirectionalWeight = refl

e2DirectionalWeight : directionalE1Weight e2 ≡ 0ℚ
e2DirectionalWeight = refl

record PlaneProjectorDeterminesInternalDirectionalWeight : Set where
  field
    readout : M.Matrix3 → ℚ
    agreesOnRange :
      (value : V.Vector3) →
      A.apply plane12 value ≡ value →
      readout plane12 ≡ directionalE1Weight value

open PlaneProjectorDeterminesInternalDirectionalWeight public

planeProjectorCannotDetermineInternalDirectionalWeight :
  PlaneProjectorDeterminesInternalDirectionalWeight →
  1ℚ ≡ 0ℚ
planeProjectorCannotDetermineInternalDirectionalWeight candidate =
  trans
    (Relation.Binary.PropositionalEquality.sym
      (trans
        (agreesOnRange candidate e1 p12FixesE1)
        e1DirectionalWeight))
    (trans
      (agreesOnRange candidate e2 p12FixesE2)
      e2DirectionalWeight)
  where
  open import Relation.Binary.PropositionalEquality

record ClusterObservationWithResidual : Set where
  constructor cluster-observation-with-residual
  field
    clusterProjector : M.Matrix3
    internalDirection : V.Vector3

round80ClusterProjectorRemovesInternalBasisGauge : Bool
round80ClusterProjectorRemovesInternalBasisGauge = true

round80ClusterProjectorDeterminesEveryDirectionalObservable : Bool
round80ClusterProjectorDeterminesEveryDirectionalObservable = false

round80DegenerateC4NeedsClusterInvariantObservableOrResidual : Bool
round80DegenerateC4NeedsClusterInvariantObservableOrResidual = true

round80ClusterProjectorDeterminesEveryDirectionalObservableIsFalse :
  round80ClusterProjectorDeterminesEveryDirectionalObservable ≡ false
round80ClusterProjectorDeterminesEveryDirectionalObservableIsFalse = refl
