{-# OPTIONS --safe #-}
module DASHI.Unified.SingularBasinCoarseRGTOEValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Unified.SingularBasinCoarseRGTOEExact as Owner
import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Physics.Dynamics.SingularBasinReductionExact as Reduction
import DASHI.Physics.Dynamics.SingularBasinFiniteWitnessExact as Finite
import DASHI.Physics.Dynamics.BasinResolutionRobustnessExact as Resolution
import DASHI.Physics.Dynamics.SingularBasinResolutionWitnessExact as ResolutionWitness
import DASHI.Physics.Dynamics.YanchukStableManifoldCrossingTargetExact as Yanchuk

toeFiniteReductionMatchesOwner :
  TOE.toeSingularBasinFiniteReduction
  ≡ Owner.finiteReduction
toeFiniteReductionMatchesOwner = refl

unifierFiniteReductionMatchesOwner :
  Unifier.unifierSingularBasinFiniteReduction
  ≡ Owner.finiteReduction
unifierFiniteReductionMatchesOwner = refl

toeFiniteReductionStillNotBasinPreserving :
  ¬ Reduction.BasinPreserving Owner.finiteReduction
toeFiniteReductionStillNotBasinPreserving =
  TOE.toeSingularBasinFiniteReductionNotBasinPreserving

unifierFiniteReductionStillNotBasinPreserving :
  ¬ Reduction.BasinPreserving Owner.finiteReduction
unifierFiniteReductionStillNotBasinPreserving =
  Unifier.unifierSingularBasinFiniteReductionNotBasinPreserving

toeFiniteBasinStillDoesNotFactor :
  ¬ Reduction.PredicateFactorisation
      Finite.project
      Finite.FullInBasin
toeFiniteBasinStillDoesNotFactor =
  TOE.toeSingularBasinFiniteFullBasinDoesNotFactor

unifierFiniteBasinStillDoesNotFactor :
  ¬ Reduction.PredicateFactorisation
      Finite.project
      Finite.FullInBasin
unifierFiniteBasinStillDoesNotFactor =
  Unifier.unifierSingularBasinFiniteFullBasinDoesNotFactor

toeSelectedResolutionStillNotRobust :
  ¬ Resolution.RobustAt
      ResolutionWitness.finiteResolutionGeometry
      Finite.FullInBasin
      ResolutionWitness.selectedResolution
      Finite.funnelState
toeSelectedResolutionStillNotRobust =
  TOE.toeSingularBasinSelectedResolutionNotRobust

unifierSelectedResolutionStillNotRobust :
  ¬ Resolution.RobustAt
      ResolutionWitness.finiteResolutionGeometry
      Finite.FullInBasin
      ResolutionWitness.selectedResolution
      Finite.funnelState
unifierSelectedResolutionStillNotRobust =
  Unifier.unifierSingularBasinSelectedResolutionNotRobust

toeStableManifoldTubeStillOpen :
  Yanchuk.intervalStableManifoldTubeCertified
    Owner.yanchukStableManifoldValidationBoundary
  ≡ false
toeStableManifoldTubeStillOpen =
  TOE.toeYanchukIntervalStableManifoldTubeStillMissing

unifierStableManifoldTubeStillOpen :
  Yanchuk.intervalStableManifoldTubeCertified
    Owner.yanchukStableManifoldValidationBoundary
  ≡ false
unifierStableManifoldTubeStillOpen =
  Unifier.unifierYanchukIntervalStableManifoldTubeStillMissing

toeBasinSeparationStillOpen :
  Yanchuk.basinSeparationTheoremCertified
    Owner.yanchukStableManifoldValidationBoundary
  ≡ false
toeBasinSeparationStillOpen =
  TOE.toeYanchukBasinSeparationTheoremStillMissing

unifierBasinSeparationStillOpen :
  Yanchuk.basinSeparationTheoremCertified
    Owner.yanchukStableManifoldValidationBoundary
  ≡ false
unifierBasinSeparationStillOpen =
  Unifier.unifierYanchukBasinSeparationTheoremStillMissing

toeZKPFrameMatchesOwner :
  TOE.toeSingularBasinZKPFrame
  ≡ Owner.canonicalSingularBasinTOEZKPFrame
toeZKPFrameMatchesOwner = refl

unifierZKPFrameMatchesOwner :
  Unifier.unifierSingularBasinZKPFrame
  ≡ Owner.canonicalSingularBasinTOEZKPFrame
unifierZKPFrameMatchesOwner = refl
