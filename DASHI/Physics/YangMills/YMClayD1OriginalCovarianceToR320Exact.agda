{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayD1OriginalCovarianceToR320Exact where

------------------------------------------------------------------------
-- CLAY D1: the least-privilege original-source R320 analytic interface.
--
-- Prove a spatial bound on the SAME connected covariance of the finite
-- physical Gibbs measure: the selected mixed log derivative is then
-- EXACTLY that covariance, with no new derivative/localization oracle.
--
-- No Set-valued Clay endpoint, finite-jet assumption, or independent
-- coarse measure. The bound remains an actual physical input and is NOT
-- inferred from the formal equality of two moments.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_; ∣_∣)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanT5StateFamilySourceAlgebraRound295Exact as R295
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.YMClayRouteSH1DirectSelectedMarkedDecayExact as H1
import DASHI.Physics.YangMills.YMClayDirectSourceOSMassGapFrontierExact as Direct
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant

module _
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
  where

  -- Equality of actual selected source Hessian and ORIGINAL connected
  -- covariance. Both use the exact same finite sequence of Gibbs measures.
  selectedHessianIsOriginalConnectedCovariance :
    ∀ cutoff left right →
    Cumulant.mixedSecondLogDerivative (R318.calculus base)
      left right cutoff
    ≡
    R278.connectedCovarianceValue extension
      (Gram.measureSequence dataSet cutoff) left right
  selectedHessianIsOriginalConnectedCovariance cutoff left right =
    trans
      (cong (λ hessian → hessian cutoff)
        (Cumulant.mixedSecondLogDerivativeIsConnectedCovariance
          (R318.calculus base) left right))
      (R295.sourceConnectedCovarianceIsExactFiniteT5
        dataSet extension left right cutoff)

  selectedHessianMagnitudeIsOriginalCovarianceMagnitude :
    ∀ cutoff left right →
    R278.magnitude extension
      (Cumulant.mixedSecondLogDerivative (R318.calculus base)
        left right cutoff)
    ≡
    R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet cutoff) left right
  selectedHessianMagnitudeIsOriginalCovarianceMagnitude cutoff left right =
    cong (R278.magnitude extension)
      (selectedHessianIsOriginalConnectedCovariance cutoff left right)

  -- The ONE estimate a source-specific CMP116/RG/cluster argument must
  -- produce. This is a theorem PREMISE, not an automatically built bound.
  -- Note that the bound is on the actual finite Gibbs covariance,
  -- not on an abstract independent J calculus.
  originalConnectedCovarianceRootedShellBound :
    (∀ cutoff left right →
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff) left right
      ≤
      Shell.rootedShell (R318.shellData base)
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        (R318.connectingRoot base cutoff left right)
        (R318.physicalDistance base left right)) →
    R320.DirectSelectedT5MarkedDecayPayment base
  originalConnectedCovarianceRootedShellBound originalBound = record
    { R320.DirectSelectedT5MarkedDecayPayment.mixedDerivativeMagnitudeBelowSelectedShell =
        λ cutoff left right →
          subst
            (λ lower →
              lower ≤
              Shell.rootedShell (R318.shellData base)
                (R318.scaleOf base cutoff)
                (R318.volumeOf base cutoff)
                (R318.connectingRoot base cutoff left right)
                (R318.physicalDistance base left right))
            (sym (selectedHessianMagnitudeIsOriginalCovarianceMagnitude
              cutoff left right))
            (originalBound cutoff left right)
    }

  -- Reverse implication: R320's one physical field is no stronger than
  -- the concrete original selected connected-covariance shell estimate.
  -- This is the exact algebraic max-cut, not a new analytic hypothesis.
  r320ImpliesOriginalConnectedCovarianceRootedShellBound :
    R320.DirectSelectedT5MarkedDecayPayment base →
    ∀ cutoff left right →
    R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet cutoff) left right
    ≤
    Shell.rootedShell (R318.shellData base)
      (R318.scaleOf base cutoff)
      (R318.volumeOf base cutoff)
      (R318.connectingRoot base cutoff left right)
      (R318.physicalDistance base left right)
  r320ImpliesOriginalConnectedCovarianceRootedShellBound
      payment cutoff left right =
    subst
      (λ lower →
        lower ≤
        Shell.rootedShell (R318.shellData base)
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
          (R318.connectingRoot base cutoff left right)
          (R318.physicalDistance base left right))
      (selectedHessianMagnitudeIsOriginalCovarianceMagnitude
        cutoff left right)
      (R320.mixedDerivativeMagnitudeBelowSelectedShell
        payment cutoff left right)

  -- The existing canonical Route-S compiler immediately consumes the
  -- original physical covariance bound. Its output is the literal finite
  -- T5 source that R333 expects; no independent R296 source is requested.
  originalCovarianceBoundBuildsR333FiniteSource :
    (originalBound :
      ∀ cutoff left right →
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff) left right
      ≤
      Shell.rootedShell (R318.shellData base)
        (R318.scaleOf base cutoff)
        (R318.volumeOf base cutoff)
        (R318.connectingRoot base cutoff left right)
        (R318.physicalDistance base left right)) →
    (magnitudeIsAbsolute :
      ∀ value → R278.magnitude extension value ≡ ∣ value ∣) →
    R296.ExactT5JMagnitudePresentation dataSet extension
  originalCovarianceBoundBuildsR333FiniteSource
      originalBound magnitudeIsAbsolute =
    Direct.routeSH1BuildsFiniteMagnitude base
      (record
        { H1.RouteSH1DirectSelectedPayment.directSelectedDecay =
            originalConnectedCovarianceRootedShellBound originalBound
        })
      magnitudeIsAbsolute
