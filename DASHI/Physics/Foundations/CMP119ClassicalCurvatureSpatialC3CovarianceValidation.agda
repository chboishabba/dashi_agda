module DASHI.Physics.Foundations.CMP119ClassicalCurvatureSpatialC3CovarianceValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119ClassicalCurvatureStressInsertionExact as Stress
import DASHI.Physics.Foundations.CMP119ClassicalCurvatureSpatialC3CovarianceExact as Cut

classicalCurvatureSpatialC3Recovered :
  Cut.classicalCurvatureSpatialC3Recovered ≡ true
classicalCurvatureSpatialC3Recovered = refl

classicalStressSpatialC3Recovered :
  Cut.classicalStressSpatialC3Recovered ≡ true
classicalStressSpatialC3Recovered = refl

cycle01To02Covariant : ∀ curvature →
  Stress.stressInsertion (Cut.spatialC3Curvature curvature) K.component02
  ≡ Stress.stressInsertion curvature K.component01
cycle01To02Covariant curvature =
  Cut.spatialC3StressCovariant curvature K.component01

cycle12To23Covariant : ∀ curvature →
  Stress.stressInsertion (Cut.spatialC3Curvature curvature) K.component23
  ≡ Stress.stressInsertion curvature K.component12
cycle12To23Covariant curvature =
  Cut.spatialC3StressCovariant curvature K.component12

classicalSectorDoesNotCloseGeneratedActionQ1 :
  Cut.classicalCurvatureC3ClosesFullGeneratedActionQ1 ≡ false
classicalSectorDoesNotCloseGeneratedActionQ1 = refl
