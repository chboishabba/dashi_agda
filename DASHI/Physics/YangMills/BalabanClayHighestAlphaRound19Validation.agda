module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound19Validation where

-- Focused validation root for the standard Combes--Thomas replacement of the
-- custom residual/collar lane.  It extends round eighteen with:
--
--   * exact finite diagonal conjugation and inverse transport;
--   * exact finite tilt-defect row budgeting;
--   * rational geometric support-graph weights;
--   * half-gap coercivity survival at delta=1/32;
--   * physical 3072-coordinate SU(2) promotion to geometric Green decay;
--   * independent constant-sector and fluctuation-sector normalization walls;
--   * an augmented Wilson + gauge + constraint Hessian structure theorem with
--       Swoboda's continuum Hessian used only as structural precedent.
--
-- The root does not claim that the literal physical Hessian stencil, its
-- support-graph row mass, or the tilted inverse norm-to-entry estimate are
-- already proved.  Those remain the precise physical Combes--Thomas inputs.

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound18Validation
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasConjugationExact
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasTiltBudgetExact
import DASHI.Physics.YangMills.BalabanP33RationalGeometricCombesThomasWeightExact
import DASHI.Physics.YangMills.BalabanP33CombesThomasCoercivitySurvivalExact
import DASHI.Physics.YangMills.BalabanP33PhysicalCombesThomasPromotionExact
import DASHI.Physics.YangMills.BalabanP33BlockPoincareNormalizationWallExact
import DASHI.Physics.YangMills.BalabanP33AugmentedYangMillsHessianStructureExact
