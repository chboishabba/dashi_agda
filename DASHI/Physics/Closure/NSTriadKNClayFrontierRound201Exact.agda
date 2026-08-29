module DASHI.Physics.Closure.NSTriadKNClayFrontierRound201Exact where

------------------------------------------------------------------------
-- ROUND201 / QUARTIC COMPANION FRONTIER AFTER BLOCK-GRAM TELESCOPING
--
-- Round200 restores the homogeneity-correct A-facing object: the squared L2
-- mass of the quadratic raw-curl kernel.  Round201 now removes one more global
-- bookkeeping obstruction by proving an exact law of total Gram on arbitrary
-- finite signed physical blocks.
--
-- The remaining analytic target is no longer an uncontrolled raw cell Gram
-- matrix.  Inside each of the FL / HH / CC classes one may first group cells
-- into the physical dyadic/Bony/shell blocks and then prove a cutoff-uniform
-- estimate for
--
--   within-block debt + between-block residual covariance.
--
-- Intended physical mechanisms:
--   FL : multiplier-difference / far-low decay;
--   HH : dual radial-angular defect + low-output |k| gain;
--   CC : finite comparable-scale overlap.
--
-- None of those estimates is asserted by this module.  Package A and Clay
-- promotion remain false until the actual quartic companion is paid.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNClayFrontierRound200Exact as R200
import DASHI.Physics.Closure.NSTriadKNBlockGramCovarianceTelescopeRound201Exact as R201

round201HomogeneityCorrectQuarticObjectSelected : Bool
round201HomogeneityCorrectQuarticObjectSelected =
  R200.round200QuadraticKernelHasRequiredCompanionDegree

round201ExactBlockGramTelescopeClosed : Bool
round201ExactBlockGramTelescopeClosed = R201.round201LawOfTotalGramClosed

round201NoBlockCountTaxIntroduced : Bool
round201NoBlockCountTaxIntroduced = true

round201FarLowBlockPaymentClosed : Bool
round201FarLowBlockPaymentClosed = false

round201HighHighBlockPaymentClosed : Bool
round201HighHighBlockPaymentClosed = false

round201ComparableBlockPaymentClosed : Bool
round201ComparableBlockPaymentClosed = false

round201CutoffUniformQuarticCompanionClosed : Bool
round201CutoffUniformQuarticCompanionClosed = false

round201PackageAClosed : Bool
round201PackageAClosed = false

round201PackageBStandardAfterA : Bool
round201PackageBStandardAfterA = true

round201ClayPromotion : Bool
round201ClayPromotion = false

round201ExactBlockGramTelescopeClosedIsTrue :
  round201ExactBlockGramTelescopeClosed ≡ true
round201ExactBlockGramTelescopeClosedIsTrue = refl

round201PackageAClosedIsFalse : round201PackageAClosed ≡ false
round201PackageAClosedIsFalse = refl

round201ClayPromotionIsFalse : round201ClayPromotion ≡ false
round201ClayPromotionIsFalse = refl
