{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116FirstGradientLocalizationRound255Exact where

------------------------------------------------------------------------
-- ROUND255 / FIRST-GRADIENT LOCALITY IS A CMP116 FINITE-DERIVATIVE INSTANCE
--
-- CMP116 Sect.1 states that the localized analytic activities may be
-- differentiated a finite number of times and that the derivatives are
-- represented by Cauchy formulae while the independent spatial/tree exponential
-- majorant survives.  The existing Hessian owner specializes that statement to
-- second field variation.  Heat/Doob covariance consumes first field variation.
--
-- Therefore first-gradient locality is NOT a new YM decay theorem.  It is one
-- derivative-order specialization of the same source theorem, conditional only
-- on identifying the literal Heat/Doob gradient direction with the declared
-- CMP116 analytic field coordinate and using the same uniform positive radius.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanPreferredCommonRadiusFrontierRound232Exact as Radius

-- Source theorem: finite declared field/source derivatives retain the localized
-- exponential majorant.  First variation is a special case, not a new source
-- estimate.
cmp116FirstGradientLocalizationSourceLevel : ProofLevel
cmp116FirstGradientLocalizationSourceLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

firstGradientCauchyPreservesExternalMajorantLevel : ProofLevel
firstGradientCauchyPreservesExternalMajorantLevel =
  Source.finitePolydiscCauchyDerivativePreservesExternalMajorantLevel

-- Shared physical/source coordinate seam.  This deliberately aliases the same
-- marked-coordinate/uniform-radius owner used for beta/Hessian/composite marks;
-- it does not introduce an independent gradient decay assumption.
literalCMP116FirstGradientCoordinateAndRadiusLevel : ProofLevel
literalCMP116FirstGradientCoordinateAndRadiusLevel =
  Source.physicalCMP116MarkedCoordinateAndUniformRadiusIdentificationLevel

-- The common-radius consumer is independently minimized in Round232.  Once the
-- coordinate is identified, no second first-gradient-specific radius is owed.
literalUniformCommonRadiusLevel : ProofLevel
literalUniformCommonRadiusLevel = Radius.literalUniformCommonRadiusLevel
