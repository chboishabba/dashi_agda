module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound22Validation where

------------------------------------------------------------------------
-- Focused validation root for the corrected physical Wilson/Hodge tranche.
--
-- Importing this module elaborates the round-twenty finite Combes--Thomas
-- endgame together with:
--
--   * the exact rational quaternion and four-link sixteen-atom Wilson rule;
--   * the rational literal gauge/constraint Hessian assembly;
--   * the full three-component physical Hodge/Poincare lift;
--   * the periodic four-dimensional curl-divergence identity;
--   * the open-versus-periodic boundary defect and positivity;
--   * the concrete flat Wilson=curl and flat gauge=divergence identities;
--   * the physical right-exponential background plaquette jets;
--   * the corrected boundary-assisted Wilson-plus-gauge coercivity reduction;
--   * the same-h producer interface stripped of duplicated scalar receipts.
--
-- The root does not assert the remaining nonzero-background Wilson and gauge
-- defect inequalities, the literal Hessian matrix/stencil producer, a finite
-- inverse construction, a continuum limit, or a Clay completion.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound20Validation
open import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact
open import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact
open import DASHI.Physics.YangMills.BalabanP33PhysicalSU2HodgeCoercivityExact
open import DASHI.Physics.YangMills.BalabanP33OpenPeriodicBoundaryEnergyAuditExact
open import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact
open import DASHI.Physics.YangMills.BalabanP33PhysicalFlatWilsonCurlIdentificationExact
open import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact
open import DASHI.Physics.YangMills.BalabanP33PhysicalPeriodicOpenReferenceBridgeExact
open import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintCancellationExact
open import DASHI.Physics.YangMills.BalabanP33WilsonSharpBudgetCoercivityExact
open import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonGaugeBoundaryCoercivityExact
open import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact
open import DASHI.Physics.YangMills.BalabanP33LiteralPhysicalPerturbationAdapterExact
