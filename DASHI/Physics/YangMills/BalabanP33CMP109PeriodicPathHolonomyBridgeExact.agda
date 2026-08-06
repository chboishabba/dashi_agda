module DASHI.Physics.YangMills.BalabanP33CMP109PeriodicPathHolonomyBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Identify the new orientation-sensitive occurrence holonomy with the
-- repository's pre-existing periodic path holonomy.  This prevents the
-- derivative kernel from living on a parallel path convention.
--
-- For the same positive-bond field and exact link group, the signed-word
-- recursion is definitionally the existing `pathHolonomy` recursion.  Combined
-- with the occurrence-list theorem, this gives
--
--   holonomy(occurrences(start,word))
--     = pathHolonomy(realization,start,word).
--
-- Thus the support-sensitive derivative kernel is attached to the literal
-- contour whose group value enters the CMP109 printed map.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanP33CMP109PeriodicContourEdgeKernelExact as Kernel

literalPeriodicWordHolonomyEqualsRepositoryPathHolonomy :
  ∀ {n Group Lie}
    (algebra : Kernel.OrientedDifferentialAlgebra Group Lie)
    (realization : Bond.PeriodicBondGaugeRealization
      n Group (Kernel.group algebra))
    (site : Periodic.PeriodicBlock n) directions →
  Kernel.literalPeriodicWordHolonomy algebra
    (Bond.bondField realization) site directions
  ≡ Bond.pathHolonomy realization site directions
literalPeriodicWordHolonomyEqualsRepositoryPathHolonomy
    algebra realization site [] = refl
literalPeriodicWordHolonomyEqualsRepositoryPathHolonomy
    algebra realization site (Carrier.pair axis true ∷ directions) =
  cong
    (Bond.multiply (Kernel.group algebra)
      (Bond.bondField realization (Carrier.pair site axis)))
    (literalPeriodicWordHolonomyEqualsRepositoryPathHolonomy
      algebra realization
      (Bond.walkStep site (Carrier.pair axis true)) directions)
literalPeriodicWordHolonomyEqualsRepositoryPathHolonomy
    algebra realization site (Carrier.pair axis false ∷ directions) =
  cong
    (Bond.multiply (Kernel.group algebra)
      (Bond.inverse (Kernel.group algebra)
        (Bond.bondField realization
          (Carrier.pair (Bond.negativeStep site axis) axis))))
    (literalPeriodicWordHolonomyEqualsRepositoryPathHolonomy
      algebra realization
      (Bond.walkStep site (Carrier.pair axis false)) directions)

occurrenceHolonomyEqualsRepositoryPathHolonomy :
  ∀ {n Group Lie}
    (algebra : Kernel.OrientedDifferentialAlgebra Group Lie)
    (agreement : Kernel.GroupOperationsAgree Group Lie algebra)
    (realization : Bond.PeriodicBondGaugeRealization
      n Group (Kernel.group algebra))
    (site : Periodic.PeriodicBlock n) directions →
  Kernel.literalOccurrenceHolonomy algebra
    (Bond.bondField realization)
    (Kernel.contourOccurrences site directions)
  ≡ Bond.pathHolonomy realization site directions
occurrenceHolonomyEqualsRepositoryPathHolonomy
    algebra agreement realization site directions =
  trans
    (Kernel.occurrenceHolonomyEqualsPeriodicWordHolonomy
      algebra agreement (Bond.bondField realization) site directions)
    (literalPeriodicWordHolonomyEqualsRepositoryPathHolonomy
      algebra realization site directions)

cmp109PeriodicPathConventionIdentificationLevel : ProofLevel
cmp109PeriodicPathConventionIdentificationLevel = machineChecked

cmp109OccurrenceToPrintedPathHolonomyLevel : ProofLevel
cmp109OccurrenceToPrintedPathHolonomyLevel = machineChecked
