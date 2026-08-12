module DASHI.Physics.YangMills.BalabanPath13AllPhysicalFibresPoincareExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Sum the exact source-scale Path13 Poincare inequality over the complete
-- repository enumeration of all four-axis physical fibres.  This turns the
-- one-dimensional certificate into a genuine L=13 block statement:
--
--   (1/18) sum_f ||13 h - fibreSum(h)||_f^2
--       <= sum_f E_f(13 h - fibreSum(h)).
--
-- There are 4*13^3 physical fibres and every term is literal.  No dense
-- 342732-dimensional matrix is formed.  The next migration step is the exact
-- four-axis martingale/conditional-expectation identity converting the summed
-- centred fibre norm into the desired global constrained norm.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Product; pair)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Finite
import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCertificate as Generated
import DASHI.Physics.YangMills.BalabanPath13PhysicalFibreMatchExact as Physical13

side13FibreNorm : SiteField 13 → PhysicalFibre 13 → ℚ
side13FibreNorm field (pair axis transverse) =
  scaledCenteredFibreNormSq field axis transverse

side13FibreEnergy : SiteField 13 → PhysicalFibre 13 → ℚ
side13FibreEnergy field (pair axis transverse) =
  scaledCenteredFibreEdgeEnergy field axis transverse

side13AllFibreNorm : SiteField 13 → ℚ
side13AllFibreNorm field =
  sumRational (physicalFibreEnumeration 13) (side13FibreNorm field)

side13AllFibreEnergy : SiteField 13 → ℚ
side13AllFibreEnergy field =
  sumRational (physicalFibreEnumeration 13) (side13FibreEnergy field)

side13FibrePoincarePointwise :
  ∀ field fibre →
  Generated.oneEighteenth * side13FibreNorm field fibre
  ≤ side13FibreEnergy field fibre
side13FibrePoincarePointwise field (pair axis transverse) =
  Physical13.physicalSide13FibrePoincare field axis transverse

side13AllPhysicalFibresPoincare : ∀ field →
  Generated.oneEighteenth * side13AllFibreNorm field
  ≤ side13AllFibreEnergy field
side13AllPhysicalFibresPoincare field =
  let
    fibres = physicalFibreEnumeration 13
    summed :
      sumRational fibres
        (λ fibre → Generated.oneEighteenth * side13FibreNorm field fibre)
      ≤ sumRational fibres (side13FibreEnergy field)
    summed = Finite.sumPointwiseBelow fibres
      (λ fibre → Generated.oneEighteenth * side13FibreNorm field fibre)
      (side13FibreEnergy field)
      (side13FibrePoincarePointwise field)
  in
  subst
    (λ left → left ≤ side13AllFibreEnergy field)
    (sym
      (sumRationalScale Generated.oneEighteenth fibres
        (side13FibreNorm field)))
    summed

path13AllPhysicalFibresPoincareLevel : ProofLevel
path13AllPhysicalFibresPoincareLevel = machineChecked

-- The exact fibre enumeration cardinality is already machine checked in
-- BalabanPhysicalBlockFibreCarrier.  For L=13 it computes to 4*13^3 = 8788.
-- What is still needed for a global normal floor is not another spectral
-- calculation: it is the L=13 normalized conditional-expectation/martingale
-- decomposition and its orthogonality on this same physical carrier.
cmp109L13FourAxisMartingalePoincareLevel : ProofLevel
cmp109L13FourAxisMartingalePoincareLevel = conditional
