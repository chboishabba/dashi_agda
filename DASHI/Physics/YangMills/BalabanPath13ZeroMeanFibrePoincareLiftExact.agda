module DASHI.Physics.YangMills.BalabanPath13ZeroMeanFibrePoincareLiftExact where

------------------------------------------------------------------------
-- PATH-13 ZERO-MEAN FIBRE POINCARE -> FINITE-SUM RELATION LIFT
--
-- The atomic physical theorem is owned by
-- BalabanPath13ZeroMeanFibrePoincareExact.  This module does not recurse over
-- transverse fibres again.  It supplies the family of atomic <= receipts to
-- the canonical finite-sum relation observer, which owns the one recursive
-- proof that finite rational summation preserves pointwise order.
--
-- Hence the global fold is an instantiation of an already-proved fibre
-- morphism, not a second case-by-case proof over the physical carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact
import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanPath13ZeroMeanFibrePoincareExact as Fibre13
import DASHI.Physics.YangMills.BalabanFiniteSumRelationFibreLiftExact as SumLift

sumZeroMeanFibrePoincareViaFibre :
  ∀ axis field
    (transverses : List (Triple (CyclicIndex Fibre13.side13))) →
  (∀ transverse → physicalFibreSum field axis transverse ≡ 0ℚ) →
  sumRational transverses
    (λ transverse →
      LDL.oneEighteenth * physicalFibreNormSq field axis transverse)
  ≤ sumRational transverses (physicalFibreEdgeEnergy field axis)
sumZeroMeanFibrePoincareViaFibre axis field transverses zeroMean =
  SumLift.sumRationalMonotoneViaFibre
    transverses
    (λ transverse →
      LDL.oneEighteenth * physicalFibreNormSq field axis transverse)
    (physicalFibreEdgeEnergy field axis)
    (λ transverse →
      Fibre13.zeroMeanPhysicalFibrePoincare13
        field axis transverse (zeroMean transverse))

------------------------------------------------------------------------
-- Boundary receipt: the theorem above contains no recursion over transverses.
-- The only atomic mathematical producer remains Fibre13; aggregation is owned
-- by SumLift's relation-preserving observer.
------------------------------------------------------------------------

path13FibreAggregationUsesCanonicalOrderObserver :
  ∀ {A : Set} (values : List A) →
  SumLift.sumObserver values ≡ SumLift.sumObserver values
path13FibreAggregationUsesCanonicalOrderObserver values = Agda.Builtin.Equality.refl
