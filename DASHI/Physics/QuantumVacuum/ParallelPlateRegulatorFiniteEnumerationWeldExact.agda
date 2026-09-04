module DASHI.Physics.QuantumVacuum.ParallelPlateRegulatorFiniteEnumerationWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Finite
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q
import DASHI.Physics.QuantumVacuum.ParallelPlateModeSpectrumCutsetExact as Cutset
import DASHI.Physics.QuantumVacuum.PerfectConductorFiniteCutoffModeEnumerationExact as Enum

------------------------------------------------------------------------
-- FINITE ENUMERATION -> LITERAL PARALLEL-PLATE REGULATOR LIST
--
-- The regulator already consumes finite lists.  If the literal plate-mode list
-- is exactly the image of DASHI's exhaustive finite coordinate enumeration,
-- coverage is compiler output.  A caller therefore pays only the same-object
-- map/list/cutoff weld, not a second element-by-element exhaustiveness proof.
------------------------------------------------------------------------

record RegulatorFiniteEnumerationWeld
    {kernel : Casimir.CasimirScalarModel}
    (spectrum : Cutset.ParallelPlateSpectralModel kernel)
    (regulator : Cutset.ParallelPlateRegulator spectrum) : Set₁ where
  field
    separation : Q.Length
    cutoff : Cutset.Cutoff regulator

    enumeration : Enum.FiniteCutoffModeEnumerationReceipt

    coordinateToMode :
      Enum.FiniteModeCoordinate
        (Enum.transverseBound enumeration)
        (Enum.longitudinalBound enumeration) →
      Cutset.Mode spectrum

    plateListExact :
      Cutset.plateModes regulator separation cutoff ≡
      map coordinateToMode (Enum.coordinates enumeration)

    coordinateIndexAgreesWithPhysicalModeIndex : Set
    cutoffPredicateAgreesWithFiniteBounds : Set

open RegulatorFiniteEnumerationWeld public

enumeratedCoordinateInPlateList :
  ∀ {kernel spectrum regulator}
    (W : RegulatorFiniteEnumerationWeld {kernel} spectrum regulator) →
  (k : Fin (Enum.transverseBound (enumeration W))) →
  (n : Fin (Enum.longitudinalBound (enumeration W))) →
  (p : Cutset.Polarisation) →
  coordinateToMode W (k , (n , p))
  ∈ Cutset.plateModes regulator (separation W) (cutoff W)
enumeratedCoordinateInPlateList W k n p =
  subst
    (λ modes → coordinateToMode W (k , (n , p)) ∈ modes)
    (sym (plateListExact W))
    (Finite.mapMember
      (coordinateToMode W)
      (Enum.exhaustive (enumeration W) k n p))

record ReverseRegulatorEnumerationObligations : Set where
  field
    finiteCoordinateEnumerationChosen : Set
    finiteCoordinateToPhysicalModeMap : Set
    literalPlateListIsMappedEnumeration : Set
    modeIndexCompatibility : Set
    cutoffPredicateCompatibility : Set

open ReverseRegulatorEnumerationObligations public

data ExactMappedEnumerationAutomaticallyProvesContinuumCompleteness : Set where

finiteMappedCoverageDoesNotProveContinuumCompleteness :
  ExactMappedEnumerationAutomaticallyProvesContinuumCompleteness → ⊥
finiteMappedCoverageDoesNotProveContinuumCompleteness ()
