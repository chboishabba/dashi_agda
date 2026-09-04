module DASHI.Physics.QuantumVacuum.ParallelPlateRegulatorFiniteEnumerationWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.Fin.Base using (Fin)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q
import DASHI.Physics.QuantumVacuum.ParallelPlateModeSpectrumCutsetExact as Cutset
import DASHI.Physics.QuantumVacuum.PerfectConductorFiniteCutoffModeEnumerationExact as Enum

------------------------------------------------------------------------
-- FINITE ENUMERATION -> LITERAL PARALLEL-PLATE REGULATOR LIST
--
-- The regulator already consumes finite lists.  This weld states exactly what
-- is needed to know that a concrete cutoff list is not merely a sample: every
-- bounded transverse/longitudinal/polarization coordinate is represented in
-- the literal list used by the regulated energy.
------------------------------------------------------------------------

record RegulatorFiniteEnumerationWeld
    {kernel : Casimir.CasimirScalarModel}
    (spectrum : Cutset.ParallelPlateSpectralModel kernel)
    (regulator : Cutset.ParallelPlateRegulator spectrum) : Set₁ where
  field
    separation : Q.Length
    cutoff : Cutset.Cutoff regulator

    transverseBound longitudinalBound : Nat
    enumeration : Enum.FiniteCutoffModeEnumerationReceipt

    coordinateToMode :
      Enum.FiniteModeCoordinate transverseBound longitudinalBound →
      Cutset.Mode spectrum

    enumerationHasRequestedBounds :
      (Enum.transverseBound enumeration ≡ transverseBound) ×
      (Enum.longitudinalBound enumeration ≡ longitudinalBound)

    coordinateIndexAgreesWithPhysicalModeIndex : Set
    cutoffPredicateAgreesWithFiniteBounds : Set

    everyEnumeratedCoordinateInPlateList :
      (k : Fin transverseBound) →
      (n : Fin longitudinalBound) →
      (p : Cutset.Polarisation) →
      coordinateToMode (k , (n , p))
      ∈ Cutset.plateModes regulator separation cutoff

open RegulatorFiniteEnumerationWeld public

record ReverseRegulatorEnumerationObligations : Set where
  field
    finiteBoundsExtractedFromCutoff : Set
    finiteCoordinateToPhysicalModeMap : Set
    modeIndexCompatibility : Set
    cutoffPredicateCompatibility : Set
    literalPlateListCoverage : Set

open ReverseRegulatorEnumerationObligations public

data RegulatorListAutomaticallyExhaustiveBecauseFinite : Set where

finiteListNeedsCoverageProof :
  RegulatorListAutomaticallyExhaustiveBecauseFinite → ⊥
finiteListNeedsCoverageProof ()
