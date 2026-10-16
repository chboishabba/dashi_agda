module DASHI.Physics.Closure.E6HyperformH3H2IncidenceGroundStateExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformH3H2PhaseIncidenceExact as Incidence
import DASHI.Physics.Closure.E6HyperformH3H2InvariantPotentialNoGoExact as NoGo

------------------------------------------------------------------------
-- INCIDENCE-ONLY INTERACTION AFTER THE ONSITE-POTENTIAL NO-GO
--
-- A section chooses one of the nine incident H2 faces over each H3 patch.
-- The simplest relational interaction already present in the hyperfabric is:
-- reward two adjacent H3 patches when they both choose their shared H2 face.
--
-- If k_f in {0,1,2,3,4} H3 patches choose one H2 face f, its agreement
-- contribution is C(k_f,2).  Since every H2 has exactly four incident H3 and
-- every section makes 120 choices,
--
--   sum_f k_f = 120,
--   C(k,2) <= 3k/2  for 0<=k<=4,
--
-- with equality only for k=0 or k=4. Hence total agreement is at most 180,
-- and equality occurs exactly when occupied H2 faces are saturated four-stars:
-- a partition of all 120 H3 patches into 30 incident-H2 stars.
--
-- The independent exhaustive Python producer finds exactly 6642 such exact
-- covers. Under the full W(E6) generator action these split into four orbits:
--
--   162, 1620, 1620, 3240,
--
-- with stabilizers 320, 32, 32, 16 respectively.
--
-- Defect gap. Let n1,n2,n3 count partially occupied faces of occupancies
-- 1,2,3. Since total load is 0 mod 4,
--
--   n1 + 2 n2 + 3 n3 = 0 mod 4.
--
-- Relative to the 180 bound the agreement deficit is
--
--   (3 n1 + 4 n2 + 3 n3)/2.
--
-- The least positive compatible value is 3, attained by one occupancy-1 and
-- one occupancy-3 face. A literal one-H3 flip from an enumerated exact cover
-- realizes agreement 177, so the dimensionless interaction defect gap is 3.
-- This equals the separately computed fibre-Laplacian gap numerically; no
-- same-operator theorem is inferred from the equality.
--
-- The upper-bound/gap reasoning is mathematical; the 6642 enumeration/orbit
-- decomposition remains LOCAL COMPUTATION RECEIPT rather than Agda kernel
-- enumeration. This interaction is a canonical finite MODEL candidate, not a
-- claim that nature uses this Hamiltonian.
------------------------------------------------------------------------

h3Count : Nat
h3Count = 120

h2Count : Nat
h2Count = 270

incidenceCount : Nat
incidenceCount = 1080

h2StarSize : Nat
h2StarSize = 4

exactCoverFaceCount : Nat
exactCoverFaceCount = 30

maximumAgreementEdges : Nat
maximumAgreementEdges = 180

firstExcitationAgreementEdges : Nat
firstExcitationAgreementEdges = 177

dimensionlessDefectGap : Nat
dimensionlessDefectGap = 3

groundStateExactCoverCount : Nat
groundStateExactCoverCount = 6642

groundStateWeylOrbitCount : Nat
groundStateWeylOrbitCount = 4

groundStateOrbitSizes : String
groundStateOrbitSizes = "162,1620,1620,3240"

groundStateStabilizerOrders : String
groundStateStabilizerOrders = "320,32,32,16"

candidateInteraction : String
candidateInteraction =
  "reward adjacent H3 patches iff both selected sections choose their shared incident H2 face"

record H3H2IncidenceGroundStateLocalReceipt : Set where
  constructor h3-h2-incidence-ground-state-local-receipt
  field
    same120H3CarrierUsed : Bool
    same270H2CarrierUsed : Bool
    same1080IncidenceFlagsUsed : Bool
    interactionUsesOnlyExistingIncidence : Bool
    everyH2StarHasFourH3 : Bool
    everySectionMakes120H2Selections : Bool
    occupancyBoundGivesMaximum180 : Bool
    equalityForcesOccupiedStarsSaturated : Bool
    maximumAgreement180PaidLocally : Bool
    exactCoverExistsPaidLocally : Bool
    exactCoverCount6642PaidLocally : Bool
    fourWeylGroundStateOrbitsPaidLocally : Bool
    orbitSizes162_1620_1620_3240PaidLocally : Bool
    stabilizers320_32_32_16PaidLocally : Bool
    occupancyCongruenceForcesDefectAtLeastThree : Bool
    onePatchFlipRealizesDefectThree : Bool
    firstExcitation177PaidLocally : Bool
    dimensionlessDefectGapThreePaidLocally : Bool
    gapThreeIdentifiedWithFibreLaplacianBySameOperatorTheorem : Bool
    groundStateEnumerationAgdaKernelProved : Bool
    physicalInteractionLawDerived : Bool
    physicalInteractionCoefficientDerived : Bool
    continuumLimitDerived : Bool
    empiricalGroundStateObserved : Bool
    boundary : String
open H3H2IncidenceGroundStateLocalReceipt public

canonicalBoundary : H3H2IncidenceGroundStateLocalReceipt
canonicalBoundary =
  h3-h2-incidence-ground-state-local-receipt
    true true true true true true true true true true true true true true
    true true true true false
    false false false false false
    "The onsite-invariant selection no-go motivates a relational interaction using only the already-owned H3-H2 incidence. Agreement is bounded by 180, exhaustive local enumeration finds 6642 exact-cover ground states in four W(E6) orbits, and occupancy congruence plus a literal one-H3 flip gives an exact dimensionless defect gap 3. The equal numerical fibre-Laplacian gap is kept separate absent a same-operator theorem. Enumeration/orbit counts are computation receipts, not Agda-kernel proofs; no physical Hamiltonian coefficient, continuum law or empirical vacuum selection is inferred."

incidenceReceipt : Incidence.H3H2PhaseIncidenceLocalReceipt
incidenceReceipt = Incidence.canonicalH3H2PhaseIncidenceLocalReceipt

onsiteNoGoBoundary : NoGo.H3H2InvariantPotentialBoundary
onsiteNoGoBoundary = NoGo.canonicalInvariantPotentialBoundary
