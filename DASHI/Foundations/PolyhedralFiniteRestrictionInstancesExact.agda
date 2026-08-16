module DASHI.Foundations.PolyhedralFiniteRestrictionInstancesExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Instantiate the generic ContinuousIrrep -> FiniteRestriction ->
-- BranchingSpectrum -> FixedSpaceSpectrum carrier with the four independently
-- computed finite rotation lenses.  Fixed-space probes are restricted to
-- cyclic rotation orders actually present in each target group:
--
--   D4 : C2,C4
--   A4 : C2,C3
--   S4 : C2,C3,C4
--   A5 : C2,C3,C5.
--
-- No C5 probe is silently attached to S4 and no C4 probe is silently attached
-- to A5 merely because the ambient SO(3) representation admits such rotations.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Candidate
import DASHI.Foundations.FiniteRepresentationRestrictionCore as Core
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.D4SO3RestrictionJ0To35Exact as D4
import DASHI.Foundations.TetrahedralSO3RestrictionJ0To35Exact as Tet
import DASHI.Foundations.OctahedralSO3RestrictionJ0To35Exact as Oct
import DASHI.Foundations.IcosahedralSO3RestrictionJ0To35Exact as Ico
import DASHI.Foundations.PolyhedralFixedSpaceSpectrumJ0To35Exact as Fixed

------------------------------------------------------------------------
-- D4 instance.
------------------------------------------------------------------------

d4Family : Core.FiniteIrrepFamily
d4Family =
  Core.finite-irrep-family
    Candidate.D4IrrepKind
    (Candidate.A1 ∷ Candidate.A2 ∷ Candidate.B1 ∷ Candidate.B2 ∷ Candidate.E2 ∷ [])
    Candidate.irrepDimension
    "rotational D4 irreps A1,A2,B1,B2,E"

d4CoreDimensionExact :
  (j : Spin.AngularMomentum0To35) →
  Core.sumWeighted
    (Core.irreps d4Family)
    (Core.finiteIrrepDimension d4Family)
    (D4.multiplicityOf (D4.branchingSpectrum j))
  ≡ Spin.jDimension j
d4CoreDimensionExact Spin.j0 = refl
d4CoreDimensionExact Spin.j1 = refl
d4CoreDimensionExact Spin.j2 = refl
d4CoreDimensionExact Spin.j3 = refl
d4CoreDimensionExact Spin.j4 = refl
d4CoreDimensionExact Spin.j5 = refl
d4CoreDimensionExact Spin.j6 = refl
d4CoreDimensionExact Spin.j7 = refl
d4CoreDimensionExact Spin.j8 = refl
d4CoreDimensionExact Spin.j9 = refl
d4CoreDimensionExact Spin.j10 = refl
d4CoreDimensionExact Spin.j11 = refl
d4CoreDimensionExact Spin.j12 = refl
d4CoreDimensionExact Spin.j13 = refl
d4CoreDimensionExact Spin.j14 = refl
d4CoreDimensionExact Spin.j15 = refl
d4CoreDimensionExact Spin.j16 = refl
d4CoreDimensionExact Spin.j17 = refl
d4CoreDimensionExact Spin.j18 = refl
d4CoreDimensionExact Spin.j19 = refl
d4CoreDimensionExact Spin.j20 = refl
d4CoreDimensionExact Spin.j21 = refl
d4CoreDimensionExact Spin.j22 = refl
d4CoreDimensionExact Spin.j23 = refl
d4CoreDimensionExact Spin.j24 = refl
d4CoreDimensionExact Spin.j25 = refl
d4CoreDimensionExact Spin.j26 = refl
d4CoreDimensionExact Spin.j27 = refl
d4CoreDimensionExact Spin.j28 = refl
d4CoreDimensionExact Spin.j29 = refl
d4CoreDimensionExact Spin.j30 = refl
d4CoreDimensionExact Spin.j31 = refl
d4CoreDimensionExact Spin.j32 = refl
d4CoreDimensionExact Spin.j33 = refl
d4CoreDimensionExact Spin.j34 = refl
d4CoreDimensionExact Spin.j35 = refl

d4Branching :
  (j : Spin.AngularMomentum0To35) →
  Core.BranchingSpectrum (Spin.continuousSO3Irrep j) d4Family
d4Branching j =
  Core.branching-spectrum
    (D4.multiplicityOf (D4.branchingSpectrum j))
    (d4CoreDimensionExact j)
    "exact rotational-D4 restriction"

data D4FixedProbe : Set where
  d4C2 d4C4 : D4FixedProbe

d4FixedDimension :
  Spin.AngularMomentum0To35 → D4FixedProbe → Nat
d4FixedDimension j d4C2 = Fixed.fixedDimension j Fixed.C2Probe
d4FixedDimension j d4C4 = Fixed.fixedDimension j Fixed.C4Probe

d4ProbeLabel : D4FixedProbe → String
d4ProbeLabel d4C2 = "D4 C2 fixed subspace"
d4ProbeLabel d4C4 = "D4 C4 fixed subspace"

d4FixedSpaces :
  Spin.AngularMomentum0To35 → Core.FixedSpaceSpectrum
d4FixedSpaces j =
  Core.fixed-space-spectrum
    D4FixedProbe
    (d4FixedDimension j)
    d4ProbeLabel
    "fixed-space probes from cyclic rotation orders present in D4"

d4FiniteRestriction :
  (j : Spin.AngularMomentum0To35) → Core.FiniteRestriction
d4FiniteRestriction j =
  Core.finite-restriction
    (Spin.continuousSO3Irrep j)
    d4Family
    (d4Branching j)
    (d4FixedSpaces j)
    "SO(3) j restricted to rotational D4"

------------------------------------------------------------------------
-- A4 instance.
------------------------------------------------------------------------

tetrahedralMultiplicityOf :
  Tet.TetrahedralSpectrum → Tet.TetrahedralIrrep → Nat
tetrahedralMultiplicityOf spectrum Tet.T1 = Tet.multiplicityT1 spectrum
tetrahedralMultiplicityOf spectrum Tet.T1Omega = Tet.multiplicityT1Omega spectrum
tetrahedralMultiplicityOf spectrum Tet.T1OmegaSquared = Tet.multiplicityT1OmegaSquared spectrum
tetrahedralMultiplicityOf spectrum Tet.T3 = Tet.multiplicityT3 spectrum

tetrahedralFamily : Core.FiniteIrrepFamily
tetrahedralFamily =
  Core.finite-irrep-family
    Tet.TetrahedralIrrep
    (Tet.T1 ∷ Tet.T1Omega ∷ Tet.T1OmegaSquared ∷ Tet.T3 ∷ [])
    Tet.tetrahedralIrrepDimension
    "rotational tetrahedral A4 irreps 1,1omega,1omega2,3"

tetrahedralCoreDimensionExact :
  (j : Spin.AngularMomentum0To35) →
  Core.sumWeighted
    (Core.irreps tetrahedralFamily)
    (Core.finiteIrrepDimension tetrahedralFamily)
    (tetrahedralMultiplicityOf (Tet.branchingSpectrum j))
  ≡ Spin.jDimension j
tetrahedralCoreDimensionExact Spin.j0 = refl
tetrahedralCoreDimensionExact Spin.j1 = refl
tetrahedralCoreDimensionExact Spin.j2 = refl
tetrahedralCoreDimensionExact Spin.j3 = refl
tetrahedralCoreDimensionExact Spin.j4 = refl
tetrahedralCoreDimensionExact Spin.j5 = refl
tetrahedralCoreDimensionExact Spin.j6 = refl
tetrahedralCoreDimensionExact Spin.j7 = refl
tetrahedralCoreDimensionExact Spin.j8 = refl
tetrahedralCoreDimensionExact Spin.j9 = refl
tetrahedralCoreDimensionExact Spin.j10 = refl
tetrahedralCoreDimensionExact Spin.j11 = refl
tetrahedralCoreDimensionExact Spin.j12 = refl
tetrahedralCoreDimensionExact Spin.j13 = refl
tetrahedralCoreDimensionExact Spin.j14 = refl
tetrahedralCoreDimensionExact Spin.j15 = refl
tetrahedralCoreDimensionExact Spin.j16 = refl
tetrahedralCoreDimensionExact Spin.j17 = refl
tetrahedralCoreDimensionExact Spin.j18 = refl
tetrahedralCoreDimensionExact Spin.j19 = refl
tetrahedralCoreDimensionExact Spin.j20 = refl
tetrahedralCoreDimensionExact Spin.j21 = refl
tetrahedralCoreDimensionExact Spin.j22 = refl
tetrahedralCoreDimensionExact Spin.j23 = refl
tetrahedralCoreDimensionExact Spin.j24 = refl
tetrahedralCoreDimensionExact Spin.j25 = refl
tetrahedralCoreDimensionExact Spin.j26 = refl
tetrahedralCoreDimensionExact Spin.j27 = refl
tetrahedralCoreDimensionExact Spin.j28 = refl
tetrahedralCoreDimensionExact Spin.j29 = refl
tetrahedralCoreDimensionExact Spin.j30 = refl
tetrahedralCoreDimensionExact Spin.j31 = refl
tetrahedralCoreDimensionExact Spin.j32 = refl
tetrahedralCoreDimensionExact Spin.j33 = refl
tetrahedralCoreDimensionExact Spin.j34 = refl
tetrahedralCoreDimensionExact Spin.j35 = refl

tetrahedralBranching :
  (j : Spin.AngularMomentum0To35) →
  Core.BranchingSpectrum (Spin.continuousSO3Irrep j) tetrahedralFamily
tetrahedralBranching j =
  Core.branching-spectrum
    (tetrahedralMultiplicityOf (Tet.branchingSpectrum j))
    (tetrahedralCoreDimensionExact j)
    "exact rotational-tetrahedral restriction"

data TetrahedralFixedProbe : Set where
  tetrahedralC2 tetrahedralC3 : TetrahedralFixedProbe

tetrahedralFixedDimension :
  Spin.AngularMomentum0To35 → TetrahedralFixedProbe → Nat
tetrahedralFixedDimension j tetrahedralC2 = Fixed.fixedDimension j Fixed.C2Probe
tetrahedralFixedDimension j tetrahedralC3 = Fixed.fixedDimension j Fixed.C3Probe

tetrahedralProbeLabel : TetrahedralFixedProbe → String
tetrahedralProbeLabel tetrahedralC2 = "A4 C2 fixed subspace"
tetrahedralProbeLabel tetrahedralC3 = "A4 C3 fixed subspace"

tetrahedralFixedSpaces :
  Spin.AngularMomentum0To35 → Core.FixedSpaceSpectrum
tetrahedralFixedSpaces j =
  Core.fixed-space-spectrum
    TetrahedralFixedProbe
    (tetrahedralFixedDimension j)
    tetrahedralProbeLabel
    "fixed-space probes from cyclic rotation orders present in A4"

tetrahedralFiniteRestriction :
  (j : Spin.AngularMomentum0To35) → Core.FiniteRestriction
tetrahedralFiniteRestriction j =
  Core.finite-restriction
    (Spin.continuousSO3Irrep j)
    tetrahedralFamily
    (tetrahedralBranching j)
    (tetrahedralFixedSpaces j)
    "SO(3) j restricted to rotational tetrahedral A4"

------------------------------------------------------------------------
-- S4 / octahedral instance.
------------------------------------------------------------------------

data OctahedralFixedProbe : Set where
  octahedralC2 octahedralC3 octahedralC4 : OctahedralFixedProbe

octahedralFixedDimension :
  Spin.AngularMomentum0To35 → OctahedralFixedProbe → Nat
octahedralFixedDimension j octahedralC2 = Fixed.fixedDimension j Fixed.C2Probe
octahedralFixedDimension j octahedralC3 = Fixed.fixedDimension j Fixed.C3Probe
octahedralFixedDimension j octahedralC4 = Fixed.fixedDimension j Fixed.C4Probe

octahedralProbeLabel : OctahedralFixedProbe → String
octahedralProbeLabel octahedralC2 = "S4 C2 fixed subspace"
octahedralProbeLabel octahedralC3 = "S4 C3 fixed subspace"
octahedralProbeLabel octahedralC4 = "S4 C4 fixed subspace"

octahedralFixedSpaces :
  Spin.AngularMomentum0To35 → Core.FixedSpaceSpectrum
octahedralFixedSpaces j =
  Core.fixed-space-spectrum
    OctahedralFixedProbe
    (octahedralFixedDimension j)
    octahedralProbeLabel
    "fixed-space probes from cyclic rotation orders present in S4"

octahedralFiniteRestriction :
  (j : Spin.AngularMomentum0To35) → Core.FiniteRestriction
octahedralFiniteRestriction j =
  Core.finite-restriction
    (Spin.continuousSO3Irrep j)
    Oct.octahedralFamily
    (Oct.octahedralBranching j)
    (octahedralFixedSpaces j)
    "SO(3) j restricted to rotational octahedral S4"

------------------------------------------------------------------------
-- A5 / icosahedral instance.
------------------------------------------------------------------------

data IcosahedralFixedProbe : Set where
  icosahedralC2 icosahedralC3 icosahedralC5 : IcosahedralFixedProbe

icosahedralFixedDimension :
  Spin.AngularMomentum0To35 → IcosahedralFixedProbe → Nat
icosahedralFixedDimension j icosahedralC2 = Fixed.fixedDimension j Fixed.C2Probe
icosahedralFixedDimension j icosahedralC3 = Fixed.fixedDimension j Fixed.C3Probe
icosahedralFixedDimension j icosahedralC5 = Fixed.fixedDimension j Fixed.C5Probe

icosahedralProbeLabel : IcosahedralFixedProbe → String
icosahedralProbeLabel icosahedralC2 = "A5 C2 fixed subspace"
icosahedralProbeLabel icosahedralC3 = "A5 C3 fixed subspace"
icosahedralProbeLabel icosahedralC5 = "A5 C5 fixed subspace"

icosahedralFixedSpaces :
  Spin.AngularMomentum0To35 → Core.FixedSpaceSpectrum
icosahedralFixedSpaces j =
  Core.fixed-space-spectrum
    IcosahedralFixedProbe
    (icosahedralFixedDimension j)
    icosahedralProbeLabel
    "fixed-space probes from cyclic rotation orders present in A5"

icosahedralFiniteRestriction :
  (j : Spin.AngularMomentum0To35) → Core.FiniteRestriction
icosahedralFiniteRestriction j =
  Core.finite-restriction
    (Spin.continuousSO3Irrep j)
    Ico.icosahedralFamily
    (Ico.icosahedralBranching j)
    (icosahedralFixedSpaces j)
    "SO(3) j restricted to rotational icosahedral A5"

record PolyhedralRestrictionBundle
    (j : Spin.AngularMomentum0To35) : Set₁ where
  field
    d4 : Core.FiniteRestriction
    tetrahedral : Core.FiniteRestriction
    octahedral : Core.FiniteRestriction
    icosahedral : Core.FiniteRestriction

canonicalPolyhedralRestrictionBundle :
  (j : Spin.AngularMomentum0To35) → PolyhedralRestrictionBundle j
canonicalPolyhedralRestrictionBundle j =
  record
    { d4 = d4FiniteRestriction j
    ; tetrahedral = tetrahedralFiniteRestriction j
    ; octahedral = octahedralFiniteRestriction j
    ; icosahedral = icosahedralFiniteRestriction j
    }

record PolyhedralRestrictionInstanceBoundary : Set where
  field
    genericRestrictionCoreHasConcreteInstances : Bool
    genericRestrictionCoreHasConcreteInstancesIsTrue :
      genericRestrictionCoreHasConcreteInstances ≡ true

    genericWeightedDimensionObligationsDischarged : Bool
    genericWeightedDimensionObligationsDischargedIsTrue :
      genericWeightedDimensionObligationsDischarged ≡ true

    probesRestrictedToOrdersPresentInTargetGroup : Bool
    probesRestrictedToOrdersPresentInTargetGroupIsTrue :
      probesRestrictedToOrdersPresentInTargetGroup ≡ true

    fixedSpaceProbeListClaimedCompleteForAllSubgroups : Bool
    fixedSpaceProbeListClaimedCompleteForAllSubgroupsIsFalse :
      fixedSpaceProbeListClaimedCompleteForAllSubgroups ≡ false

canonicalPolyhedralRestrictionInstanceBoundary :
  PolyhedralRestrictionInstanceBoundary
canonicalPolyhedralRestrictionInstanceBoundary =
  record
    { genericRestrictionCoreHasConcreteInstances = true
    ; genericRestrictionCoreHasConcreteInstancesIsTrue = refl
    ; genericWeightedDimensionObligationsDischarged = true
    ; genericWeightedDimensionObligationsDischargedIsTrue = refl
    ; probesRestrictedToOrdersPresentInTargetGroup = true
    ; probesRestrictedToOrdersPresentInTargetGroupIsTrue = refl
    ; fixedSpaceProbeListClaimedCompleteForAllSubgroups = false
    ; fixedSpaceProbeListClaimedCompleteForAllSubgroupsIsFalse = refl
    }
