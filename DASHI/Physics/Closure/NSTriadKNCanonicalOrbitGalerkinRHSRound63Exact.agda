module DASHI.Physics.Closure.NSTriadKNCanonicalOrbitGalerkinRHSRound63Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- ROUND 63 / A0 RHS CLOSURE
--
-- The Round62 count-growth defect came from mapping the RHS over the full
-- reconstructed +/- list and then storing every result again as a positive
-- representative.  The correct fixed-coordinate operation is much simpler:
--
--   1. use the canonical one-representative-per-reality-orbit cutoff list;
--   2. feed exactly that sublist into the mature Round30 literal coefficient
--      mapper;
--   3. store exactly those coefficients as the coordinate derivative.
--
-- Every produced coefficient is therefore still the literal
-- viscous-plus-exhaustive-quadratic Fourier coefficient.  This module changes
-- only the coordinate enumeration, not the Navier-Stokes RHS.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Coefficient
import DASHI.Physics.Closure.NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact as Concrete
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffPhysicalVectorFieldRound62Exact as Adapter
import DASHI.Physics.Closure.NSTriadKNCanonicalRealityOrbitHalfLatticeRound63Exact as Half
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffOrbitCarrierRound63Exact as Orbit
import DASHI.Physics.Closure.NSTriadKNReconstructedOrbitCoordinateGrowthNoGoRound62Exact as Growth

positiveModeEqualZeroFalse :
  (k : Z3.FourierMode) →
  Half.leadingPositive k ≡ true →
  Output.modeEqual k Z3.zeroMode ≡ false
positiveModeEqualZeroFalse
    (Z3.mode (+ zero) (+ zero) (+ zero)) ()
positiveModeEqualZeroFalse
    (Z3.mode (+ zero) (+ zero) (+ (suc z))) selected = refl
positiveModeEqualZeroFalse
    (Z3.mode (+ zero) (+ zero) -[1+ z ]) ()
positiveModeEqualZeroFalse
    (Z3.mode (+ zero) (+ (suc y)) z) selected = refl
positiveModeEqualZeroFalse
    (Z3.mode (+ zero) -[1+ y ] z) ()
positiveModeEqualZeroFalse
    (Z3.mode (+ (suc x)) y z) selected = refl
positiveModeEqualZeroFalse
    (Z3.mode -[1+ x ] y z) ()

memberSurvivesRemoveZero :
  ∀ {k modes} →
  Output.modeEqual k Z3.zeroMode ≡ false →
  k Cube.∈ modes →
  k Cube.∈ Canonical.removeZero modes
memberSurvivesRemoveZero {modes = []} notZero ()
memberSurvivesRemoveZero {k} {modes = head ∷ tail} notZero member
  with Output.modeEqual head Z3.zeroMode
... | true with member
...   | Cube.here refl with notZero
...     | ()
...   | Cube.there rest = memberSurvivesRemoveZero notZero rest
... | false with member
...   | Cube.here equality = Cube.here equality
...   | Cube.there rest = Cube.there (memberSurvivesRemoveZero notZero rest)

canonicalModeIncludedInPhysicalSystem :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (family : Canonical.CutoffSameObjectFamily F E)
    (state : State.ReconstructedPhysicalState F E)
    (mode : Z3.FourierMode) →
  mode Cube.∈ Orbit.canonicalCutoffOrbitModes
      (Canonical.cutoff (Canonical.datumAt family state)) →
  mode Cube.∈ Audit.modes
    (Coefficient.finiteSystem
      (Concrete.physicalSystemAt
        (Adapter.canonicalStateIndexedPhysicalGalerkinSystem family) state))
canonicalModeIncludedInPhysicalSystem family state mode member =
  let
    datum = Canonical.datumAt family state
    cutoff = Canonical.cutoff datum
    selected = Orbit.canonicalCutoffMemberPositive member
    cubeMember : mode Cube.∈ Cube.cutoffModes cutoff
    cubeMember =
      Cube.cutoffModeEnumerationComplete cutoff mode
        (Orbit.canonicalCutoffMemberSound member)
    nonzeroMember : mode Cube.∈ Canonical.nonzeroCutoffModes cutoff
    nonzeroMember =
      memberSurvivesRemoveZero
        (positiveModeEqualZeroFalse mode selected)
        cubeMember
    retainedMeaning = Canonical.retainedModesAreLiteralNonzeroCutoff datum
  in
  subst
    (λ modes → mode Cube.∈ modes)
    (sym retainedMeaning)
    nonzeroMember

canonicalOrbitRHSCoeefficients :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  Canonical.CutoffSameObjectFamily F E →
  (state : State.ReconstructedPhysicalState F E) →
  List (Phase.TransverseModeCoefficient F E)
canonicalOrbitRHSCoeefficients family state =
  let
    builder = Adapter.canonicalStateIndexedPhysicalGalerkinSystem family
    source = Orbit.canonicalCutoffOrbitModes
      (Canonical.cutoff (Canonical.datumAt family state))
  in
  Concrete.mapConcreteCoefficients builder state source
    (canonicalModeIncludedInPhysicalSystem family state)

canonicalOrbitRHSCoefficientWitness :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (family : Canonical.CutoffSameObjectFamily F E)
    (state : State.ReconstructedPhysicalState F E)
    coefficient →
  coefficient State.∈ canonicalOrbitRHSCoeefficients family state →
  Concrete.LiteralCoefficientWitness
    (Adapter.canonicalStateIndexedPhysicalGalerkinSystem family)
    state coefficient
canonicalOrbitRHSCoefficientWitness family state =
  let
    builder = Adapter.canonicalStateIndexedPhysicalGalerkinSystem family
    source = Orbit.canonicalCutoffOrbitModes
      (Canonical.cutoff (Canonical.datumAt family state))
  in
  Concrete.mappedConcreteCoefficientWitness
    builder state source
    (canonicalModeIncludedInPhysicalSystem family state)

canonicalOrbitRHSState :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  Canonical.CutoffSameObjectFamily F E →
  State.ReconstructedPhysicalState F E →
  State.ReconstructedPhysicalState F E
canonicalOrbitRHSState family state =
  State.reconstructed-physical-state
    (canonicalOrbitRHSCoeefficients family state)
    outputNonzero
  where
  builder = Adapter.canonicalStateIndexedPhysicalGalerkinSystem family

  outputNonzero : ∀ coefficient →
    coefficient State.∈ canonicalOrbitRHSCoeefficients family state →
    Z3.NonZeroMode (Phase.coefficientMode coefficient)
  outputNonzero coefficient member =
    let
      witness = canonicalOrbitRHSCoefficientWitness family state coefficient member
      sourceNZ =
        Coefficient.retainedModeNonzero
          (Concrete.physicalSystemAt builder state)
          (Concrete.sourceMode witness)
          (Concrete.sourceMembership witness)
    in
    subst Z3.NonZeroMode
      (sym (Concrete.modeExact witness)) sourceNZ

canonicalOrbitRHSCountIsCoordinateCount :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (family : Canonical.CutoffSameObjectFamily F E)
    (state : State.ReconstructedPhysicalState F E) →
  Growth.length (canonicalOrbitRHSCoeefficients family state)
  ≡ Growth.length
      (Orbit.canonicalCutoffOrbitModes
        (Canonical.cutoff (Canonical.datumAt family state)))
canonicalOrbitRHSCountIsCoordinateCount family state =
  let
    builder = Adapter.canonicalStateIndexedPhysicalGalerkinSystem family
    source = Orbit.canonicalCutoffOrbitModes
      (Canonical.cutoff (Canonical.datumAt family state))
  in
  Growth.mapConcreteCoefficientsCount
    builder state source
    (canonicalModeIncludedInPhysicalSystem family state)

round63LiteralGalerkinRHSClosesCanonicalOrbitCoordinateEnumeration : Bool
round63LiteralGalerkinRHSClosesCanonicalOrbitCoordinateEnumeration = true

round63LiteralGalerkinRHSClosesCanonicalOrbitCoordinateEnumerationIsTrue :
  round63LiteralGalerkinRHSClosesCanonicalOrbitCoordinateEnumeration ≡ true
round63LiteralGalerkinRHSClosesCanonicalOrbitCoordinateEnumerationIsTrue = refl
