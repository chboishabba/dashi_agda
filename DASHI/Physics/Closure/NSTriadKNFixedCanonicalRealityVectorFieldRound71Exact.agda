module DASHI.Physics.Closure.NSTriadKNFixedCanonicalRealityVectorFieldRound71Exact where

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
-- ROUND 71 / FIXED-CUTOFF FULL-SPACE REALITY VECTOR FIELD
--
-- Construct one autonomous finite Galerkin vector field before invoking
-- Picard.  The fixed geometry contains only N, E, |k|^-2 and viscosity.  The
-- evolving state contains one arbitrary Complex3 F value for every canonical
-- positive reality-orbit representative.  No transversality proof is required
-- in the full Picard phase space.
--
-- Negative Fourier values are reconstructed by conjugation and modes outside
-- the retained reality orbits evaluate to zero.  Thus reality is built into the
-- finite state while divergence-freedom remains an invariant subspace to prove
-- for transverse initial data.
--
-- The raw Audit.FiniteComplex3GalerkinSystem already accepts arbitrary velocity
-- values and its projectedNonlinearity applies the literal Leray projector.
-- We therefore define
--
--   F_N(u)(k) = -nu |k|^2 u(k) + projectedNonlinearity(u)(k)
--
-- for arbitrary finite reality states and map it back over exactly the same
-- canonical positive mode list.  The geometry is fixed independently of u.
--
-- This closes the structural/autonomy part of the finite-real input vector
-- field.  Remaining analytic work is: identify its six-real coordinate formula
-- as a degree-two locally Lipschitz real polynomial and provide the real
-- Picard-Lindelof/continuation authority.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffOrbitCarrierRound63Exact as Orbit

record FixedCanonicalGeometry
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) : Set (lsuc r) where
  constructor fixed-canonical-geometry
  field
    cutoff : Nat
    inverseSquare : C3.ModeInverseSquare F E
    viscosity : C3.Carrier F

open FixedCanonicalGeometry public

record CanonicalModeValue {r : Level} (F : C3.RealField r) : Set r where
  constructor canonical-mode-value
  field
    mode : Z3.FourierMode
    value : C3.Complex3 F

open CanonicalModeValue public

modeList : ∀ {r} {F : C3.RealField r} → List (CanonicalModeValue F) → List Z3.FourierMode
modeList [] = []
modeList (entry ∷ rest) = mode entry ∷ modeList rest

record CanonicalRealityState
    {r : Level}
    (F : C3.RealField r)
    (N : Nat) : Set r where
  constructor canonical-reality-state
  field
    positiveValues : List (CanonicalModeValue F)
    positiveModesExact : modeList positiveValues ≡ Orbit.canonicalCutoffOrbitModes N

open CanonicalRealityState public

zeroModeValues :
  ∀ {r} (F : C3.RealField r) →
  List Z3.FourierMode → List (CanonicalModeValue F)
zeroModeValues F [] = []
zeroModeValues F (mode ∷ rest) =
  canonical-mode-value mode (C3.complex3Zero F) ∷ zeroModeValues F rest

zeroModeValuesModesExact :
  ∀ {r} (F : C3.RealField r) modes →
  modeList (zeroModeValues F modes) ≡ modes
zeroModeValuesModesExact F [] = refl
zeroModeValuesModesExact F (mode ∷ rest)
  rewrite zeroModeValuesModesExact F rest = refl

zeroCanonicalRealityState :
  ∀ {r} (F : C3.RealField r) N → CanonicalRealityState F N
zeroCanonicalRealityState F N =
  canonical-reality-state
    (zeroModeValues F (Orbit.canonicalCutoffOrbitModes N))
    (zeroModeValuesModesExact F (Orbit.canonicalCutoffOrbitModes N))

lookupPositive :
  ∀ {r} {F : C3.RealField r} →
  List (CanonicalModeValue F) → Z3.FourierMode → C3.Complex3 F
lookupPositive {F = F} [] selected = C3.complex3Zero F
lookupPositive (entry ∷ rest) selected
  with Output.modeEqual selected (mode entry)
... | true = value entry
... | false = lookupPositive rest selected

lookupNegative :
  ∀ {r} {F : C3.RealField r} →
  List (CanonicalModeValue F) → Z3.FourierMode → C3.Complex3 F
lookupNegative {F = F} [] selected = C3.complex3Zero F
lookupNegative (entry ∷ rest) selected
  with Output.modeEqual selected (Z3.negateMode (mode entry))
... | true = C3.complex3Conjugate (value entry)
... | false = lookupNegative rest selected

positiveModeOccurs :
  ∀ {r} {F : C3.RealField r} →
  List (CanonicalModeValue F) → Z3.FourierMode → Bool
positiveModeOccurs [] selected = false
positiveModeOccurs (entry ∷ rest) selected
  with Output.modeEqual selected (mode entry)
... | true = true
... | false = positiveModeOccurs rest selected

realityVelocity :
  ∀ {r} {F : C3.RealField r} {N} →
  CanonicalRealityState F N → Z3.FourierMode → C3.Complex3 F
realityVelocity state selected
  with positiveModeOccurs (positiveValues state) selected
... | true = lookupPositive (positiveValues state) selected
... | false = lookupNegative (positiveValues state) selected

-- Fixed geometry, independent of the evolving state.  Audit metadata fields
-- are proposition TYPES, so we store the actual intended propositions without
-- claiming them inhabited here.
fixedAuditSystem :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : FixedCanonicalGeometry F E)
    (state : CanonicalRealityState F (cutoff geometry)) →
  Audit.FiniteComplex3GalerkinSystem F E (inverseSquare geometry)
fixedAuditSystem {F = F} {E = E} geometry state = record
  { Audit.FiniteComplex3GalerkinSystem.cutoff = cutoff geometry
  ; Audit.FiniteComplex3GalerkinSystem.modes =
      Canonical.nonzeroCutoffModes (cutoff geometry)
  ; Audit.FiniteComplex3GalerkinSystem.triads =
      Physical.physicalTriadEnumeration (cutoff geometry)
  ; Audit.FiniteComplex3GalerkinSystem.velocity = realityVelocity state
  ; Audit.FiniteComplex3GalerkinSystem.viscosity = viscosity geometry
  ; Audit.FiniteComplex3GalerkinSystem.modeListed =
      λ mode → mode Cube.∈ Canonical.nonzeroCutoffModes (cutoff geometry)
  ; Audit.FiniteComplex3GalerkinSystem.triadListed =
      λ incidence → incidence Cube.∈
        Physical.physicalTriadEnumeration (cutoff geometry)
  ; Audit.FiniteComplex3GalerkinSystem.modesAreLiteralCutoff =
      Canonical.nonzeroCutoffModes (cutoff geometry)
        ≡ Canonical.nonzeroCutoffModes (cutoff geometry)
  ; Audit.FiniteComplex3GalerkinSystem.triadsAreLiteralEnumeration = refl
  ; Audit.FiniteComplex3GalerkinSystem.zeroModeExcluded =
      ∀ mode → mode Cube.∈ Canonical.nonzeroCutoffModes (cutoff geometry) →
        Z3.NonZeroMode mode
  ; Audit.FiniteComplex3GalerkinSystem.realityClosed =
      ∀ entry → entry Cube.∈ positiveValues state →
        realityVelocity state (Z3.negateMode (mode entry))
        ≡ C3.complex3Conjugate (value entry)
  }

viscousScalar :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : FixedCanonicalGeometry F E) →
  Z3.FourierMode → C3.Complex F
viscousScalar {F = F} geometry mode =
  C3.realEmbed F
    (C3.negate F
      (C3.multiply F
        (viscosity geometry)
        (C3.normSquared (inverseSquare geometry) mode)))

rawCanonicalRHSAt :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : FixedCanonicalGeometry F E)
    (state : CanonicalRealityState F (cutoff geometry)) →
  Z3.FourierMode → C3.Complex3 F
rawCanonicalRHSAt geometry state mode =
  C3.complex3Add
    (C3.complex3Scale
      (viscousScalar geometry mode)
      (realityVelocity state mode))
    (Audit.projectedNonlinearity (fixedAuditSystem geometry state) mode)

mapCanonicalRHS :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : FixedCanonicalGeometry F E) →
  List Z3.FourierMode →
  CanonicalRealityState F (cutoff geometry) →
  List (CanonicalModeValue F)
mapCanonicalRHS geometry [] state = []
mapCanonicalRHS geometry (mode ∷ rest) state =
  canonical-mode-value mode (rawCanonicalRHSAt geometry state mode)
  ∷ mapCanonicalRHS geometry rest state

mapCanonicalRHSModesExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : FixedCanonicalGeometry F E)
    (source : List Z3.FourierMode)
    (state : CanonicalRealityState F (cutoff geometry)) →
  modeList (mapCanonicalRHS geometry source state) ≡ source
mapCanonicalRHSModesExact geometry [] state = refl
mapCanonicalRHSModesExact geometry (mode ∷ rest) state
  rewrite mapCanonicalRHSModesExact geometry rest state = refl

fixedCanonicalRealityVectorField :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (geometry : FixedCanonicalGeometry F E) →
  CanonicalRealityState F (cutoff geometry) →
  CanonicalRealityState F (cutoff geometry)
fixedCanonicalRealityVectorField geometry state =
  canonical-reality-state
    (mapCanonicalRHS geometry
      (Orbit.canonicalCutoffOrbitModes (cutoff geometry)) state)
    (mapCanonicalRHSModesExact geometry
      (Orbit.canonicalCutoffOrbitModes (cutoff geometry)) state)

round71FixedCanonicalGeometryIndependentOfState : Bool
round71FixedCanonicalGeometryIndependentOfState = true

round71FullSpaceRealityVectorFieldConstructed : Bool
round71FullSpaceRealityVectorFieldConstructed = true

round71FullSpaceFieldUsesLiteralProjectedNonlinearity : Bool
round71FullSpaceFieldUsesLiteralProjectedNonlinearity = true

round71FullSpaceRealCoordinatePolynomialLipschitzConstructed : Bool
round71FullSpaceRealCoordinatePolynomialLipschitzConstructed = false

round71FixedCanonicalGeometryIndependentOfStateIsTrue :
  round71FixedCanonicalGeometryIndependentOfState ≡ true
round71FixedCanonicalGeometryIndependentOfStateIsTrue = refl

round71FullSpaceRealityVectorFieldConstructedIsTrue :
  round71FullSpaceRealityVectorFieldConstructed ≡ true
round71FullSpaceRealityVectorFieldConstructedIsTrue = refl

round71FullSpaceRealCoordinatePolynomialLipschitzConstructedIsFalse :
  round71FullSpaceRealCoordinatePolynomialLipschitzConstructed ≡ false
round71FullSpaceRealCoordinatePolynomialLipschitzConstructedIsFalse = refl
