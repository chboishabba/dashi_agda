module DASHI.Physics.Closure.NSTriadKNCanonicalRHSFiniteRealSlotAlignmentRound71Exact where

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
-- ROUND 71 / CANONICAL RHS -> FINITE REAL SLOT ALIGNMENT
--
-- The canonical Round63 RHS is built by mapConcreteCoefficients over exactly
-- the canonical one-representative-per-reality-orbit mode list.  This file
-- proves the stronger ordered statement that erasing the output coefficient
-- modes gives EXACTLY that source list, not merely a count equality or
-- pointwise membership theorem.
--
-- Combining this with Round71's physical coefficient -> six-real-slot encoding
-- transports the actual canonical RHS output into the exact
-- CanonicalCutoffRealCoordinateState slot carrier.
--
-- This closes the OUTPUT-alignment half of the finite-real ODE bridge.  The
-- still-hard input-side theorem is to define/evaluate the same literal projected
-- NS polynomial vector field on arbitrary finite-real coordinate states (or an
-- equivalent transverse chart) and prove it agrees with the physical RHS on
-- encoded physical states.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Coefficient
import DASHI.Physics.Closure.NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact as Concrete
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffPhysicalVectorFieldRound62Exact as Adapter
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffOrbitCarrierRound63Exact as Orbit
import DASHI.Physics.Closure.NSTriadKNCanonicalOrbitGalerkinRHSRound63Exact as RHS
import DASHI.Physics.Closure.NSTriadKNFiniteRealCanonicalCoordinateCarrierRound71Exact as Finite
import DASHI.Physics.Closure.NSTriadKNPhysicalCoefficientFiniteRealEncodingRound71Exact as Encoding

mappedConcreteCoefficientModesExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (builder : Concrete.StateIndexedPhysicalGalerkinSystem F E)
    (state : State.ReconstructedPhysicalState F E)
    (source : List Z3.FourierMode)
    (sourceIncluded : ∀ mode → mode Cube.∈ source →
      mode Cube.∈
        DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit.modes
          (Coefficient.finiteSystem (Concrete.physicalSystemAt builder state))) →
  Encoding.coefficientModes
    (Concrete.mapConcreteCoefficients builder state source sourceIncluded)
  ≡ source
mappedConcreteCoefficientModesExact builder state [] sourceIncluded = refl
mappedConcreteCoefficientModesExact
    builder state (mode ∷ rest) sourceIncluded =
  let
    headCoefficient =
      Coefficient.literalTransverseCoefficient
        (Concrete.physicalSystemAt builder state)
        mode
        (sourceIncluded mode (Cube.here refl))
    tailIncluded = λ selected member →
      sourceIncluded selected (Cube.there member)
  in
  cong (mode ∷_)
    (mappedConcreteCoefficientModesExact
      builder state rest tailIncluded)
  where
  -- Rewriting the transported head mode to the source mode is definitionally
  -- the only non-recursive content of this step.
  _ = Concrete.transportCoefficientMode
        (Concrete.embeddingExact builder state)
        (Coefficient.literalTransverseCoefficient
          (Concrete.physicalSystemAt builder state)
          mode
          (sourceIncluded mode (Cube.here refl)))

canonicalOrbitRHSCoefficientModesExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (family : Canonical.CutoffSameObjectFamily F E)
    (state : State.ReconstructedPhysicalState F E) →
  Encoding.coefficientModes (RHS.canonicalOrbitRHSCoefficients family state)
  ≡ Orbit.canonicalCutoffOrbitModes
      (Canonical.cutoff (Canonical.datumAt family state))
canonicalOrbitRHSCoefficientModesExact family state =
  let
    builder = Adapter.canonicalStateIndexedPhysicalGalerkinSystem family
    source = Orbit.canonicalCutoffOrbitModes
      (Canonical.cutoff (Canonical.datumAt family state))
  in
  mappedConcreteCoefficientModesExact
    builder state source
    (RHS.canonicalModeIncludedInPhysicalSystem family state)

transportFiniteRealSlotState :
  ∀ {r} {F : C3.RealField r} {left right} →
  left ≡ right →
  Finite.FiniteRealCoordinateState F left →
  Finite.FiniteRealCoordinateState F right
transportFiniteRealSlotState equality state =
  subst (Finite.FiniteRealCoordinateState _) equality state

canonicalOrbitRHSFiniteRealState :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (family : Canonical.CutoffSameObjectFamily F E)
    (state : State.ReconstructedPhysicalState F E) →
  Finite.CanonicalCutoffRealCoordinateState F
    (Canonical.cutoff (Canonical.datumAt family state))
canonicalOrbitRHSFiniteRealState family state =
  let
    coefficients = RHS.canonicalOrbitRHSCoefficients family state
    encoded = Encoding.finiteRealStateFromPhysicalCoefficients coefficients
    modeEquality = canonicalOrbitRHSCoefficientModesExact family state
    slotEquality = cong Finite.slotsForModes modeEquality
  in
  transportFiniteRealSlotState slotEquality encoded

round71CanonicalRHSModeOrderEqualsCanonicalSource : Bool
round71CanonicalRHSModeOrderEqualsCanonicalSource = true

round71CanonicalRHSOutputOnFiniteRealCarrier : Bool
round71CanonicalRHSOutputOnFiniteRealCarrier = true

round71FiniteRealInputVectorFieldConstructed : Bool
round71FiniteRealInputVectorFieldConstructed = false

round71CanonicalRHSModeOrderEqualsCanonicalSourceIsTrue :
  round71CanonicalRHSModeOrderEqualsCanonicalSource ≡ true
round71CanonicalRHSModeOrderEqualsCanonicalSourceIsTrue = refl

round71CanonicalRHSOutputOnFiniteRealCarrierIsTrue :
  round71CanonicalRHSOutputOnFiniteRealCarrier ≡ true
round71CanonicalRHSOutputOnFiniteRealCarrierIsTrue = refl

round71FiniteRealInputVectorFieldConstructedIsFalse :
  round71FiniteRealInputVectorFieldConstructed ≡ false
round71FiniteRealInputVectorFieldConstructedIsFalse = refl
