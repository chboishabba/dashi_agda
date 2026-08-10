module DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Repair the last hidden quantifier in the finite Galerkin producer.  Round 33
-- proved that an arbitrary ReconstructedPhysicalState need not define a
-- function of Fourier mode: duplicate positive representatives and overlap
-- between positive and reconstructed-negative sheets must agree.  A physical
-- finite system also needs an actual cutoff.
--
-- This module therefore constructs the finite system on the exact strengthened
-- datum carrying both facts:
--
--   * same-object coefficient compatibility;
--   * reconstructed retained modes are exactly the nonzero part of the
--     concrete max-coordinate cutoff cube.
--
-- From those data, the velocity is the executable Round-33 lookup, the triads
-- are the literal exhaustive physicalTriadEnumeration, every retained mode is
-- proved nonzero, and every retained velocity coefficient is proved transverse.
-- The construction then inhabits PhysicalFiniteComplex3GalerkinSystem.
--
-- A family of such strengthened data produces the existing Round-31
-- SameCarrierSameObjectGalerkinBuilder.  No unrelated finite system can be
-- substituted.  The remaining physical producer is therefore explicit:
-- construct the cutoff-compatible strengthened state family used by the ODE,
-- rather than asking the weaker raw state type to carry information it does
-- not contain.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Coefficient
import DASHI.Physics.Closure.NSTriadKNSameCarrierSameObjectRound31Exact as Same
import DASHI.Physics.Closure.NSTriadKNSameObjectLookupConsistencyRound33Exact as Lookup

------------------------------------------------------------------------
-- Literal nonzero cutoff support.
------------------------------------------------------------------------

removeZero : List Z3.FourierMode → List Z3.FourierMode
removeZero [] = []
removeZero (mode ∷ rest)
  with Output.modeEqual mode Z3.zeroMode
... | true = removeZero rest
... | false = mode ∷ removeZero rest

nonzeroCutoffModes : Nat → List Z3.FourierMode
nonzeroCutoffModes cutoff = removeZero (Cube.cutoffModes cutoff)

------------------------------------------------------------------------
-- The reconstructed state modes are literally positive/negative orbit pairs.
------------------------------------------------------------------------

orbitModes :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  List (Phase.TransverseModeCoefficient F E) → List Z3.FourierMode
orbitModes [] = []
orbitModes (coefficient ∷ rest) =
  Phase.coefficientMode coefficient
  ∷ Phase.reconstructedNegativeMode coefficient
  ∷ orbitModes rest

reconstructedStateModesExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (state : State.ReconstructedPhysicalState F E) →
  Same.reconstructedStateModes state
  ≡ orbitModes (State.positiveOrbitCoefficients state)
reconstructedStateModesExact state = refl

reconstructedModeNonzero :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (state : State.ReconstructedPhysicalState F E)
    mode →
  mode Cube.∈ Same.reconstructedStateModes state →
  Z3.NonZeroMode mode
reconstructedModeNonzero {F = F} {E = E} state mode member =
  go (State.positiveOrbitCoefficients state)
    (λ coefficient coefficientMember → coefficientMember)
    mode
    (subst
      (mode Cube.∈_)
      (reconstructedStateModesExact state)
      member)
  where
  go :
    (coefficients : List (Phase.TransverseModeCoefficient F E)) →
    (include : ∀ coefficient →
      coefficient State.∈ coefficients →
      coefficient State.∈ State.positiveOrbitCoefficients state) →
    (selected : Z3.FourierMode) →
    selected Cube.∈ orbitModes coefficients →
    Z3.NonZeroMode selected
  go [] include selected ()
  go (coefficient ∷ rest) include selected (Cube.here equality) =
    subst Z3.NonZeroMode (sym equality)
      (State.positiveModesNonzero state coefficient
        (include coefficient (State.here refl)))
  go (coefficient ∷ rest) include selected
      (Cube.there (Cube.here equality)) =
    subst Z3.NonZeroMode (sym equality)
      (State.reconstructedNegativeModeNonzero state coefficient
        (include coefficient (State.here refl)))
  go (coefficient ∷ rest) include selected
      (Cube.there (Cube.there tailMember)) =
    go rest
      (λ tailCoefficient tailMembership →
        include tailCoefficient (State.there tailMembership))
      selected tailMember

canonicalVelocityTransverseOnRetained :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (compatibility : Lookup.SameObjectCompatibleState F E state)
    mode →
  mode Cube.∈ Same.reconstructedStateModes state →
  C3.bilinearDot3
    (C3.modeVector E mode)
    (Lookup.literalVelocityAt compatibility mode)
  ≡ C3.complexZero F
canonicalVelocityTransverseOnRetained
    {F = F} {E = E} {state = state}
    compatibility mode member =
  go (State.positiveOrbitCoefficients state)
    (λ coefficient coefficientMember → coefficientMember)
    mode
    (subst
      (mode Cube.∈_)
      (reconstructedStateModesExact state)
      member)
  where
  go :
    (coefficients : List (Phase.TransverseModeCoefficient F E)) →
    (include : ∀ coefficient →
      coefficient State.∈ coefficients →
      coefficient State.∈ State.positiveOrbitCoefficients state) →
    (selected : Z3.FourierMode) →
    selected Cube.∈ orbitModes coefficients →
    C3.bilinearDot3
      (C3.modeVector E selected)
      (Lookup.literalVelocityAt compatibility selected)
    ≡ C3.complexZero F
  go [] include selected ()
  go (coefficient ∷ rest) include selected (Cube.here equality) =
    let
      globalMember = include coefficient (State.here refl)
      atPositive :
        C3.bilinearDot3
          (C3.modeVector E (Phase.coefficientMode coefficient))
          (Lookup.literalVelocityAt compatibility
            (Phase.coefficientMode coefficient))
        ≡ C3.complexZero F
      atPositive =
        trans
          (cong
            (C3.bilinearDot3
              (C3.modeVector E (Phase.coefficientMode coefficient)))
            (Lookup.literalVelocityAtPositiveExact
              compatibility coefficient globalMember))
          (Phase.transverse coefficient)
    in
    subst
      (λ selectedMode →
        C3.bilinearDot3
          (C3.modeVector E selectedMode)
          (Lookup.literalVelocityAt compatibility selectedMode)
        ≡ C3.complexZero F)
      (sym equality)
      atPositive
  go (coefficient ∷ rest) include selected
      (Cube.there (Cube.here equality)) =
    let
      globalMember = include coefficient (State.here refl)
      atNegative :
        C3.bilinearDot3
          (C3.modeVector E (Phase.reconstructedNegativeMode coefficient))
          (Lookup.literalVelocityAt compatibility
            (Phase.reconstructedNegativeMode coefficient))
        ≡ C3.complexZero F
      atNegative =
        trans
          (cong
            (C3.bilinearDot3
              (C3.modeVector E
                (Phase.reconstructedNegativeMode coefficient)))
            (Lookup.literalVelocityAtNegativeExact
              compatibility coefficient globalMember))
          (State.reconstructedNegativeCoefficientTransverse coefficient)
    in
    subst
      (λ selectedMode →
        C3.bilinearDot3
          (C3.modeVector E selectedMode)
          (Lookup.literalVelocityAt compatibility selectedMode)
        ≡ C3.complexZero F)
      (sym equality)
      atNegative
  go (coefficient ∷ rest) include selected
      (Cube.there (Cube.there tailMember)) =
    go rest
      (λ tailCoefficient tailMembership →
        include tailCoefficient (State.there tailMembership))
      selected tailMember

------------------------------------------------------------------------
-- The strengthened same-object datum.
------------------------------------------------------------------------

record CutoffSameObjectDatum
    {r} (F : C3.RealField r) (E : C3.IntegerEmbedding F)
    (state : State.ReconstructedPhysicalState F E) : Set (lsuc r) where
  constructor cutoff-same-object-datum
  field
    compatibility : Lookup.SameObjectCompatibleState F E state
    cutoff : Nat
    inverseSquare : C3.ModeInverseSquare F E
    viscosity : C3.Carrier F

    retainedModesAreLiteralNonzeroCutoff :
      Same.reconstructedStateModes state ≡ nonzeroCutoffModes cutoff

open CutoffSameObjectDatum public

canonicalAuditFiniteSystem :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E} →
  CutoffSameObjectDatum F E state →
  Audit.FiniteComplex3GalerkinSystem F E (inverseSquare _)
canonicalAuditFiniteSystem {state = state} datum = record
  { Audit.FiniteComplex3GalerkinSystem.cutoff = cutoff datum
  ; Audit.FiniteComplex3GalerkinSystem.modes = Same.reconstructedStateModes state
  ; Audit.FiniteComplex3GalerkinSystem.triads =
      Physical.physicalTriadEnumeration (cutoff datum)
  ; Audit.FiniteComplex3GalerkinSystem.velocity =
      Lookup.literalVelocityAt (compatibility datum)
  ; Audit.FiniteComplex3GalerkinSystem.viscosity = viscosity datum
  ; Audit.FiniteComplex3GalerkinSystem.modeListed =
      λ mode → mode Cube.∈ Same.reconstructedStateModes state
  ; Audit.FiniteComplex3GalerkinSystem.triadListed =
      λ incidence → incidence Cube.∈
        Physical.physicalTriadEnumeration (cutoff datum)
  ; Audit.FiniteComplex3GalerkinSystem.modesAreLiteralCutoff =
      Same.reconstructedStateModes state ≡ nonzeroCutoffModes (cutoff datum)
  ; Audit.FiniteComplex3GalerkinSystem.triadsAreLiteralEnumeration = refl
  ; Audit.FiniteComplex3GalerkinSystem.zeroModeExcluded =
      ∀ mode → mode Cube.∈ Same.reconstructedStateModes state →
        Z3.NonZeroMode mode
  ; Audit.FiniteComplex3GalerkinSystem.realityClosed =
      Lookup.SameObjectCompatibleState F E state
  }

canonicalPhysicalFiniteSystem :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E} →
  CutoffSameObjectDatum F E state →
  Coefficient.PhysicalFiniteComplex3GalerkinSystem F
canonicalPhysicalFiniteSystem {F = F} {E = E} {state = state} datum = record
  { Coefficient.PhysicalFiniteComplex3GalerkinSystem.physicalEmbedding = E
  ; Coefficient.PhysicalFiniteComplex3GalerkinSystem.physicalInverseSquare =
      inverseSquare datum
  ; Coefficient.PhysicalFiniteComplex3GalerkinSystem.finiteSystem =
      canonicalAuditFiniteSystem datum
  ; Coefficient.PhysicalFiniteComplex3GalerkinSystem.viscosity = viscosity datum
  ; Coefficient.PhysicalFiniteComplex3GalerkinSystem.retainedModeNonzero =
      reconstructedModeNonzero state
  ; Coefficient.PhysicalFiniteComplex3GalerkinSystem.retainedVelocityTransverse =
      canonicalVelocityTransverseOnRetained (compatibility datum)
  }

canonicalFiniteSystemEmbeddingExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : CutoffSameObjectDatum F E state) →
  Audit.integerEmbedding
    (Coefficient.finiteSystem (canonicalPhysicalFiniteSystem datum))
  ≡ E
canonicalFiniteSystemEmbeddingExact datum = refl

canonicalFiniteSystemPositiveExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : CutoffSameObjectDatum F E state)
    coefficient →
  coefficient State.∈ State.positiveOrbitCoefficients state →
  Audit.velocityAt
    (Coefficient.finiteSystem (canonicalPhysicalFiniteSystem datum))
    (Phase.coefficientMode coefficient)
  ≡ Phase.coefficientValue coefficient
canonicalFiniteSystemPositiveExact datum coefficient member =
  Lookup.literalVelocityAtPositiveExact
    (compatibility datum) coefficient member

canonicalFiniteSystemNegativeExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : CutoffSameObjectDatum F E state)
    coefficient →
  coefficient State.∈ State.positiveOrbitCoefficients state →
  Audit.velocityAt
    (Coefficient.finiteSystem (canonicalPhysicalFiniteSystem datum))
    (Phase.reconstructedNegativeMode coefficient)
  ≡ Phase.reconstructedNegativeValue coefficient
canonicalFiniteSystemNegativeExact datum coefficient member =
  Lookup.literalVelocityAtNegativeExact
    (compatibility datum) coefficient member

canonicalFiniteSystemRetainedModesExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : CutoffSameObjectDatum F E state) →
  Audit.modes
    (Coefficient.finiteSystem (canonicalPhysicalFiniteSystem datum))
  ≡ Same.reconstructedStateModes state
canonicalFiniteSystemRetainedModesExact datum = refl

------------------------------------------------------------------------
-- A family of strengthened data closes the existing Round-31 builder.
------------------------------------------------------------------------

record CutoffSameObjectFamily
    {r} (F : C3.RealField r) (E : C3.IntegerEmbedding F) : Set (lsuc r) where
  field
    datumAt :
      (state : State.ReconstructedPhysicalState F E) →
      CutoffSameObjectDatum F E state

open CutoffSameObjectFamily public

canonicalSameCarrierSameObjectBuilder :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  CutoffSameObjectFamily F E →
  Same.SameCarrierSameObjectGalerkinBuilder F E
canonicalSameCarrierSameObjectBuilder family = record
  { Same.SameCarrierSameObjectGalerkinBuilder.physicalSystemAt =
      λ state → canonicalPhysicalFiniteSystem (datumAt family state)
  ; Same.SameCarrierSameObjectGalerkinBuilder.embeddingExact =
      λ state → canonicalFiniteSystemEmbeddingExact (datumAt family state)
  ; Same.SameCarrierSameObjectGalerkinBuilder.positiveVelocityExact =
      λ state coefficient member →
        canonicalFiniteSystemPositiveExact
          (datumAt family state) coefficient member
  ; Same.SameCarrierSameObjectGalerkinBuilder.negativeVelocityExact =
      λ state coefficient member →
        canonicalFiniteSystemNegativeExact
          (datumAt family state) coefficient member
  ; Same.SameCarrierSameObjectGalerkinBuilder.retainedModesExact =
      λ state → canonicalFiniteSystemRetainedModesExact (datumAt family state)
  }

canonicalCutoffSameObjectFiniteSystemClosed : Bool
canonicalCutoffSameObjectFiniteSystemClosed = true

cutoffSameObjectFamilyConstructedForRawStateCarrier : Bool
cutoffSameObjectFamilyConstructedForRawStateCarrier = false

canonicalCutoffSameObjectFiniteSystemClosedIsTrue :
  canonicalCutoffSameObjectFiniteSystemClosed ≡ true
canonicalCutoffSameObjectFiniteSystemClosedIsTrue = refl

cutoffSameObjectFamilyConstructedForRawStateCarrierIsFalse :
  cutoffSameObjectFamilyConstructedForRawStateCarrier ≡ false
cutoffSameObjectFamilyConstructedForRawStateCarrierIsFalse = refl
