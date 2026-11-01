module DASHI.Physics.Closure.NSTriadKNSameObjectLookupConsistencyRound33Exact where

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
-- DASHI CONTRIBUTION
--
-- Close the executable lookup part of the Round-31 same-object leaf and
-- expose the exact obstruction hidden by the earlier state type.
--
-- Any SameCarrierSameObjectGalerkinBuilder forces:
--
--   * equal stored values whenever two positive representatives have the
--     same Fourier mode;
--   * agreement between a positive representative and a reconstructed
--     negative representative whenever their Fourier modes coincide.
--
-- Hence a state containing conflicting duplicate representatives cannot
-- admit the claimed builder.  Conversely, those two compatibility laws are
-- sufficient to construct one total coefficient lookup whose positive and
-- reconstructed-negative evaluations are exact.  The construction uses the
-- repository's executable equality on Z^3 and does not replace the physical
-- state by an extensionally similar coordinate object.
--
-- This closes the finite lookup/gluing subleaf.  Supplying the cutoff,
-- viscosity, inverse-square data and literal FiniteComplex3GalerkinSystem
-- remains a separate producer.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Coefficient
import DASHI.Physics.Closure.NSTriadKNSameCarrierSameObjectRound31Exact as Same

------------------------------------------------------------------------
-- Compatibility laws forced by any literal same-object builder.
------------------------------------------------------------------------

PositiveModeFunctional :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  List (Phase.TransverseModeCoefficient F E) → Set r
PositiveModeFunctional coefficients =
  ∀ left right →
  left State.∈ coefficients →
  right State.∈ coefficients →
  Phase.coefficientMode left ≡ Phase.coefficientMode right →
  Phase.coefficientValue left ≡ Phase.coefficientValue right

PositiveNegativeCompatible :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  List (Phase.TransverseModeCoefficient F E) → Set r
PositiveNegativeCompatible coefficients =
  ∀ positive source →
  positive State.∈ coefficients →
  source State.∈ coefficients →
  Phase.coefficientMode positive
    ≡ Phase.reconstructedNegativeMode source →
  Phase.coefficientValue positive
    ≡ Phase.reconstructedNegativeValue source

builderVelocity :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  Same.SameCarrierSameObjectGalerkinBuilder F E →
  State.ReconstructedPhysicalState F E →
  Z3.FourierMode → C3.Complex3 F
builderVelocity builder state =
  Audit.velocityAt
    (Coefficient.finiteSystem (Same.physicalSystemAt builder state))

builderForcesPositiveModeFunctional :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (builder : Same.SameCarrierSameObjectGalerkinBuilder F E)
    (state : State.ReconstructedPhysicalState F E) →
  PositiveModeFunctional (State.positiveOrbitCoefficients state)
builderForcesPositiveModeFunctional builder state
    left right leftMember rightMember sameMode =
  trans
    (sym
      (Same.positiveVelocityExact
        builder state left leftMember))
    (trans
      (cong (builderVelocity builder state) sameMode)
      (Same.positiveVelocityExact
        builder state right rightMember))

builderForcesPositiveNegativeCompatibility :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (builder : Same.SameCarrierSameObjectGalerkinBuilder F E)
    (state : State.ReconstructedPhysicalState F E) →
  PositiveNegativeCompatible (State.positiveOrbitCoefficients state)
builderForcesPositiveNegativeCompatibility builder state
    positive source positiveMember sourceMember sameMode =
  trans
    (sym
      (Same.positiveVelocityExact
        builder state positive positiveMember))
    (trans
      (cong (builderVelocity builder state) sameMode)
      (Same.negativeVelocityExact
        builder state source sourceMember))

record PositiveModeConflict
    {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (state : State.ReconstructedPhysicalState F E) : Set r where
  constructor positive-mode-conflict
  field
    left right : Phase.TransverseModeCoefficient F E
    leftMember :
      left State.∈ State.positiveOrbitCoefficients state
    rightMember :
      right State.∈ State.positiveOrbitCoefficients state
    sameMode :
      Phase.coefficientMode left ≡ Phase.coefficientMode right
    positiveValuesConflict :
      Phase.coefficientValue left ≡ Phase.coefficientValue right → ⊥

open PositiveModeConflict public

positiveModeConflictRefutesBuilder :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E} →
  PositiveModeConflict state →
  Same.SameCarrierSameObjectGalerkinBuilder F E → ⊥
positiveModeConflictRefutesBuilder {state = state} conflict builder =
  positiveValuesConflict conflict
    (builderForcesPositiveModeFunctional builder state
      (left conflict) (right conflict)
      (leftMember conflict) (rightMember conflict)
      (sameMode conflict))

record PositiveNegativeConflict
    {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (state : State.ReconstructedPhysicalState F E) : Set r where
  constructor positive-negative-conflict
  field
    positive source : Phase.TransverseModeCoefficient F E
    positiveMember :
      positive State.∈ State.positiveOrbitCoefficients state
    sourceMember :
      source State.∈ State.positiveOrbitCoefficients state
    samePhysicalMode :
      Phase.coefficientMode positive
        ≡ Phase.reconstructedNegativeMode source
    sheetValuesConflict :
      Phase.coefficientValue positive
        ≡ Phase.reconstructedNegativeValue source → ⊥

open PositiveNegativeConflict public

positiveNegativeConflictRefutesBuilder :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E} →
  PositiveNegativeConflict state →
  Same.SameCarrierSameObjectGalerkinBuilder F E → ⊥
positiveNegativeConflictRefutesBuilder {state = state} conflict builder =
  sheetValuesConflict conflict
    (builderForcesPositiveNegativeCompatibility builder state
      (positive conflict) (source conflict)
      (positiveMember conflict) (sourceMember conflict)
      (samePhysicalMode conflict))

------------------------------------------------------------------------
-- Executable lookup on one compatible reality-orbit state.
------------------------------------------------------------------------

lookupPositive :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  List (Phase.TransverseModeCoefficient F E) →
  Z3.FourierMode → C3.Complex3 F
lookupPositive {F = F} [] mode = C3.complex3Zero F
lookupPositive (head ∷ rest) mode
  with Output.modeEqual mode (Phase.coefficientMode head)
... | true = Phase.coefficientValue head
... | false = lookupPositive rest mode

lookupNegative :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  List (Phase.TransverseModeCoefficient F E) →
  Z3.FourierMode → C3.Complex3 F
lookupNegative {F = F} [] mode = C3.complex3Zero F
lookupNegative (head ∷ rest) mode
  with Output.modeEqual mode (Phase.reconstructedNegativeMode head)
... | true = Phase.reconstructedNegativeValue head
... | false = lookupNegative rest mode

lookupPositiveExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {coefficients : List (Phase.TransverseModeCoefficient F E)} →
  PositiveModeFunctional coefficients →
  ∀ coefficient →
  coefficient State.∈ coefficients →
  lookupPositive coefficients (Phase.coefficientMode coefficient)
    ≡ Phase.coefficientValue coefficient
lookupPositiveExact {coefficients = []} functional coefficient ()
lookupPositiveExact {coefficients = head ∷ rest}
    functional coefficient (State.here refl)
  rewrite Output.modeEqualRefl (Phase.coefficientMode head) = refl
lookupPositiveExact {coefficients = head ∷ rest}
    functional coefficient (State.there member)
  with Output.modeEqual
    (Phase.coefficientMode coefficient)
    (Phase.coefficientMode head)
... | true =
  sym
    (functional coefficient head
      (State.there member) (State.here refl)
      (Output.modeEqualSound refl))
... | false =
  lookupPositiveExact
    {coefficients = rest}
    (λ left right leftMember rightMember sameMode →
      functional left right
        (State.there leftMember)
        (State.there rightMember)
        sameMode)
    coefficient member

negateModeReflectsEquality :
  ∀ {left right} →
  Z3.negateMode left ≡ Z3.negateMode right →
  left ≡ right
negateModeReflectsEquality {left} {right} equality =
  trans
    (sym (Symmetry.negateModeInvolutive left))
    (trans
      (cong Z3.negateMode equality)
      (Symmetry.negateModeInvolutive right))

NegativeModeFunctional :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  List (Phase.TransverseModeCoefficient F E) → Set r
NegativeModeFunctional coefficients =
  ∀ left right →
  left State.∈ coefficients →
  right State.∈ coefficients →
  Phase.reconstructedNegativeMode left
    ≡ Phase.reconstructedNegativeMode right →
  Phase.reconstructedNegativeValue left
    ≡ Phase.reconstructedNegativeValue right

positiveFunctionalImpliesNegativeFunctional :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {coefficients : List (Phase.TransverseModeCoefficient F E)} →
  PositiveModeFunctional coefficients →
  NegativeModeFunctional coefficients
positiveFunctionalImpliesNegativeFunctional functional
    left right leftMember rightMember sameMode =
  cong
    (λ value → C3.complex3Conjugate value)
    (functional left right leftMember rightMember
      (negateModeReflectsEquality sameMode))

lookupNegativeExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {coefficients : List (Phase.TransverseModeCoefficient F E)} →
  NegativeModeFunctional coefficients →
  ∀ coefficient →
  coefficient State.∈ coefficients →
  lookupNegative coefficients
      (Phase.reconstructedNegativeMode coefficient)
    ≡ Phase.reconstructedNegativeValue coefficient
lookupNegativeExact {coefficients = []} functional coefficient ()
lookupNegativeExact {coefficients = head ∷ rest}
    functional coefficient (State.here refl)
  rewrite Output.modeEqualRefl
    (Phase.reconstructedNegativeMode head) = refl
lookupNegativeExact {coefficients = head ∷ rest}
    functional coefficient (State.there member)
  with Output.modeEqual
    (Phase.reconstructedNegativeMode coefficient)
    (Phase.reconstructedNegativeMode head)
... | true =
  sym
    (functional coefficient head
      (State.there member) (State.here refl)
      (Output.modeEqualSound refl))
... | false =
  lookupNegativeExact
    {coefficients = rest}
    (λ left right leftMember rightMember sameMode →
      functional left right
        (State.there leftMember)
        (State.there rightMember)
        sameMode)
    coefficient member

positiveModeOccurs :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  List (Phase.TransverseModeCoefficient F E) →
  Z3.FourierMode → Bool
positiveModeOccurs [] mode = false
positiveModeOccurs (head ∷ rest) mode
  with Output.modeEqual mode (Phase.coefficientMode head)
... | true = true
... | false = positiveModeOccurs rest mode

positiveModeOccursComplete :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {coefficients : List (Phase.TransverseModeCoefficient F E)}
    {coefficient} →
  coefficient State.∈ coefficients →
  positiveModeOccurs coefficients (Phase.coefficientMode coefficient)
    ≡ true
positiveModeOccursComplete {coefficients = []} ()
positiveModeOccursComplete {coefficients = head ∷ rest}
    (State.here refl)
  rewrite Output.modeEqualRefl (Phase.coefficientMode head) = refl
positiveModeOccursComplete {coefficients = head ∷ rest}
    {coefficient} (State.there member)
  with Output.modeEqual
    (Phase.coefficientMode coefficient)
    (Phase.coefficientMode head)
... | true = refl
... | false = positiveModeOccursComplete member

data PositiveModeHit
    {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (coefficients : List (Phase.TransverseModeCoefficient F E))
    (mode : Z3.FourierMode) : Set r where
  positive-mode-hit :
    (coefficient : Phase.TransverseModeCoefficient F E) →
    coefficient State.∈ coefficients →
    mode ≡ Phase.coefficientMode coefficient →
    PositiveModeHit coefficients mode

positiveModeOccursSound :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {coefficients : List (Phase.TransverseModeCoefficient F E)}
    {mode} →
  positiveModeOccurs coefficients mode ≡ true →
  PositiveModeHit coefficients mode
positiveModeOccursSound {coefficients = []} ()
positiveModeOccursSound {coefficients = head ∷ rest} {mode} proof
  with Output.modeEqual mode (Phase.coefficientMode head)
... | true =
  positive-mode-hit head
    (State.here refl)
    (Output.modeEqualSound refl)
... | false
  with positiveModeOccursSound
    {coefficients = rest} {mode = mode} proof
...   | positive-mode-hit coefficient member sameMode =
      positive-mode-hit coefficient (State.there member) sameMode

record SameObjectCompatibleState
    {r} (F : C3.RealField r) (E : C3.IntegerEmbedding F)
    (state : State.ReconstructedPhysicalState F E) : Set r where
  constructor same-object-compatible-state
  field
    positiveFunctional :
      PositiveModeFunctional (State.positiveOrbitCoefficients state)
    positiveNegativeCompatibility :
      PositiveNegativeCompatible (State.positiveOrbitCoefficients state)

open SameObjectCompatibleState public

builderCompatibleState :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (builder : Same.SameCarrierSameObjectGalerkinBuilder F E)
    (state : State.ReconstructedPhysicalState F E) →
  SameObjectCompatibleState F E state
builderCompatibleState builder state =
  same-object-compatible-state
    (builderForcesPositiveModeFunctional builder state)
    (builderForcesPositiveNegativeCompatibility builder state)

literalVelocityAt :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E} →
  SameObjectCompatibleState F E state →
  Z3.FourierMode → C3.Complex3 F
literalVelocityAt {state = state} compatibility mode
  with positiveModeOccurs
    (State.positiveOrbitCoefficients state) mode
... | true =
  lookupPositive (State.positiveOrbitCoefficients state) mode
... | false =
  lookupNegative (State.positiveOrbitCoefficients state) mode

literalVelocityAtPositiveExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (compatibility : SameObjectCompatibleState F E state)
    coefficient →
  coefficient State.∈ State.positiveOrbitCoefficients state →
  literalVelocityAt compatibility (Phase.coefficientMode coefficient)
    ≡ Phase.coefficientValue coefficient
literalVelocityAtPositiveExact compatibility coefficient member
  rewrite positiveModeOccursComplete member =
  lookupPositiveExact
    (positiveFunctional compatibility)
    coefficient member

literalVelocityAtNegativeExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (compatibility : SameObjectCompatibleState F E state)
    coefficient →
  coefficient State.∈ State.positiveOrbitCoefficients state →
  literalVelocityAt compatibility
      (Phase.reconstructedNegativeMode coefficient)
    ≡ Phase.reconstructedNegativeValue coefficient
literalVelocityAtNegativeExact {state = state}
    compatibility coefficient member
  with positiveModeOccurs
    (State.positiveOrbitCoefficients state)
    (Phase.reconstructedNegativeMode coefficient)
... | true
  with positiveModeOccursSound
    {coefficients = State.positiveOrbitCoefficients state}
    {mode = Phase.reconstructedNegativeMode coefficient}
    refl
...   | positive-mode-hit positive positiveMember sameMode =
      trans
        (lookupPositiveExact
          (positiveFunctional compatibility)
          positive positiveMember)
        (positiveNegativeCompatibility compatibility
          positive coefficient positiveMember member
          (sym sameMode))
... | false =
  lookupNegativeExact
    (positiveFunctionalImpliesNegativeFunctional
      (positiveFunctional compatibility))
    coefficient member

record CanonicalSameObjectVelocityLookup
    {r} (F : C3.RealField r) (E : C3.IntegerEmbedding F)
    (state : State.ReconstructedPhysicalState F E) : Set r where
  constructor canonical-same-object-velocity-lookup
  field
    canonicalVelocityAt : Z3.FourierMode → C3.Complex3 F
    canonicalRetainedModes : List Z3.FourierMode

    canonicalPositiveExact :
      ∀ coefficient →
      coefficient State.∈ State.positiveOrbitCoefficients state →
      canonicalVelocityAt (Phase.coefficientMode coefficient)
        ≡ Phase.coefficientValue coefficient

    canonicalNegativeExact :
      ∀ coefficient →
      coefficient State.∈ State.positiveOrbitCoefficients state →
      canonicalVelocityAt (Phase.reconstructedNegativeMode coefficient)
        ≡ Phase.reconstructedNegativeValue coefficient

    canonicalRetainedModesExact :
      canonicalRetainedModes ≡ Same.reconstructedStateModes state

open CanonicalSameObjectVelocityLookup public

canonicalSameObjectVelocityLookup :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E} →
  SameObjectCompatibleState F E state →
  CanonicalSameObjectVelocityLookup F E state
canonicalSameObjectVelocityLookup {state = state} compatibility =
  canonical-same-object-velocity-lookup
    (literalVelocityAt compatibility)
    (Same.reconstructedStateModes state)
    (literalVelocityAtPositiveExact compatibility)
    (literalVelocityAtNegativeExact compatibility)
    refl

builderCanonicalVelocityLookup :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (builder : Same.SameCarrierSameObjectGalerkinBuilder F E)
    (state : State.ReconstructedPhysicalState F E) →
  CanonicalSameObjectVelocityLookup F E state
builderCanonicalVelocityLookup builder state =
  canonicalSameObjectVelocityLookup
    (builderCompatibleState builder state)

builderAndCanonicalPositiveAgree :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (builder : Same.SameCarrierSameObjectGalerkinBuilder F E)
    (state : State.ReconstructedPhysicalState F E)
    coefficient →
  coefficient State.∈ State.positiveOrbitCoefficients state →
  builderVelocity builder state (Phase.coefficientMode coefficient)
  ≡ canonicalVelocityAt
      (builderCanonicalVelocityLookup builder state)
      (Phase.coefficientMode coefficient)
builderAndCanonicalPositiveAgree builder state coefficient member =
  trans
    (Same.positiveVelocityExact
      builder state coefficient member)
    (sym
      (canonicalPositiveExact
        (builderCanonicalVelocityLookup builder state)
        coefficient member))

builderAndCanonicalNegativeAgree :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (builder : Same.SameCarrierSameObjectGalerkinBuilder F E)
    (state : State.ReconstructedPhysicalState F E)
    coefficient →
  coefficient State.∈ State.positiveOrbitCoefficients state →
  builderVelocity builder state
      (Phase.reconstructedNegativeMode coefficient)
  ≡ canonicalVelocityAt
      (builderCanonicalVelocityLookup builder state)
      (Phase.reconstructedNegativeMode coefficient)
builderAndCanonicalNegativeAgree builder state coefficient member =
  trans
    (Same.negativeVelocityExact
      builder state coefficient member)
    (sym
      (canonicalNegativeExact
        (builderCanonicalVelocityLookup builder state)
        coefficient member))

sameObjectCompatibilityNecessityClosed : Bool
sameObjectCompatibilityNecessityClosed = true

canonicalRetainedVelocityLookupClosed : Bool
canonicalRetainedVelocityLookupClosed = true

canonicalFiniteGalerkinSystemBuilderConstructed : Bool
canonicalFiniteGalerkinSystemBuilderConstructed = false

sameObjectCompatibilityNecessityClosedIsTrue :
  sameObjectCompatibilityNecessityClosed ≡ true
sameObjectCompatibilityNecessityClosedIsTrue = refl

canonicalRetainedVelocityLookupClosedIsTrue :
  canonicalRetainedVelocityLookupClosed ≡ true
canonicalRetainedVelocityLookupClosedIsTrue = refl

canonicalFiniteGalerkinSystemBuilderConstructedIsFalse :
  canonicalFiniteGalerkinSystemBuilderConstructed ≡ false
canonicalFiniteGalerkinSystemBuilderConstructedIsFalse = refl
