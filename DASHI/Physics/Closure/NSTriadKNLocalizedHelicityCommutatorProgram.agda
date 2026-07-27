module DASHI.Physics.Closure.NSTriadKNLocalizedHelicityCommutatorProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Venue/year: Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
-- Uses: the eight helical sign triples for one Fourier triad.
-- Relationship: uses the exact sign indexing only.  Statistical cascade
-- direction is not promoted to a pointwise deterministic PDE inequality.
--
-- Authors: Luca Biferale; Stefano Musacchio; Federico Toschi.
-- Title: "Inverse Energy Cascade in Three-Dimensional Isotropic Turbulence".
-- Venue/year: Physical Review Letters 108 (2012), 164501.
-- DOI: 10.1103/PhysRevLett.108.164501.
-- Uses: motivation for retaining homochiral sign information.
-- Relationship: the decimated/statistical conclusion is evidence, not an
-- inhabitant of any pointwise signed-class bound below.
--
-- Corrected mathematical framing (2026-07): The six-mode witness is
-- modewise helicity-balanced, so E+(k) = E-(k) at every occupied mode.
-- Computing the per-mode helical split E+-/E- is therefore redundant
-- once modewise helicity is proved zero.  A state-dependent corrector
-- chi_a(k) sign(E+(k)-E-(k)) C_k is not yet a valid Lyapunov multiplier
-- family: it is state-dependent rather than a fixed quadratic operator,
-- discontinuous where E+ = E-, and choosing the sign from the current
-- state does not automatically give a favourable sign for the nonlinear
-- derivative.  Localization survives for a subtler reason: H_chi(u) = 0
-- for every scalar chi on the witness (every summand vanishes), but H_chi
-- is not an Euler invariant because chi(k), chi(p), chi(q) are unequal
-- when p+q=k, so the triadic derivative produces cutoff-difference
-- commutators.  The decisive next computations are: (1) evaluate the
-- literal localized-helicity derivative on the six-mode witness for the
-- actual candidate cutoffs chi_a; (2) compute triadwise contributions
-- before summation, indexed by geometry and helicity triple; (3) test
-- smooth fixed weights (dyadic windows, low/high transitions), not
-- state-following signs; (4) fail fast against all modewise-balanced
-- states by searching within |u_k^+| = |u_k^-| rather than treating the
-- current witness as isolated.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (_≤_)

data HelicitySign : Set where
  plus minus : HelicitySign

record HelicityTriple : Set where
  constructor triple
  field
    left right output : HelicitySign

allEightHelicityTriples : List HelicityTriple
allEightHelicityTriples =
  triple plus plus plus ∷
  triple plus plus minus ∷
  triple plus minus plus ∷
  triple plus minus minus ∷
  triple minus plus plus ∷
  triple minus plus minus ∷
  triple minus minus plus ∷
  triple minus minus minus ∷ []

data GeometricClass : Set where
  near lowHigh highLow farLow farHigh transition residual :
    GeometricClass

record HelicalTriadClass : Set where
  constructor helical-class
  field
    geometry : GeometricClass
    signs : HelicityTriple

record LocalizedHelicityCommutator
    {m v s : Level} : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    Mode : Set m
    Vector : Set v
    Scalar : Set s
    zero : Scalar
    add subtract : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set s

    modeAdd : Mode → Mode → Mode
    vectorSubtract : Vector → Vector → Vector
    curlSymbol : Mode → Vector → Vector
    curlDifference : Mode → Mode → Vector → Vector
    localizedMultiplier : Mode → Vector → Vector
    localizedMultiplierDifference :
      Mode → Mode → Vector → Vector

    Triad : Set
    triadLeft triadRight triadOutput : Triad → Mode
    resonance : ∀ triad →
      modeAdd (triadLeft triad) (triadRight triad)
      ≡ triadOutput triad

    localizedHelicityMultiplierDifferenceIdentity :
      ∀ triad value →
      localizedMultiplierDifference
        (triadOutput triad)
        (triadRight triad)
        value
      ≡ vectorSubtract
          (localizedMultiplier (triadOutput triad) value)
          (localizedMultiplier (triadRight triad) value)

    curlSymbolTriadDifferenceExact :
      ∀ triad value →
      curlDifference
        (triadOutput triad)
        (triadRight triad)
        value
      ≡ curlSymbol (triadLeft triad) value

    localizedCurlTriadDifference : Triad → Vector → Vector

    localizedCurlMultiplierTriadDifference :
      ∀ triad value →
      localizedMultiplierDifference
        (triadOutput triad)
        (triadRight triad)
        value
      ≡ localizedCurlTriadDifference triad value

    localizedHelicityNonlinearTerm
      localizedHelicityExpandedTriadTerm : Triad → Scalar

    localizedHelicityNonlinearTriadExpansion :
      ∀ triad →
      localizedHelicityNonlinearTerm triad
      ≡ localizedHelicityExpandedTriadTerm triad

    localizedHelicitySymmetrisedTerm : Triad → Scalar
    localizedHelicitySymmetrisationIdentity :
      ∀ triad →
      localizedHelicityExpandedTriadTerm triad
      ≡ localizedHelicitySymmetrisedTerm triad

    localizedHelicityEulerDefect
      localizedHelicityCommutatorValue : Triad → Scalar

    localizedHelicityEulerDefectIsCommutator :
      ∀ triad →
      localizedHelicityEulerDefect triad
      ≡ localizedHelicityCommutatorValue triad

    lowHighGain highLowGain farLowRadiusGain
      farHighTailGain transitionBound : Triad → Scalar

    localizedHelicityLowHighCommutatorGain :
      ∀ triad →
      _≤_ (localizedHelicityCommutatorValue triad)
           (lowHighGain triad)

    localizedHelicityHighLowCommutatorGain :
      ∀ triad →
      _≤_ (localizedHelicityCommutatorValue triad)
           (highLowGain triad)

    localizedHelicityFarLowRadiusGain :
      ∀ triad →
      _≤_ (localizedHelicityCommutatorValue triad)
           (farLowRadiusGain triad)

    localizedHelicityFarHighTailGain :
      ∀ triad →
      _≤_ (localizedHelicityCommutatorValue triad)
           (farHighTailGain triad)

    localizedHelicityTransitionMultiplierBound :
      ∀ triad →
      _≤_ (localizedHelicityCommutatorValue triad)
           (transitionBound triad)

open LocalizedHelicityCommutator public

record HelicalKernelSchurProgram
    {c s : Level} : Set (lsuc (c ⊔ s)) where
  field
    Cutoff Chart State : Set c
    KernelScalar : Set s
    absoluteKernel : KernelScalar → Nat

    helicalKernel :
      Chart → Cutoff → Nat → Nat → KernelScalar

    literalKernel :
      Chart → Cutoff → Nat → Nat → KernelScalar

    helicalKernelLiteralDefinition :
      ∀ chart cutoff row column →
      helicalKernel chart cutoff row column
      ≡ literalKernel chart cutoff row column

    helicalKernelIndependentOfCutoff :
      ∀ chart cutoff₁ cutoff₂ row column →
      helicalKernel chart cutoff₁ row column
      ≡ helicalKernel chart cutoff₂ row column

    RealityOrbitCompatible SwapCompatible SignedClassCompatible :
      KernelScalar → Set s

    helicalKernelRealityOrbitCompatible :
      ∀ chart cutoff row column →
      RealityOrbitCompatible (helicalKernel chart cutoff row column)

    helicalKernelSwapCompatible :
      ∀ chart cutoff row column →
      SwapCompatible (helicalKernel chart cutoff row column)

    helicalKernelSignedClassCompatible :
      ∀ chart cutoff row column →
      SignedClassCompatible (helicalKernel chart cutoff row column)

    pointwiseNear pointwiseLowHigh pointwiseHighLow
      pointwiseFarLow pointwiseFarHigh pointwiseTransition :
      Chart → Cutoff → Nat → Nat → Nat

    helicalKernelPointwiseNearBound :
      ∀ chart cutoff row column →
      absoluteKernel (helicalKernel chart cutoff row column)
      ≤ pointwiseNear chart cutoff row column

    helicalKernelPointwiseLowHighBound :
      ∀ chart cutoff row column →
      absoluteKernel (helicalKernel chart cutoff row column)
      ≤ pointwiseLowHigh chart cutoff row column

    helicalKernelPointwiseHighLowBound :
      ∀ chart cutoff row column →
      absoluteKernel (helicalKernel chart cutoff row column)
      ≤ pointwiseHighLow chart cutoff row column

    helicalKernelPointwiseFarLowBound :
      ∀ chart cutoff row column →
      absoluteKernel (helicalKernel chart cutoff row column)
      ≤ pointwiseFarLow chart cutoff row column

    helicalKernelPointwiseFarHighBound :
      ∀ chart cutoff row column →
      absoluteKernel (helicalKernel chart cutoff row column)
      ≤ pointwiseFarHigh chart cutoff row column

    helicalKernelPointwiseTransitionBound :
      ∀ chart cutoff row column →
      absoluteKernel (helicalKernel chart cutoff row column)
      ≤ pointwiseTransition chart cutoff row column

    shellRowSum shellColumnSum : Chart → Cutoff → Nat → Nat
    rowSchurConstant columnSchurConstant : Nat

    helicalFullShellRowSchurUniform :
      ∀ chart cutoff row →
      shellRowSum chart cutoff row ≤ rowSchurConstant

    helicalFullShellColumnSchurUniform :
      ∀ chart cutoff column →
      shellColumnSum chart cutoff column ≤ columnSchurConstant

    schurInputSquared schurOutputSquared : State → Nat

    helicalFullShellSchurOperatorBound :
      ∀ state →
      schurOutputSquared state
      ≤ rowSchurConstant * columnSchurConstant * schurInputSquared state

open HelicalKernelSchurProgram public

record HelicalSignedClassProgram
    {c s : Level} : Set (lsuc (c ⊔ s)) where
  field
    Cutoff Chart State : Set c
    SignedScalar : Set s
    zero : SignedScalar
    add : SignedScalar → SignedScalar → SignedScalar
    magnitude : SignedScalar → Nat

    helicalClassContribution :
      GeometricClass → HelicityTriple →
      Chart → Cutoff → State → SignedScalar

    fullHelicalCubic : Chart → Cutoff → State → SignedScalar
    helicalSignedSevenClassSum :
      Chart → Cutoff → State → SignedScalar

    helicalCubicEqualsSignedSevenClassSum :
      ∀ chart cutoff state →
      fullHelicalCubic chart cutoff state
      ≡ helicalSignedSevenClassSum chart cutoff state

    nearLiteralKernel lowHighLiteralKernel highLowLiteralKernel
      farLowLiteralKernel farHighLiteralKernel transitionLiteralKernel :
      HelicityTriple → Chart → Cutoff → State → SignedScalar

    helicalNearClassLiteralKernel :
      ∀ signs chart cutoff state →
      helicalClassContribution near signs chart cutoff state
      ≡ nearLiteralKernel signs chart cutoff state

    helicalLowHighClassLiteralKernel :
      ∀ signs chart cutoff state →
      helicalClassContribution lowHigh signs chart cutoff state
      ≡ lowHighLiteralKernel signs chart cutoff state

    helicalHighLowClassLiteralKernel :
      ∀ signs chart cutoff state →
      helicalClassContribution highLow signs chart cutoff state
      ≡ highLowLiteralKernel signs chart cutoff state

    helicalFarLowClassLiteralKernel :
      ∀ signs chart cutoff state →
      helicalClassContribution farLow signs chart cutoff state
      ≡ farLowLiteralKernel signs chart cutoff state

    helicalFarHighClassLiteralKernel :
      ∀ signs chart cutoff state →
      helicalClassContribution farHigh signs chart cutoff state
      ≡ farHighLiteralKernel signs chart cutoff state

    helicalTransitionClassLiteralKernel :
      ∀ signs chart cutoff state →
      helicalClassContribution transition signs chart cutoff state
      ≡ transitionLiteralKernel signs chart cutoff state

    FixedChartInterval : Chart → Cutoff → State → Set

    helicalFixedChartResidualVanishes :
      ∀ signs chart cutoff state →
      FixedChartInterval chart cutoff state →
      helicalClassContribution residual signs chart cutoff state ≡ zero

    dissipation remainder : Chart → Cutoff → State → Nat

    helicalNearSignedClassBound :
      ∀ signs chart cutoff state →
      magnitude (helicalClassContribution near signs chart cutoff state)
      ≤ dissipation chart cutoff state + remainder chart cutoff state

    helicalLowHighSignedClassBound :
      ∀ signs chart cutoff state →
      magnitude (helicalClassContribution lowHigh signs chart cutoff state)
      ≤ dissipation chart cutoff state + remainder chart cutoff state

    helicalHighLowSignedClassBound :
      ∀ signs chart cutoff state →
      magnitude (helicalClassContribution highLow signs chart cutoff state)
      ≤ dissipation chart cutoff state + remainder chart cutoff state

    helicalFarLowSignedCommutatorBound :
      ∀ signs chart cutoff state →
      magnitude (helicalClassContribution farLow signs chart cutoff state)
      ≤ dissipation chart cutoff state + remainder chart cutoff state

    helicalFarHighSignedTailBound :
      ∀ signs chart cutoff state →
      magnitude (helicalClassContribution farHigh signs chart cutoff state)
      ≤ dissipation chart cutoff state + remainder chart cutoff state

    helicalTransitionSignedClassBound :
      ∀ signs chart cutoff state →
      magnitude (helicalClassContribution transition signs chart cutoff state)
      ≤ dissipation chart cutoff state + remainder chart cutoff state

    TransferCoefficient : HelicityTriple → Set s
    Favourable : HelicityTriple → Set s
    Dominant Minority : HelicityTriple → Set s

    sameHelicityTriadTransferFormula :
      ∀ signs → TransferCoefficient signs

    mixedHelicityTriadSignFormula :
      ∀ signs → TransferCoefficient signs

    sameHelicityTriadFavourableSign :
      ∀ signs →
      Favourable signs →
      TransferCoefficient signs

    dominantHelicityClassReserve :
      ∀ signs → Dominant signs → Nat

    minorityHelicityClassRemainder :
      ∀ signs → Minority signs → Nat

    helicalBeneficialSignCharacterisation :
      ∀ signs → Favourable signs → Set s

    helicalBeneficialSignedClassesRetained :
      ∀ signs chart cutoff state →
      Favourable signs →
      Set s

    helicalSignedClassBoundsAssemble :
      ∀ chart cutoff state →
      magnitude (fullHelicalCubic chart cutoff state)
      ≤ dissipation chart cutoff state + remainder chart cutoff state

open HelicalSignedClassProgram public

helicalSignGeometryProgrammeRepresented : Bool
helicalSignGeometryProgrammeRepresented = true

helicalSignGeometryProgrammeRepresentedIsTrue :
  helicalSignGeometryProgrammeRepresented ≡ true
helicalSignGeometryProgrammeRepresentedIsTrue = refl

localizedHelicityCommutatorBoundsClosed : Bool
localizedHelicityCommutatorBoundsClosed = false

localizedHelicityCommutatorBoundsClosedIsFalse :
  localizedHelicityCommutatorBoundsClosed ≡ false
localizedHelicityCommutatorBoundsClosedIsFalse = refl

sameHelicityPointwiseFavourabilityClosed : Bool
sameHelicityPointwiseFavourabilityClosed = false

sameHelicityPointwiseFavourabilityClosedIsFalse :
  sameHelicityPointwiseFavourabilityClosed ≡ false
sameHelicityPointwiseFavourabilityClosedIsFalse = refl
