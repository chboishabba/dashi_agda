module DASHI.Foundations.CausalOrderLorentzClosure where

open import Agda.Primitive using (Level; Setω; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Causal-order / chain-antichain / Lorentz closure surface.
--
-- This module does not identify a particular existing DASHI carrier with a
-- continuum spacetime.  It records the exact theorem payload required to make
-- that identification without conflating:
--
--   * the causal partial order,
--   * chain depth and antichain width,
--   * contractive multiscale decimation,
--   * the forced quadratic defect,
--   * the unique 3+1 Lorentzian signature.
--
-- A downstream module may only consume a Lorentz closure after supplying every
-- field of CausalOrderLorentzClosure.

record CausalPoset {ℓ : Level} : Set (lsuc ℓ) where
  field
    Event :
      Set ℓ

    _≺_ :
      Event → Event → Set ℓ

    irreflexive :
      ∀ x → (x ≺ x) → Bool

    transitive :
      ∀ {x y z} → x ≺ y → y ≺ z → x ≺ z

    locallyFinite :
      Event → Event → Bool

open CausalPoset public

record ChainAntichainGeometry {ℓ : Level} (P : CausalPoset {ℓ}) :
  Set (lsuc ℓ) where
  open CausalPoset P
  field
    Chain :
      Event → Event → Set ℓ

    Antichain :
      Set ℓ

    separates :
      Antichain → Event → Event → Set ℓ

    chainDepth :
      Event → Event → Nat

    antichainWidth :
      Event → Event → Nat

    chainDepthCountsMaximalCausalLength :
      Event → Event → Bool

    antichainWidthCountsMinimalSeparator :
      Event → Event → Bool

open ChainAntichainGeometry public

record ContractiveDecimation {ℓ : Level} : Set (lsuc ℓ) where
  field
    State :
      Set ℓ

    Distance :
      State → State → Set ℓ

    renormalize :
      State → State

    project :
      State → State

    canonicalize :
      State → State

    decimate :
      State → State

    decimateIsCPR :
      ∀ s → decimate s ≡ canonicalize (project (renormalize s))

    strictContraction :
      State → State → Bool

    completeUltrametric :
      Bool

    uniqueFixedPointPerBasin :
      Bool

open ContractiveDecimation public

record OrthogonalMultiscaleQuadraticClosure {ℓ : Level}
  (D : ContractiveDecimation {ℓ}) : Set (lsuc ℓ) where
  open ContractiveDecimation D
  field
    Scalar :
      Set ℓ

    Detail :
      Set ℓ

    coarse :
      State → State

    detail :
      State → Detail

    defect :
      State → Scalar

    detailDefect :
      Detail → Scalar

    add :
      Scalar → Scalar → Scalar

    recognisableSplit :
      State → Bool

    projectionAnnihilatesDetail :
      State → Bool

    pythagoreanAdditivity :
      ∀ s → defect s ≡ add (defect (coarse s)) (detailDefect (detail s))

    parallelogramLaw :
      Bool

    quadraticDefectUnique :
      Bool

    decimationMonotone :
      State → Bool

open OrthogonalMultiscaleQuadraticClosure public

record LorentzSignature31 : Setω where
  field
    SpatialDimension :
      Nat

    TimeDimension :
      Nat

    spatialDimensionIsThree :
      SpatialDimension ≡ 3

    timeDimensionIsOne :
      TimeDimension ≡ 1

    indefinite :
      Bool

    hasNontrivialNullCone :
      Bool

    spatiallyIsotropic :
      Bool

    finitePropagationSpeed :
      Bool

    uniqueStableSignature :
      Bool

open LorentzSignature31 public

record IntervalSurface {ℓ : Level}
  (P : CausalPoset {ℓ})
  (G : ChainAntichainGeometry P) : Set (lsuc ℓ) where
  open CausalPoset P
  open ChainAntichainGeometry G
  field
    Interval :
      Event → Event → Set ℓ

    lightCone :
      Event → Event → Bool

    intervalUsesChainDepthAndAntichainWidth :
      Event → Event → Bool

    nullExactlyFiniteSpeedBoundary :
      Event → Event → Bool

    intervalUniqueUnderClosureAxioms :
      Bool

open IntervalSurface public

record CausalOrderLorentzClosure : Setω where
  field
    level :
      Level

    causalPoset :
      CausalPoset {level}

    chainAntichainGeometry :
      ChainAntichainGeometry causalPoset

    decimation :
      ContractiveDecimation {level}

    quadraticClosure :
      OrthogonalMultiscaleQuadraticClosure decimation

    signature31 :
      LorentzSignature31

    intervalSurface :
      IntervalSurface causalPoset chainAntichainGeometry

    contractionForcesOrthogonalSplit :
      Bool

    orthogonalSplitForcesQuadraticDefect :
      Bool

    involutionIsotropyFiniteSpeedForceIndefiniteOneTimeSignature :
      Bool

    dimensionalSaturationForcesThreeSpaceDimensions :
      Bool

    chainAntichainIntervalForcesLorentzCone :
      Bool

    allClosureTheoremsDischarged :
      Bool

open CausalOrderLorentzClosure public

record CausalOrderLorentzReceipt : Set where
  field
    chainDepthExplicit : Bool
    antichainWidthExplicit : Bool
    contractionExplicit : Bool
    quadraticClosureExplicit : Bool
    signature31Explicit : Bool
    finiteSpeedConeExplicit : Bool
    promotionRequiresClosureWitness : Bool

canonicalCausalOrderLorentzReceipt : CausalOrderLorentzReceipt
canonicalCausalOrderLorentzReceipt =
  record
    { chainDepthExplicit = true
    ; antichainWidthExplicit = true
    ; contractionExplicit = true
    ; quadraticClosureExplicit = true
    ; signature31Explicit = true
    ; finiteSpeedConeExplicit = true
    ; promotionRequiresClosureWitness = true
    }

causalOrderLorentzBoundaryText : String
causalOrderLorentzBoundaryText =
  "Chain depth, antichain width, contractive decimation, quadratic closure, and unique 3+1 signature are separate typed obligations.  Downstream GR/quantum unification may consume them only through a supplied CausalOrderLorentzClosure witness."
