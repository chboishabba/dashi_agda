module DASHI.ArithmeticGeometry.DupontDASHIBridge where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit     using (⊤; tt)
open import Relation.Nullary      using (¬_)

open import DASHI.ArithmeticGeometry.ChainAntichainHeight
open import DASHI.ArithmeticGeometry.LocalGlobalObstruction

------------------------------------------------------------------------
-- DuPont-facing arithmetic regime.
------------------------------------------------------------------------

data Genus : Set where
  genus0 genus1 higherGenus : Genus

record PrimeWindow : Set where
  constructor primeWindow
  field
    upperPrime : Nat
    finiteWindow : Bool

record DupontSurface : Set₁ where
  field
    genus       : Genus
    primeWindow : PrimeWindow

    localGlobal : LocalGlobalProblem
    obstruction : CohomologyObstruction localGlobal

open DupontSurface public

------------------------------------------------------------------------
-- DASHI does not identify finite prime windows, Monster-prime coordinates,
-- or bounded search with the arithmetic theorem itself.  Those are lenses.
------------------------------------------------------------------------

record ArithmeticLensStack (D : DupontSurface) : Set₁ where
  field
    profileOfLocalData : EverywhereLocal (localGlobal D) → OrderProfile
    weights            : HeightWeights

    localScan          : EverywhereLocal (localGlobal D) → Bool
    boundedSearch      : Nat → BoundedSearchReceipt (localGlobal D)

    -- Certified layer supplied by 3-descent / Selmer / pairing machinery.
    certifiedDecision  : LocalGlobalDecision (localGlobal D)

open ArithmeticLensStack public

------------------------------------------------------------------------
-- Genus-zero closure requires an explicit Hasse-style bridge.
------------------------------------------------------------------------

record GenusZeroClosure (D : DupontSurface) : Set₁ where
  field
    isGenusZero : genus D ≡ genus0
    hasseBridge : EverywhereLocal (localGlobal D) →
                  GlobalWitness (localGlobal D)

------------------------------------------------------------------------
-- Genus-one closure requires an obstruction classifier, not merely deeper
-- coordinate search.
------------------------------------------------------------------------

record GenusOneClosure (D : DupontSurface) : Set₁ where
  field
    isGenusOne : genus D ≡ genus1

    classify : EverywhereLocal (localGlobal D) → Decision

    found-sound :
      ∀ locals → classify locals ≡ global-found →
      GlobalWitness (localGlobal D)

    obstructed-sound :
      ∀ locals → classify locals ≡ certified-obstructed →
      ¬ GlobalWitness (localGlobal D)

------------------------------------------------------------------------
-- Concrete comparison theorem schema.
--
-- DASHI is a structural superset only after the arithmetic content is
-- supplied as an instance.  The schema prevents the weaker architecture-only
-- claim from being promoted to mathematical containment.
------------------------------------------------------------------------

record DASHISubsumesDupont (D : DupontSurface) : Set₁ where
  field
    lenses : ArithmeticLensStack D

    genus0Closure : genus D ≡ genus0 → GenusZeroClosure D
    genus1Closure : genus D ≡ genus1 → GenusOneClosure D

    no-search-promotion :
      ∀ bound →
      BoundedSearchReceipt.pointFound
        (ArithmeticLensStack.boundedSearch lenses bound) ≡ false →
      ⊤

------------------------------------------------------------------------
-- Experimental evidence surface.
------------------------------------------------------------------------

record ExperimentReceipt : Set where
  field
    genus0LocalGlobalMatched : Bool
    genus1LocalPruningHelped : Bool
    torsorPersistentFailureObserved : Bool
    newInvariantCertifiedSha : Bool
    chainAntichainValidatedAgainstCanonicalHeight : Bool

currentReceipt : ExperimentReceipt
currentReceipt = record
  { genus0LocalGlobalMatched = true
  ; genus1LocalPruningHelped = true
  ; torsorPersistentFailureObserved = true
  ; newInvariantCertifiedSha = false
  ; chainAntichainValidatedAgainstCanonicalHeight = false
  }
