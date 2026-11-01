module Ontology.DNA.OperationalChemistryQuotient where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Ontology.DNA.Supervoxel4Adic using (FlatDNA256)
open import Ontology.DNA.ChemistryConcrete using
  (countStrong; countComplementSpan2; countRCPal4; countHairpin6;
   thermoKernelConcrete; admissibleConcrete)
import Ontology.Hecke.QuotientRepresentation as HQ

------------------------------------------------------------------------
-- The lossless U/V coordinates are an exact chart, not a non-trivial
-- chemistry quotient.  This module defines the quotient on coarse operational
-- observables instead.

record OperationalChemistryFeature : Set where
  constructor operationalFeature
  field
    gcLoad : Nat
    complementSpanRisk : Nat
    reverseComplementRisk : Nat
    shortHairpinRisk : Nat
    aggregateThermoRisk : Nat
    admissibilityFlag : Bool

operationalFeatureMap : FlatDNA256 → OperationalChemistryFeature
operationalFeatureMap xs = operationalFeature
  (countStrong xs)
  (countComplementSpan2 xs)
  (countRCPal4 xs)
  (countHairpin6 xs)
  (thermoKernelConcrete xs)
  (admissibleConcrete xs)

_≈operational_ : FlatDNA256 → FlatDNA256 → Set
x ≈operational y = operationalFeatureMap x ≡ operationalFeatureMap y

operationalEquivalence : HQ.EquivalenceOn FlatDNA256
operationalEquivalence = record
  { _≈_ = _≈operational_
  ; refl = λ x → refl
  ; sym = sym
  ; trans = trans
  }

record TolerancePolicy : Set₁ where
  field
    close : OperationalChemistryFeature → OperationalChemistryFeature → Bool
    close-refl : ∀ f → close f f ≡ true

record AssayRelativeQuotient : Set₁ where
  field
    policy : TolerancePolicy
    sameBasin : FlatDNA256 → FlatDNA256 → Bool
    sameBasin-def : ∀ x y →
      sameBasin x y ≡ TolerancePolicy.close policy
        (operationalFeatureMap x) (operationalFeatureMap y)

-- Equality of operational features is already strictly coarser in intent than
-- equality of the lossless U/V chart.  A concrete distinct-sequence witness is
-- deliberately separated as an empirical/search certificate.
record NonTrivialOperationalWitness : Set where
  field
    left right : FlatDNA256
    distinctRaw : Bool
    sameOperationalFeature : operationalFeatureMap left ≡ operationalFeatureMap right
