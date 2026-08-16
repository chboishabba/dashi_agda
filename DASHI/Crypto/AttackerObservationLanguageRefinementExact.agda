module DASHI.Crypto.AttackerObservationLanguageRefinementExact where

------------------------------------------------------------------------
-- ATTACKER OBSERVATION-LANGUAGE REFINEMENT
--
-- Crypto specialization of the future-equivalence idea: a threat model induces
-- an observational equivalence on hidden states.  Enlarging the attacker's
-- observation language can only refine that equivalence.  A newly admitted
-- side channel matters exactly when it separates two states previously equal
-- under the base attacker language.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

record ObservationLanguage : Set₁ where
  constructor observationLanguage
  field
    Hidden Base Extra : Set
    baseObservation : Hidden → Base
    extraObservation : Hidden → Extra

open ObservationLanguage public

BaseEquivalent : (language : ObservationLanguage) → Hidden language → Hidden language → Set
BaseEquivalent language x y =
  baseObservation language x ≡ baseObservation language y

ExtendedEquivalent : (language : ObservationLanguage) → Hidden language → Hidden language → Set
ExtendedEquivalent language x y =
  BaseEquivalent language x y ×
  extraObservation language x ≡ extraObservation language y

extendedRefinesBase :
  ∀ {language : ObservationLanguage} {x y} →
  ExtendedEquivalent language x y → BaseEquivalent language x y
extendedRefinesBase extended = Data.Product.proj₁ extended

record LanguageSplitWitness (language : ObservationLanguage) : Set where
  constructor languageSplitWitness
  field
    left right : Hidden language
    baseSame : BaseEquivalent language left right
    extraDifferent :
      extraObservation language left ≡ extraObservation language right → ⊥

open LanguageSplitWitness public

splitRefutesExtendedEquivalence :
  ∀ {language : ObservationLanguage}
    (split : LanguageSplitWitness language) →
  ExtendedEquivalent language (left split) (right split) → ⊥
splitRefutesExtendedEquivalence split extended =
  extraDifferent split (Data.Product.proj₂ extended)

------------------------------------------------------------------------
-- Finite defensive regression: the public observation is constant, while an
-- implementation side observation distinguishes the hidden route.  The extra
-- coordinate therefore refines the base attacker quotient.
------------------------------------------------------------------------

data Hidden2 : Set where h0 h1 : Hidden2

data PublicOne : Set where public : PublicOne

data SideBit : Set where side0 side1 : SideBit

publicObs : Hidden2 → PublicOne
publicObs h0 = public
publicObs h1 = public

sideObs : Hidden2 → SideBit
sideObs h0 = side0
sideObs h1 = side1

finiteLanguage : ObservationLanguage
finiteLanguage = observationLanguage Hidden2 PublicOne SideBit publicObs sideObs

baseCannotSeparate : BaseEquivalent finiteLanguage h0 h1
baseCannotSeparate = refl

sideSeparates : sideObs h0 ≡ sideObs h1 → ⊥
sideSeparates ()

finiteLanguageSplit : LanguageSplitWitness finiteLanguage
finiteLanguageSplit = languageSplitWitness h0 h1 refl sideSeparates

extendedLanguageSeparates : ExtendedEquivalent finiteLanguage h0 h1 → ⊥
extendedLanguageSeparates = splitRefutesExtendedEquivalence finiteLanguageSplit

------------------------------------------------------------------------
-- Boundary: adding an observation coordinate is not itself evidence that a
-- real implementation leaks; the same-public split witness must be constructed
-- from the concrete implementation/protocol surface.
------------------------------------------------------------------------
