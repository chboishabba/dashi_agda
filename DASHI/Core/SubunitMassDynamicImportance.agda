module DASHI.Core.SubunitMassDynamicImportance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerIndexedRelevanceMeasure as Relevance
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.PluralConsumerProjectionSafety as Plural

------------------------------------------------------------------------
-- Subunit mass does not imply dynamic irrelevance.
--
-- A distinction may carry less than the normalized unit mass of the current
-- consumer model and still be exactly the distinction whose erasure yields a
-- dynamic quotient defect.  The finite witness below uses mass 1 inside a
-- whole of mass 2; the theorem is qualitative, not a universal numerical
-- bound on minority prevalence.
------------------------------------------------------------------------

_+N_ : Nat → Nat → Nat
zero +N n = n
suc m +N n = suc (m +N n)

one : Nat
one = suc zero

two : Nat
two = suc one

data EquityMassConsumer : Set where
  equityMassConsumer : EquityMassConsumer

data EquityRegion : Set where
  wholeEquityRegion majorityRegion minorityRegion : EquityRegion

equityMass : EquityMassConsumer → EquityRegion → Nat
equityMass equityMassConsumer wholeEquityRegion = two
equityMass equityMassConsumer majorityRegion = one
equityMass equityMassConsumer minorityRegion = one

equityMeasure :
  Relevance.ConsumerIndexedRelevanceMeasure
    EquityMassConsumer EquityRegion Nat
equityMeasure =
  Relevance.consumerIndexedRelevanceMeasure
    Relevance.consumerRelevanceMass
    wholeEquityRegion
    zero
    two
    _+N_
    equityMass
    (λ { equityMassConsumer → refl })

oneIsNotTwo : one ≡ two → ⊥
oneIsNotTwo ()

minorityRegionDoesNotCarryWholeMass :
  Relevance.relevanceMass equityMeasure equityMassConsumer minorityRegion
  ≡ Relevance.unitMass equityMeasure →
  ⊥
minorityRegionDoesNotCarryWholeMass = oneIsNotTwo

record SubunitMassDynamicDefect : Set₁ where
  constructor subunitMassDynamicDefect
  field
    subunitRegion : EquityRegion
    subunitMassNotUnit :
      Relevance.relevanceMass equityMeasure equityMassConsumer subunitRegion
      ≡ Relevance.unitMass equityMeasure →
      ⊥
    dynamicDefect :
      Dynamic.TerminalisationDefect
        Plural.demoSystem
        (Plural.demoProject Plural.futureSensitiveConsumer)

open SubunitMassDynamicDefect public

canonicalSubunitMassDynamicDefect : SubunitMassDynamicDefect
canonicalSubunitMassDynamicDefect =
  subunitMassDynamicDefect
    minorityRegion
    minorityRegionDoesNotCarryWholeMass
    Plural.futureSensitiveConsumerHasDefect

subunitMassDoesNotLicenseDynamicErasure :
  Dynamic.DynamicConsumerSafety
    Plural.demoSystem
    (Plural.demoProject Plural.futureSensitiveConsumer) →
  ⊥
subunitMassDoesNotLicenseDynamicErasure safety =
  Dynamic.terminalisationDefectContradictsSafety
    safety
    (dynamicDefect canonicalSubunitMassDynamicDefect)
