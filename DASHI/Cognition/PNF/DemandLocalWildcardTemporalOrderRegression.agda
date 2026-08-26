{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.DemandLocalWildcardTemporalOrderRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.DemandLocalWildcardTemporalOrderExact

------------------------------------------------------------------------
-- Finite non-commutation witness.
--
-- Fine state contains an earlier and later representative of one object.  The
-- demand lies between them.  Restriction-first keeps the earlier witness;
-- global-quotient-first chooses the later witness and restriction then removes
-- it.  The two execution orders therefore disagree.
------------------------------------------------------------------------

data Fine : Set where
  bothOccurrences : Fine

data Restricted : Set where
  earlierOnly : Restricted

data Quotient : Set where
  earlierObject laterObject noObject : Quotient

restrictFineDemo : Fine → Restricted
restrictFineDemo bothOccurrences = earlierOnly

quotientFineDemo : Fine → Quotient
quotientFineDemo bothOccurrences = laterObject

quotientRestrictedDemo : Restricted → Quotient
quotientRestrictedDemo earlierOnly = earlierObject

restrictQuotientDemo : Quotient → Quotient
restrictQuotientDemo earlierObject = earlierObject
restrictQuotientDemo laterObject = noObject
restrictQuotientDemo noObject = noObject

demoSystem : RestrictionQuotientSystem Fine Restricted Quotient
demoSystem = record
  { restrictFine = restrictFineDemo
  ; quotientFine = quotientFineDemo
  ; quotientRestricted = quotientRestrictedDemo
  ; restrictQuotient = restrictQuotientDemo
  }

nonCommutingResult :
  restrictQuotient demoSystem (quotientFine demoSystem bothOccurrences)
    ≡ noObject
nonCommutingResult = refl

restrictionFirstResult :
  quotientRestricted demoSystem (restrictFine demoSystem bothOccurrences)
    ≡ earlierObject
restrictionFirstResult = refl

noObjectIsNotEarlierObject : noObject ≡ earlierObject → ⊥
noObjectIsNotEarlierObject ()

demoDoesNotCommute : RestrictionQuotientCommutation demoSystem → ⊥
demoDoesNotCommute certificate =
  noObjectIsNotEarlierObject (commutes certificate bothOccurrences)

------------------------------------------------------------------------
-- This regression means that temporal-shadow absence is not an optimization
-- assumption.  It is either proved as commutation for the concrete carrier or
-- avoided by construction through demand-local active segments.
------------------------------------------------------------------------

data TemporalShadowCanBeIgnoredPermission : Set where

temporalShadowCannotBeIgnored : TemporalShadowCanBeIgnoredPermission → ⊥
temporalShadowCannotBeIgnored ()
