module DASHI.Analysis.RenormalisedDifferenceLimitExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERIC RENORMALISED-DIFFERENCE LIMIT
--
-- This owner captures a theorem shape needed by Casimir-type problems:
-- two regulated families need not converge separately, while their matched
-- difference may have a controlled limit.  It is deliberately application
-- neutral and imports no physical conclusion from any existing lane.
------------------------------------------------------------------------

record DifferenceFamily : Set₁ where
  field
    Regulator : Set
    Value : Set
    Limit : Set

    left right : Regulator → Value
    difference : Regulator → Value

    subtract : Value → Value → Value
    differenceLaw : (r : Regulator) →
      difference r ≡ subtract (left r) (right r)

    reading : String

open DifferenceFamily public

record DifferenceConvergence (F : DifferenceFamily) : Set₁ where
  field
    CandidateLimit : Limit F
    Converges : Set
    convergenceReceipt : Converges
    convergenceReading : String

open DifferenceConvergence public

------------------------------------------------------------------------
-- BIDI surface.
--
-- Forward: an application producer supplies a concrete DifferenceFamily and a
-- convergence receipt, yielding a reusable renormalised-difference witness.
-- Reverse: a consumer can project the exact obligations it must discharge;
-- the generic theorem never manufactures them.
------------------------------------------------------------------------

record RenormalisedDifferenceReceipt : Set₁ where
  field
    family : DifferenceFamily
    convergence : DifferenceConvergence family

open RenormalisedDifferenceReceipt public

record RenormalisedDifferenceObligations (F : DifferenceFamily) : Set₁ where
  field
    matchedRegulatorSemantics : Set
    sameObjectSubtraction : Set
    differenceConvergence : Set

open RenormalisedDifferenceObligations public

obligationsOf : RenormalisedDifferenceReceipt → Set₁
obligationsOf receipt = RenormalisedDifferenceObligations (family receipt)

------------------------------------------------------------------------
-- Authority boundary: convergence of the difference does not imply separate
-- convergence of either regulated family.
------------------------------------------------------------------------

data SeparateLeftLimitPermission : Set where

data SeparateRightLimitPermission : Set where

renormalisedDifferenceDoesNotSupplyLeftLimit :
  RenormalisedDifferenceReceipt → SeparateLeftLimitPermission → ⊥
renormalisedDifferenceDoesNotSupplyLeftLimit receipt ()

renormalisedDifferenceDoesNotSupplyRightLimit :
  RenormalisedDifferenceReceipt → SeparateRightLimitPermission → ⊥
renormalisedDifferenceDoesNotSupplyRightLimit receipt ()
