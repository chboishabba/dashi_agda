module DASHI.Mathematics.Complexity.ConcreteTapeAcceptancePredicateCodeExact where

------------------------------------------------------------------------
-- FINITE CODE FOR ACCEPTANCE IMPLICATION PREDICATES
--
-- As with transition predicates, the local Boolean kernel is fixed for the
-- machine.  The dynamic acceptance list varies only by the final-row cell.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.ConcreteTapeGlobalTracePlacementExact as Global
import DASHI.Mathematics.Complexity.ConcreteTapeEndpointCNFExact as Endpoint
import DASHI.Mathematics.Complexity.CNFPlacedConstraintConjunctionExact as Placed

record AcceptancePredicateCode (cols : Nat) : Set where
  constructor acceptance-predicate-code
  field
    cellIndex : Fin.Fin cols

open AcceptancePredicateCode public

interpretAcceptancePredicateCode :
  ∀ {machine steps cols}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  AcceptancePredicateCode cols →
  Placed.PlacedPredicate
    (Endpoint.AcceptanceLocalWidth machine)
    (Endpoint.ExtendedGlobalWidth machine steps cols)
interpretAcceptancePredicateCode
    stateCoverage symbolCoverage (acceptance-predicate-code i) =
  Endpoint.acceptancePlacedPredicate
    stateCoverage symbolCoverage (Endpoint.finToSlot i)

acceptanceCodes :
  ∀ {cols} →
  List (Fin.Fin cols) →
  List (AcceptancePredicateCode cols)
acceptanceCodes [] = []
acceptanceCodes (i ∷ rest) =
  acceptance-predicate-code i ∷ acceptanceCodes rest

allAcceptanceCodes :
  (cols : Nat) →
  List (AcceptancePredicateCode cols)
allAcceptanceCodes cols =
  acceptanceCodes (Endpoint.finList cols)

interpretAcceptanceCodes :
  ∀ {machine steps cols}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  List (AcceptancePredicateCode cols) →
  List
    (Placed.PlacedPredicate
      (Endpoint.AcceptanceLocalWidth machine)
      (Endpoint.ExtendedGlobalWidth machine steps cols))
interpretAcceptanceCodes stateCoverage symbolCoverage [] = []
interpretAcceptanceCodes stateCoverage symbolCoverage (code ∷ rest) =
  interpretAcceptancePredicateCode stateCoverage symbolCoverage code
  ∷ interpretAcceptanceCodes stateCoverage symbolCoverage rest

acceptanceCodesExact :
  ∀ {machine steps cols}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine))
    (indices : List (Fin.Fin cols)) →
  interpretAcceptanceCodes stateCoverage symbolCoverage
    (acceptanceCodes indices)
  ≡
  Endpoint.acceptanceImplicationPredicatesFin
    stateCoverage symbolCoverage indices
acceptanceCodesExact stateCoverage symbolCoverage [] = refl
acceptanceCodesExact stateCoverage symbolCoverage (i ∷ rest)
  rewrite acceptanceCodesExact stateCoverage symbolCoverage rest = refl

allAcceptanceCodesExact :
  ∀ {machine steps cols}
    (stateCoverage : Canonical.EnumerationCoverage (Local.finiteState machine))
    (symbolCoverage : Canonical.EnumerationCoverage (Local.finiteSymbol machine)) →
  interpretAcceptanceCodes stateCoverage symbolCoverage
    (allAcceptanceCodes cols)
  ≡
  Endpoint.acceptanceImplicationPredicatesFin
    stateCoverage symbolCoverage
    (Endpoint.finList cols)
allAcceptanceCodesExact stateCoverage symbolCoverage =
  acceptanceCodesExact
    stateCoverage symbolCoverage
    (Endpoint.finList _)

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The accepting endpoint stream is first-order too: dynamic data are only a
-- finite column index.  Its remaining Boolean kernel is the single fixed
-- `witnessAcceptingPredicate` for the fixed coded target.
------------------------------------------------------------------------
