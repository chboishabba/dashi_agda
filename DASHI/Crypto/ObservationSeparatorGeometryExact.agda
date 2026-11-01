module DASHI.Crypto.ObservationSeparatorGeometryExact where

------------------------------------------------------------------------
-- OBSERVATIONS CAN CHANGE RECONCILIATION GEOMETRY MORE THAN CARDINALITY
--
-- Candidate-count reduction is only one source of algorithmic value.  An
-- observation may also collapse separator state, conditional branching, or
-- reconciliation work.  This finite theorem composes the existing separator-DP
-- accounting with an observation update and makes that distinction exact.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_)

import DASHI.Crypto.ConstraintCouplingSearchExact as Coupling

record SeparatorObservationComparison : Set where
  constructor separatorObservationComparison
  field
    candidateCountBefore candidateCountAfter : Nat
    beforeSeparator afterSeparator : Coupling.BoundedSeparatorSearchCertificate
    observationCost : Nat

open SeparatorObservationComparison public

beforeSeparatorWork : SeparatorObservationComparison → Nat
beforeSeparatorWork comparison =
  Coupling.separatorDPBound (beforeSeparator comparison)

afterSeparatorWork : SeparatorObservationComparison → Nat
afterSeparatorWork comparison =
  observationCost comparison +
  Coupling.separatorDPBound (afterSeparator comparison)

record SeparatorGeometryGain
    (comparison : SeparatorObservationComparison) : Set where
  constructor separatorGeometryGain
  field
    gain : Nat
    exactGain : beforeSeparatorWork comparison ≡ afterSeparatorWork comparison + gain

open SeparatorGeometryGain public

------------------------------------------------------------------------
-- Small cardinality change, large geometry change.
--
-- Before: 6 candidates, 8 separator states, work/state = 4+4+2 = 10 => 80.
-- After:  5 candidates, 1 separator state, work/state = 4+4+1 = 9, plus
-- observation cost 3 => 12.  Net gain 68 despite removing only one candidate.
------------------------------------------------------------------------

beforeCertificate : Coupling.BoundedSeparatorSearchCertificate
beforeCertificate = Coupling.boundedSeparatorSearchCertificate 8 4 4 2

afterCertificate : Coupling.BoundedSeparatorSearchCertificate
afterCertificate = Coupling.boundedSeparatorSearchCertificate 1 4 4 1

separatorObservation : SeparatorObservationComparison
separatorObservation =
  separatorObservationComparison 6 5 beforeCertificate afterCertificate 3

beforeWorkIs80 : beforeSeparatorWork separatorObservation ≡ 80
beforeWorkIs80 = refl

afterWorkIs12 : afterSeparatorWork separatorObservation ≡ 12
afterWorkIs12 = refl

separatorObservationGain : SeparatorGeometryGain separatorObservation
separatorObservationGain = separatorGeometryGain 68 refl

oneCandidateRemoved :
  candidateCountBefore separatorObservation ≡ 6
  × candidateCountAfter separatorObservation ≡ 5
oneCandidateRemoved = refl , refl

------------------------------------------------------------------------
-- Boundary: this is an exact work-accounting regression, not a claim that a
-- concrete ML-KEM observation creates such a separator collapse.  A real attack
-- or defence must supply the same-object graph/separator witness.
------------------------------------------------------------------------
