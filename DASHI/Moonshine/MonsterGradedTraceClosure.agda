module DASHI.Moonshine.MonsterGradedTraceClosure where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin using (Fin)

import DASHI.Moonshine.GradedRepresentation as GR

------------------------------------------------------------------------
-- Exact table certificate, derived from representations and traces rather
-- than an untyped 194-by-194 socket.  The algebraic predicates are explicit
-- parameters of the certificate, and must be instantiated over an exact
-- cyclotomic carrier.

record ExactMonsterCharacterTableCertificate
  (Monster CyclotomicInteger : Set)
  (RowOrthogonal ColumnOrthogonal :
    (Fin 194 → Fin 194 → CyclotomicInteger) → Set)
  : Setω where
  field
    monsterGroup : GR.Group Monster
    classRepresentative : Fin 194 → Monster
    representation : Fin 194 → GR.FiniteDimensionalRepresentation Monster CyclotomicInteger monsterGroup
    table : Fin 194 → Fin 194 → CyclotomicInteger
    tableIsTrace : ∀ (χ c : Fin 194) →
      table χ c ≡ GR.trace (representation χ) (GR.action (representation χ) (classRepresentative c))
    rowOrthogonality : RowOrthogonal table
    columnOrthogonality : ColumnOrthogonal table
    degreeIsIdentityTrace : ∀ (χ : Fin 194) → Set
    irreducible : ∀ (χ : Fin 194) → Set
    pairwiseInequivalent : ∀ (χ ψ : Fin 194) → Set
    completeIrrepCoverage : Set
    sourceDigest : Set
    indexingConvention : Set

record MonsterGradedTraceClosure
  (Monster CyclotomicInteger McKayThompsonSeries : Set)
  (RowOrthogonal ColumnOrthogonal :
    (Fin 194 → Fin 194 → CyclotomicInteger) → Set)
  : Setω where
  field
    monsterGroup : GR.Group Monster
    gradedRepresentation : GR.GradedRepresentation Monster CyclotomicInteger monsterGroup
    tableCertificate :
      ExactMonsterCharacterTableCertificate Monster CyclotomicInteger
        RowOrthogonal ColumnOrthogonal
    certifiedSeries : McKayThompsonSeries
    coefficientTraceLaw : Set

open MonsterGradedTraceClosure public
