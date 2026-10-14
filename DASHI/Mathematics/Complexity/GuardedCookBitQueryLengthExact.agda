module DASHI.Mathematics.Complexity.GuardedCookBitQueryLengthExact where

------------------------------------------------------------------------
-- CANONICAL QUERY CODE EXPLICITLY PAYS UNARY T AND BIT INDEX
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Canonical
import DASHI.Mathematics.Complexity.GuardedCookBitQueryCodeExact as Query

------------------------------------------------------------------------
-- Length arithmetic for the exact appendMany codec.
------------------------------------------------------------------------

appendLength :
  ∀ {A : Set}
    (left right : List A) →
  Canonical.listLength (Local.append left right)
  ≡ Canonical.listLength left + Canonical.listLength right
appendLength [] right = refl
appendLength (x ∷ left) right
  rewrite appendLength left right = refl

appendManyLength :
  (sections : List (List Bool)) →
  Canonical.listLength (Query.appendMany sections)
  ≡ sumSectionLengths sections
  where
    sumSectionLengths : List (List Bool) → Nat
    sumSectionLengths [] = zero
    sumSectionLengths (section ∷ rest) =
      Canonical.listLength section + sumSectionLengths rest
appendManyLength [] = refl
appendManyLength (section ∷ rest)
  rewrite appendLength section (Query.appendMany rest)
        | appendManyLength rest =
  refl

unaryNatLength :
  (n : Nat) →
  Canonical.listLength (Query.unaryNat n) ≡ suc n
unaryNatLength zero = refl
unaryNatLength (suc n)
  rewrite unaryNatLength n = refl

------------------------------------------------------------------------
-- Any explicitly listed section contributes its full length to appendMany.
------------------------------------------------------------------------

data SectionMember (section : List Bool) : List (List Bool) → Set where
  sectionHere :
    ∀ {rest} →
    SectionMember section (section ∷ rest)

  sectionThere :
    ∀ {head rest} →
    SectionMember section rest →
    SectionMember section (head ∷ rest)

sectionLengthBelowAppendMany :
  ∀ {section sections} →
  SectionMember section sections →
  Canonical.listLength section
  ≤ Canonical.listLength (Query.appendMany sections)
sectionLengthBelowAppendMany {section} {section ∷ rest} sectionHere
  rewrite appendLength section (Query.appendMany rest) =
  NatP.m≤m+n
    (Canonical.listLength section)
    (Canonical.listLength (Query.appendMany rest))
sectionLengthBelowAppendMany
    {section} {head ∷ rest} (sectionThere member)
  rewrite appendLength head (Query.appendMany rest) =
  NatP.≤-trans
    (sectionLengthBelowAppendMany member)
    (NatP.m≤n+m
      (Canonical.listLength (Query.appendMany rest))
      (Canonical.listLength head))

------------------------------------------------------------------------
-- Concrete membership witnesses for the final two query-code sections.
------------------------------------------------------------------------

stepsSectionMember :
  (query : Query.GuardedCookBitQuery) →
  SectionMember
    (Query.unaryNat (Query.steps query))
    ( Query.unaryNat
        (DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact.stateCount
          (Query.code query))
    ∷ Query.unaryNat
        (DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact.symbolCount
          (Query.code query))
    ∷ Query.unaryNat
        (Canonical.listLength
          (DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact.rules
            (Query.code query)))
    ∷ Query.queryProgramBits query
    ∷ Query.unaryNat (Canonical.listLength (Query.input query))
    ∷ Query.encodeInputSymbols (Query.code query) (Query.input query)
    ∷ Query.unaryNat (Query.steps query)
    ∷ Query.unaryNat (Query.index query)
    ∷ [] )
stepsSectionMember query =
  sectionThere
    (sectionThere
      (sectionThere
        (sectionThere
          (sectionThere
            (sectionThere sectionHere)))))

indexSectionMember :
  (query : Query.GuardedCookBitQuery) →
  SectionMember
    (Query.unaryNat (Query.index query))
    ( Query.unaryNat
        (DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact.stateCount
          (Query.code query))
    ∷ Query.unaryNat
        (DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact.symbolCount
          (Query.code query))
    ∷ Query.unaryNat
        (Canonical.listLength
          (DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact.rules
            (Query.code query)))
    ∷ Query.queryProgramBits query
    ∷ Query.unaryNat (Canonical.listLength (Query.input query))
    ∷ Query.encodeInputSymbols (Query.code query) (Query.input query)
    ∷ Query.unaryNat (Query.steps query)
    ∷ Query.unaryNat (Query.index query)
    ∷ [] )
indexSectionMember query =
  sectionThere
    (sectionThere
      (sectionThere
        (sectionThere
          (sectionThere
            (sectionThere
              (sectionThere sectionHere))))))

stepsBelowQueryBitLength :
  (query : Query.GuardedCookBitQuery) →
  Query.steps query ≤ Query.queryBitLength query
stepsBelowQueryBitLength query =
  NatP.≤-trans
    (NatP.n≤1+n (Query.steps query))
    (substLength
      (unaryNatLength (Query.steps query))
      (sectionLengthBelowAppendMany (stepsSectionMember query)))
  where
    substLength :
      ∀ {a b c : Nat} →
      a ≡ b →
      b ≤ c →
      a ≤ c
    substLength refl proof = proof

indexBelowQueryBitLength :
  (query : Query.GuardedCookBitQuery) →
  Query.index query ≤ Query.queryBitLength query
indexBelowQueryBitLength query =
  NatP.≤-trans
    (NatP.n≤1+n (Query.index query))
    (substLength
      (unaryNatLength (Query.index query))
      (sectionLengthBelowAppendMany (indexSectionMember query)))
  where
    substLength :
      ∀ {a b c : Nat} →
      a ≡ b →
      b ≤ c →
      a ≤ c
    substLength refl proof = proof

------------------------------------------------------------------------
-- These are deliberately lower bounds only.  They certify that charging work
-- polynomially in unary T/index is also polynomially chargeable to the actual
-- canonical query input size; no hidden numeric oracle is introduced.
------------------------------------------------------------------------
