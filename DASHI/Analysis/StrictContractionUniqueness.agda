module DASHI.Analysis.StrictContractionUniqueness where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.YangMills.BalabanFiniteOneStepCore as BFO

------------------------------------------------------------------------
-- Generic uniqueness theorems for finite strict-contraction certificates.
--
-- IMPORTANT REPAIR (2026-09-07):
--
-- The historical `BFO.FiniteContractionCertificate` requires strict
-- contraction for *all* pairs.  Because it also contains a fixed point, that
-- requirement includes the pair (fixedPoint,fixedPoint).  Hence no such
-- certificate can coexist with an irreflexive strict-distance relation.
--
-- We retain the historical theorem surface for compatibility and prove the
-- no-go explicitly.  The corrected least-privilege carrier below requires
-- strict contraction only for distinct pairs and carries a state equality
-- decision so fixed-point uniqueness is constructive.
------------------------------------------------------------------------

record IrreflexiveStrictDistance
    {d : Level}
    (Distance : Set d)
    (StrictlySmaller : Distance → Distance → Set d)
    : Set (lsuc d) where
  field
    irreflexive :
      (value : Distance) →
      StrictlySmaller value value →
      ⊥

open IrreflexiveStrictDistance public

------------------------------------------------------------------------
-- Historical surface and its exact vacuity firewall.
------------------------------------------------------------------------

irreflexiveFiniteContractionImpossible :
  ∀ {x d}
    {State : Set x}
    {Distance : Set d}
    (C : BFO.FiniteContractionCertificate State Distance) →
  IrreflexiveStrictDistance Distance
    (BFO.FiniteContractionCertificate.StrictlySmaller C) →
  ⊥
irreflexiveFiniteContractionImpossible C laws =
  irreflexive laws
    (BFO.FiniteContractionCertificate.distance C
      (BFO.FiniteContractionCertificate.fixedPoint C)
      (BFO.FiniteContractionCertificate.fixedPoint C))
    (BFO.FiniteContractionCertificate.contractive C
      (BFO.FiniteContractionCertificate.fixedPoint C)
      (BFO.FiniteContractionCertificate.fixedPoint C))

strictContractionFixedPointUnique :
  ∀ {x d}
    {State : Set x}
    {Distance : Set d}
    (C : BFO.FiniteContractionCertificate State Distance) →
  IrreflexiveStrictDistance Distance
    (BFO.FiniteContractionCertificate.StrictlySmaller C) →
  (candidate : State) →
  BFO.FiniteContractionCertificate.step C candidate ≡ candidate →
  candidate ≡ BFO.FiniteContractionCertificate.fixedPoint C
strictContractionFixedPointUnique C laws candidate candidateFixed =
  ⊥-elim (irreflexiveFiniteContractionImpossible C laws)

record UniqueFixedPointCertificate
    {x d : Level}
    {State : Set x}
    {Distance : Set d}
    (C : BFO.FiniteContractionCertificate State Distance)
    : Set (lsuc (x ⊔ d)) where
  field
    strictDistance :
      IrreflexiveStrictDistance Distance
        (BFO.FiniteContractionCertificate.StrictlySmaller C)

    unique :
      (candidate : State) →
      BFO.FiniteContractionCertificate.step C candidate ≡ candidate →
      candidate ≡ BFO.FiniteContractionCertificate.fixedPoint C

open UniqueFixedPointCertificate public

certifyUniqueFixedPoint :
  ∀ {x d}
    {State : Set x}
    {Distance : Set d}
    (C : BFO.FiniteContractionCertificate State Distance) →
  IrreflexiveStrictDistance Distance
    (BFO.FiniteContractionCertificate.StrictlySmaller C) →
  UniqueFixedPointCertificate C
certifyUniqueFixedPoint C laws = record
  { strictDistance = laws
  ; unique = strictContractionFixedPointUnique C laws
  }

------------------------------------------------------------------------
-- Corrected least-privilege surface: strict contraction only for distinct
-- state pairs.  This is compatible with a genuine fixed point and an
-- irreflexive strict-distance relation.
------------------------------------------------------------------------

Distinct : ∀ {x} {State : Set x} → State → State → Set x
Distinct left right = left ≡ right → ⊥

record SeparatedFiniteContractionCertificate
    {x d : Level}
    (State : Set x)
    (Distance : Set d)
    : Set (lsuc (x ⊔ d)) where
  field
    step : State → State
    distance : State → State → Distance
    StrictlySmaller : Distance → Distance → Set d
    fixedPoint : State
    fixed : step fixedPoint ≡ fixedPoint

    decideEquality :
      (left right : State) →
      (left ≡ right) ⊎ Distinct left right

    contractiveDistinct :
      (left right : State) →
      Distinct left right →
      StrictlySmaller
        (distance (step left) (step right))
        (distance left right)

open SeparatedFiniteContractionCertificate public

separatedStrictContractionFixedPointUnique :
  ∀ {x d}
    {State : Set x}
    {Distance : Set d}
    (C : SeparatedFiniteContractionCertificate State Distance) →
  IrreflexiveStrictDistance Distance
    (SeparatedFiniteContractionCertificate.StrictlySmaller C) →
  (candidate : State) →
  SeparatedFiniteContractionCertificate.step C candidate ≡ candidate →
  candidate ≡ SeparatedFiniteContractionCertificate.fixedPoint C
separatedStrictContractionFixedPointUnique C laws candidate candidateFixed
  with SeparatedFiniteContractionCertificate.decideEquality C
    candidate
    (SeparatedFiniteContractionCertificate.fixedPoint C)
... | inj₁ same = same
... | inj₂ different =
  ⊥-elim
    (irreflexive laws
      (SeparatedFiniteContractionCertificate.distance C
        candidate
        (SeparatedFiniteContractionCertificate.fixedPoint C))
      strictSelf)
  where
  strictSelf :
    SeparatedFiniteContractionCertificate.StrictlySmaller C
      (SeparatedFiniteContractionCertificate.distance C
        candidate
        (SeparatedFiniteContractionCertificate.fixedPoint C))
      (SeparatedFiniteContractionCertificate.distance C
        candidate
        (SeparatedFiniteContractionCertificate.fixedPoint C))
  strictSelf
    rewrite candidateFixed
          | SeparatedFiniteContractionCertificate.fixed C =
    SeparatedFiniteContractionCertificate.contractiveDistinct C
      candidate
      (SeparatedFiniteContractionCertificate.fixedPoint C)
      different

record SeparatedUniqueFixedPointCertificate
    {x d : Level}
    {State : Set x}
    {Distance : Set d}
    (C : SeparatedFiniteContractionCertificate State Distance)
    : Set (lsuc (x ⊔ d)) where
  field
    strictDistance :
      IrreflexiveStrictDistance Distance
        (SeparatedFiniteContractionCertificate.StrictlySmaller C)

    unique :
      (candidate : State) →
      SeparatedFiniteContractionCertificate.step C candidate ≡ candidate →
      candidate ≡ SeparatedFiniteContractionCertificate.fixedPoint C

open SeparatedUniqueFixedPointCertificate public

certifySeparatedUniqueFixedPoint :
  ∀ {x d}
    {State : Set x}
    {Distance : Set d}
    (C : SeparatedFiniteContractionCertificate State Distance) →
  IrreflexiveStrictDistance Distance
    (SeparatedFiniteContractionCertificate.StrictlySmaller C) →
  SeparatedUniqueFixedPointCertificate C
certifySeparatedUniqueFixedPoint C laws = record
  { strictDistance = laws
  ; unique = separatedStrictContractionFixedPointUnique C laws
  }
