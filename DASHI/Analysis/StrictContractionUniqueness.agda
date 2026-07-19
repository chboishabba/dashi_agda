module DASHI.Analysis.StrictContractionUniqueness where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.YangMills.BalabanFiniteOneStepCore as BFO

------------------------------------------------------------------------
-- Generic uniqueness theorem for the existing finite contraction certificate.
--
-- The State carrier may itself be a certified local region or subtype.  Hence
-- the result should be read as uniqueness on the declared carrier, not global
-- uniqueness in an ambient physical state space.
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
  ⊥-elim
    (irreflexive laws
      (BFO.FiniteContractionCertificate.distance C
        candidate
        (BFO.FiniteContractionCertificate.fixedPoint C))
      strictSelf)
  where
  strictSelf :
    BFO.FiniteContractionCertificate.StrictlySmaller C
      (BFO.FiniteContractionCertificate.distance C
        candidate
        (BFO.FiniteContractionCertificate.fixedPoint C))
      (BFO.FiniteContractionCertificate.distance C
        candidate
        (BFO.FiniteContractionCertificate.fixedPoint C))
  strictSelf
    rewrite candidateFixed
          | BFO.FiniteContractionCertificate.fixed C =
    BFO.FiniteContractionCertificate.contractive C
      candidate
      (BFO.FiniteContractionCertificate.fixedPoint C)

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
