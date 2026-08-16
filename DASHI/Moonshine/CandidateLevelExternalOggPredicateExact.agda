module DASHI.Moonshine.CandidateLevelExternalOggPredicateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / AUTHORITY
--
-- Andrew P. Ogg,
-- "Automorphismes de courbes modulaires", Seminaire Delange-Pisot-Poitou,
-- 1974/75, exp. 7.  No DOI asserted.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem", Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- DASHI CONTRIBUTION
--
-- Put the already-separated external Ogg classification on the unbiased
-- CandidateLevel domain.  This predicate is for *post hoc comparison only*.
-- It is not available to the representation restriction functions that
-- generate branching/fixed-space data.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.CandidateLevelRepresentationHeckeSquareExact as Candidate
import DASHI.Physics.Moonshine.SupersingularPrimeLaneBridge as Ogg

ExternalOggAt : Nat → Set
ExternalOggAt level =
  Σ Ogg.SupersingularPrime
    (λ prime → Ogg.supersingularPrimeToNat prime ≡ level)

externalOggPredicate : Candidate.ExternalExceptionalPredicate
externalOggPredicate =
  record
    { Candidate.exceptional = ExternalOggAt
    ; Candidate.predicateReceipt =
        "External Ogg classification only; not consumed while deriving representation reduction data."
    }

spinor2IsExternallyOgg : ExternalOggAt 2
spinor2IsExternallyOgg = Ogg.p2 , refl

dimension7IsExternallyOgg : ExternalOggAt 7
dimension7IsExternallyOgg = Ogg.p7 , refl

dimension29IsExternallyOgg : ExternalOggAt 29
dimension29IsExternallyOgg = Ogg.p29 , refl

dimension71IsExternallyOgg : ExternalOggAt 71
dimension71IsExternallyOgg = Ogg.p71 , refl

dimension9IsNotExternallyOgg : ExternalOggAt 9 → ⊥
dimension9IsNotExternallyOgg (Ogg.p2 , ())
dimension9IsNotExternallyOgg (Ogg.p3 , ())
dimension9IsNotExternallyOgg (Ogg.p5 , ())
dimension9IsNotExternallyOgg (Ogg.p7 , ())
dimension9IsNotExternallyOgg (Ogg.p11 , ())
dimension9IsNotExternallyOgg (Ogg.p13 , ())
dimension9IsNotExternallyOgg (Ogg.p17 , ())
dimension9IsNotExternallyOgg (Ogg.p19 , ())
dimension9IsNotExternallyOgg (Ogg.p23 , ())
dimension9IsNotExternallyOgg (Ogg.p29 , ())
dimension9IsNotExternallyOgg (Ogg.p31 , ())
dimension9IsNotExternallyOgg (Ogg.p41 , ())
dimension9IsNotExternallyOgg (Ogg.p47 , ())
dimension9IsNotExternallyOgg (Ogg.p59 , ())
dimension9IsNotExternallyOgg (Ogg.p71 , ())

dimension15IsNotExternallyOgg : ExternalOggAt 15 → ⊥
dimension15IsNotExternallyOgg (Ogg.p2 , ())
dimension15IsNotExternallyOgg (Ogg.p3 , ())
dimension15IsNotExternallyOgg (Ogg.p5 , ())
dimension15IsNotExternallyOgg (Ogg.p7 , ())
dimension15IsNotExternallyOgg (Ogg.p11 , ())
dimension15IsNotExternallyOgg (Ogg.p13 , ())
dimension15IsNotExternallyOgg (Ogg.p17 , ())
dimension15IsNotExternallyOgg (Ogg.p19 , ())
dimension15IsNotExternallyOgg (Ogg.p23 , ())
dimension15IsNotExternallyOgg (Ogg.p29 , ())
dimension15IsNotExternallyOgg (Ogg.p31 , ())
dimension15IsNotExternallyOgg (Ogg.p41 , ())
dimension15IsNotExternallyOgg (Ogg.p47 , ())
dimension15IsNotExternallyOgg (Ogg.p59 , ())
dimension15IsNotExternallyOgg (Ogg.p71 , ())

record ExternalOggPredicateBoundary : Set where
  field
    externalPredicateConstructedOnUnfilteredDomain : Bool
    externalPredicateConstructedOnUnfilteredDomainIsTrue :
      externalPredicateConstructedOnUnfilteredDomain ≡ true

    representationReductionReadsExternalOggPredicate : Bool
    representationReductionReadsExternalOggPredicateIsFalse :
      representationReductionReadsExternalOggPredicate ≡ false

    OggTheoremReprovedInternallyHere : Bool
    OggTheoremReprovedInternallyHereIsFalse :
      OggTheoremReprovedInternallyHere ≡ false

canonicalExternalOggPredicateBoundary : ExternalOggPredicateBoundary
canonicalExternalOggPredicateBoundary =
  record
    { externalPredicateConstructedOnUnfilteredDomain = true
    ; externalPredicateConstructedOnUnfilteredDomainIsTrue = refl
    ; representationReductionReadsExternalOggPredicate = false
    ; representationReductionReadsExternalOggPredicateIsFalse = refl
    ; OggTheoremReprovedInternallyHere = false
    ; OggTheoremReprovedInternallyHereIsFalse = refl
    }
