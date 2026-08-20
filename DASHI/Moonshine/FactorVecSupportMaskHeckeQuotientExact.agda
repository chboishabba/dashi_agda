module DASHI.Moonshine.FactorVecSupportMaskHeckeQuotientExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- DASHI CONTRIBUTION
--
-- Give the first concrete end-to-end instance of
-- HeckeCorrespondenceQuotientDescentExact on the repository's existing Hecke
-- carriers.
--
-- Fine carrier:   FactorVec = Vec15 Nat.
-- Quotient:       supportMask : FactorVec -> Vec15 Bool.
-- Fine p-correspondence:
--
--   x |-> { bump_q (bump_p x) : q in the 15 SSP coordinates }.
--
-- Projecting this list by supportMask is exactly the already-existing
-- supportMaskCorrespondence:
--
--   m |-> { mark_q (mark_p m) : q in the 15 SSP coordinates }.
--
-- Therefore the existing support-mask finite Hecke operator is not merely
-- analogous to a quotient operator: it is pointwise the canonical induced
-- correspondence from this FactorVec producer, and every support-mask
-- observable satisfies the exact quotient intertwining law.
--
-- This theorem is deliberately internal to the repository's finite Hecke
-- model.  It does not identify FactorVec with an SO(3), modular-curve, Brandt,
-- or physical SSP carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Ontology.GodelLattice using (Vec15; FactorVec)
open import Ontology.GodelLattice renaming (v15 to mkVec15)
open import MonsterOntos using
  (SSP; p2; p3; p5; p7; p11; p13; p17; p19; p23; p29; p31; p41; p47; p59; p71)

import Ontology.Hecke.CorrespondenceRepresentation as Hecke
import Ontology.Hecke.FactorVecCorrespondence as MaskHecke
import Ontology.Hecke.FactorVecInstances as Factor
import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact as Descent

------------------------------------------------------------------------
-- Fine 15-way correspondence before support-mask quotienting.
------------------------------------------------------------------------

factorVecCorrespondence : SSP → FactorVec → Vec15 FactorVec
factorVecCorrespondence p x =
  mkVec15
    (Factor.bumpPrime p2  (Factor.bumpPrime p x))
    (Factor.bumpPrime p3  (Factor.bumpPrime p x))
    (Factor.bumpPrime p5  (Factor.bumpPrime p x))
    (Factor.bumpPrime p7  (Factor.bumpPrime p x))
    (Factor.bumpPrime p11 (Factor.bumpPrime p x))
    (Factor.bumpPrime p13 (Factor.bumpPrime p x))
    (Factor.bumpPrime p17 (Factor.bumpPrime p x))
    (Factor.bumpPrime p19 (Factor.bumpPrime p x))
    (Factor.bumpPrime p23 (Factor.bumpPrime p x))
    (Factor.bumpPrime p29 (Factor.bumpPrime p x))
    (Factor.bumpPrime p31 (Factor.bumpPrime p x))
    (Factor.bumpPrime p41 (Factor.bumpPrime p x))
    (Factor.bumpPrime p47 (Factor.bumpPrime p x))
    (Factor.bumpPrime p59 (Factor.bumpPrime p x))
    (Factor.bumpPrime p71 (Factor.bumpPrime p x))

factorVecCorrespondenceHecke : Hecke.PrimeCorrespondenceHeckeOn FactorVec
factorVecCorrespondenceHecke =
  record
    { correspondence = factorVecCorrespondence
    }

------------------------------------------------------------------------
-- Two prime bumps become two support marks under the existing quotient.
------------------------------------------------------------------------

supportMaskDoubleBump :
  (outer inner : SSP) →
  (x : FactorVec) →
  Factor.supportMask (Factor.bumpPrime outer (Factor.bumpPrime inner x))
  ≡ Factor.markPrime outer (Factor.markPrime inner (Factor.supportMask x))
supportMaskDoubleBump outer inner x =
  trans
    (Factor.supportMask-bumpPrime outer (Factor.bumpPrime inner x))
    (cong (Factor.markPrime outer) (Factor.supportMask-bumpPrime inner x))

factorVecCorrespondenceProjectsExactly :
  (p : SSP) →
  (x : FactorVec) →
  Hecke.map15 Factor.supportMask (factorVecCorrespondence p x)
  ≡ MaskHecke.supportMaskCorrespondence p (Factor.supportMask x)
factorVecCorrespondenceProjectsExactly p x
  rewrite supportMaskDoubleBump p2  p x
        | supportMaskDoubleBump p3  p x
        | supportMaskDoubleBump p5  p x
        | supportMaskDoubleBump p7  p x
        | supportMaskDoubleBump p11 p x
        | supportMaskDoubleBump p13 p x
        | supportMaskDoubleBump p17 p x
        | supportMaskDoubleBump p19 p x
        | supportMaskDoubleBump p23 p x
        | supportMaskDoubleBump p29 p x
        | supportMaskDoubleBump p31 p x
        | supportMaskDoubleBump p41 p x
        | supportMaskDoubleBump p47 p x
        | supportMaskDoubleBump p59 p x
        | supportMaskDoubleBump p71 p x
  = refl

------------------------------------------------------------------------
-- The existing support-mask quotient is projection-complete because its
-- equivalence relation is definitionally equality of support masks.
------------------------------------------------------------------------

supportMaskExactPresentation :
  Descent.ExactQuotientPresentation Factor.supportMaskQuotient
supportMaskExactPresentation =
  record
    { projectionComplete = λ equality → equality
    }

supportMaskCorrespondenceRespectsEquiv :
  (p : SSP) →
  ∀ {left right : FactorVec} →
  Factor.supportMask left ≡ Factor.supportMask right →
  Hecke.map15 Factor.supportMask (factorVecCorrespondence p left)
  ≡ Hecke.map15 Factor.supportMask (factorVecCorrespondence p right)
supportMaskCorrespondenceRespectsEquiv p {left} {right} equality =
  trans
    (factorVecCorrespondenceProjectsExactly p left)
    (trans
      (cong (MaskHecke.supportMaskCorrespondence p) equality)
      (sym (factorVecCorrespondenceProjectsExactly p right)))

factorVecSupportMaskCorrespondenceDescent :
  Descent.QuotientStablePrimeCorrespondence
    Factor.supportMaskQuotient factorVecCorrespondenceHecke
factorVecSupportMaskCorrespondenceDescent =
  record
    { exactPresentation = supportMaskExactPresentation
    ; correspondenceRespectsEquiv = supportMaskCorrespondenceRespectsEquiv
    }

------------------------------------------------------------------------
-- The repository's pre-existing support-mask correspondence is the canonical
-- quotient correspondence produced by the generic descent theorem.
------------------------------------------------------------------------

existingSupportMaskCorrespondenceIsInduced :
  (p : SSP) →
  (mask : Factor.SupportMask) →
  Hecke.PrimeCorrespondenceHeckeOn.correspondence
    MaskHecke.supportMaskCorrespondenceHecke p mask
  ≡
  Hecke.PrimeCorrespondenceHeckeOn.correspondence
    (Descent.inducedHecke factorVecSupportMaskCorrespondenceDescent) p mask
existingSupportMaskCorrespondenceIsInduced =
  Descent.inducedCorrespondenceUnique
    factorVecSupportMaskCorrespondenceDescent
    MaskHecke.supportMaskCorrespondenceHecke
    factorVecCorrespondenceProjectsExactly

------------------------------------------------------------------------
-- Exact observable-level intertwining with the existing quotient operator.
------------------------------------------------------------------------

factorVecObservableHeckeDescendsToSupportMask :
  (observable : Factor.SupportMask → Nat) →
  (p : SSP) →
  (x : FactorVec) →
  Hecke.PrimeCorrespondenceHeckeOn.operator factorVecCorrespondenceHecke
    (λ state → observable (Factor.supportMask state)) p x
  ≡
  Hecke.PrimeCorrespondenceHeckeOn.operator
    MaskHecke.supportMaskCorrespondenceHecke
    observable p (Factor.supportMask x)
factorVecObservableHeckeDescendsToSupportMask observable p x =
  trans
    (Descent.projectedObservableHeckeCommutes
      factorVecSupportMaskCorrespondenceDescent observable p x)
    (cong
      (λ values → Hecke.sum15 (Hecke.map15 observable values))
      (sym
        (existingSupportMaskCorrespondenceIsInduced
          p (Factor.supportMask x))))

------------------------------------------------------------------------
-- Boundary: this is a genuine quotient/Hecke commuting square, but it is not
-- yet the representation-theoretic SSP intertwiner sought by the Ogg lane.
------------------------------------------------------------------------

record FactorVecSupportMaskHeckeBoundary : Set where
  field
    fineCorrespondenceConstructed : Bool
    fineCorrespondenceConstructedIsTrue :
      fineCorrespondenceConstructed ≡ true

    supportMaskCorrespondenceDerivedAsQuotient : Bool
    supportMaskCorrespondenceDerivedAsQuotientIsTrue :
      supportMaskCorrespondenceDerivedAsQuotient ≡ true

    observableHeckeIntertwiningProved : Bool
    observableHeckeIntertwiningProvedIsTrue :
      observableHeckeIntertwiningProved ≡ true

    identifiesSO3ReductionWithFactorVec : Bool
    identifiesSO3ReductionWithFactorVecIsFalse :
      identifiesSO3ReductionWithFactorVec ≡ false

canonicalFactorVecSupportMaskHeckeBoundary :
  FactorVecSupportMaskHeckeBoundary
canonicalFactorVecSupportMaskHeckeBoundary =
  record
    { fineCorrespondenceConstructed = true
    ; fineCorrespondenceConstructedIsTrue = refl
    ; supportMaskCorrespondenceDerivedAsQuotient = true
    ; supportMaskCorrespondenceDerivedAsQuotientIsTrue = refl
    ; observableHeckeIntertwiningProved = true
    ; observableHeckeIntertwiningProvedIsTrue = refl
    ; identifiesSO3ReductionWithFactorVec = false
    ; identifiesSO3ReductionWithFactorVecIsFalse = refl
    }
