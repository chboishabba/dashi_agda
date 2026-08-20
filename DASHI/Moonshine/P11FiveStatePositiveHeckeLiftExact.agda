module DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Trees", Springer Monographs in Mathematics.
-- DOI: 10.1007/978-3-642-61856-7.
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- DASHI CONTRIBUTION
--
-- Construct the first genuinely POSITIVE fine geometry in this lane whose
-- quotient simultaneously realizes B_11(2), B_11(3), B_11(5).
--
-- The p=11 Brandt balance 2*B_01 = 3*B_10 implies that an ordinary symmetric
-- equitable binary quotient should have fibre-cardinality ratio 2:3.  The
-- minimal unweighted carrier therefore has five vertices:
--
--   A0,A1          -> j=0,
--   B0,B1,B2       -> j=1728.
--
-- Prime neighbour systems are defined before linearization:
--
-- ell=2:
--   K_(2,3) cross-incidence + one loop on each B vertex;
--
-- ell=3:
--   the complete graph K5;
--
-- ell=5:
--   K_(2,3) cross-incidence, three parallel A-A edges, and two parallel
--   edges between every distinct pair of B vertices.
--
-- Every edge has an actual target vertex and all multiplicities are Nat-valued.
-- Projection commutes edge-by-edge with the already source-verified positive
-- Brandt neighbour systems downstairs.  This is therefore categorically
-- different from the section-generated signed lifts falsified earlier.
--
-- IMPORTANT BOUNDARY:
-- This five-state model is an internally discovered positive finite geometry.
-- It is NOT identified here with quaternion ideal classes, a Bruhat--Tits
-- quotient, an S3 coset space, or the actual SO(3) representation carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin; zero; suc)

import Ontology.Hecke.QuotientRepresentation as Quotient
import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact as Existing
import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive
import DASHI.Moonshine.PositiveNeighbourQuotientDescentExact as Descent
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo
import DASHI.Moonshine.P11PositiveBrandtNeighbourSystemsExact as Brandt

------------------------------------------------------------------------
-- Five-state positive fine carrier and its 2+3 quotient.
------------------------------------------------------------------------

data P11Fine5 : Set where
  a0 a1 b0 b1 b2 : P11Fine5

projectFine5 : P11Fine5 → Geo.P11SupersingularJ
projectFine5 a0 = Geo.jZeroSS
projectFine5 a1 = Geo.jZeroSS
projectFine5 b0 = Geo.j1728SS
projectFine5 b1 = Geo.j1728SS
projectFine5 b2 = Geo.j1728SS

representFine5 : Geo.P11SupersingularJ → P11Fine5
representFine5 Geo.jZeroSS = a0
representFine5 Geo.j1728SS = b0

projectRepresentFine5 :
  (coarse : Geo.P11SupersingularJ) →
  projectFine5 (representFine5 coarse) ≡ coarse
projectRepresentFine5 Geo.jZeroSS = refl
projectRepresentFine5 Geo.j1728SS = refl

fine5Equivalence : Quotient.EquivalenceOn P11Fine5
fine5Equivalence =
  record
    { Quotient._≈_ = λ left right → projectFine5 left ≡ projectFine5 right
    ; Quotient.refl = λ _ → refl
    ; Quotient.sym = λ equality → sym equality
    ; Quotient.trans = λ leftMiddle middleRight → trans leftMiddle middleRight
    }

fine5Quotient :
  Quotient.QuotientInterfaceOn P11Fine5 Geo.P11SupersingularJ
fine5Quotient =
  record
    { Quotient.equiv = fine5Equivalence
    ; Quotient.proj = projectFine5
    ; Quotient.respect-proj = λ equality → equality
    ; Quotient.representative = representFine5
    ; Quotient.section = projectRepresentFine5
    }

fine5ExactPresentation : Existing.ExactQuotientPresentation fine5Quotient
fine5ExactPresentation =
  record
    { Existing.projectionComplete = λ equality → equality
    }

------------------------------------------------------------------------
-- ell = 2 positive fine geometry.
------------------------------------------------------------------------

r2Neighbour : P11Fine5 → Fin 3 → P11Fine5
r2Neighbour a0 zero = b0
r2Neighbour a0 (suc zero) = b1
r2Neighbour a0 (suc (suc zero)) = b2
r2Neighbour a1 zero = b0
r2Neighbour a1 (suc zero) = b1
r2Neighbour a1 (suc (suc zero)) = b2
r2Neighbour b0 zero = a0
r2Neighbour b0 (suc zero) = a1
r2Neighbour b0 (suc (suc zero)) = b0
r2Neighbour b1 zero = a0
r2Neighbour b1 (suc zero) = a1
r2Neighbour b1 (suc (suc zero)) = b1
r2Neighbour b2 zero = a0
r2Neighbour b2 (suc zero) = a1
r2Neighbour b2 (suc (suc zero)) = b2

R2Positive : Positive.PositiveFiniteNeighbourSystem P11Fine5
R2Positive =
  record
    { Positive.arity = 3
    ; Positive.neighbour = r2Neighbour
    }

r2ProjectionCommutes :
  (fine : P11Fine5) →
  (edge : Fin 3) →
  projectFine5 (r2Neighbour fine edge)
  ≡ Brandt.ell2Neighbour (projectFine5 fine) edge
r2ProjectionCommutes a0 zero = refl
r2ProjectionCommutes a0 (suc zero) = refl
r2ProjectionCommutes a0 (suc (suc zero)) = refl
r2ProjectionCommutes a1 zero = refl
r2ProjectionCommutes a1 (suc zero) = refl
r2ProjectionCommutes a1 (suc (suc zero)) = refl
r2ProjectionCommutes b0 zero = refl
r2ProjectionCommutes b0 (suc zero) = refl
r2ProjectionCommutes b0 (suc (suc zero)) = refl
r2ProjectionCommutes b1 zero = refl
r2ProjectionCommutes b1 (suc zero) = refl
r2ProjectionCommutes b1 (suc (suc zero)) = refl
r2ProjectionCommutes b2 zero = refl
r2ProjectionCommutes b2 (suc zero) = refl
r2ProjectionCommutes b2 (suc (suc zero)) = refl

------------------------------------------------------------------------
-- ell = 3: K5.
------------------------------------------------------------------------

r3Neighbour : P11Fine5 → Fin 4 → P11Fine5
r3Neighbour a0 zero = a1
r3Neighbour a0 (suc zero) = b0
r3Neighbour a0 (suc (suc zero)) = b1
r3Neighbour a0 (suc (suc (suc zero))) = b2
r3Neighbour a1 zero = a0
r3Neighbour a1 (suc zero) = b0
r3Neighbour a1 (suc (suc zero)) = b1
r3Neighbour a1 (suc (suc (suc zero))) = b2
r3Neighbour b0 zero = a0
r3Neighbour b0 (suc zero) = a1
r3Neighbour b0 (suc (suc zero)) = b1
r3Neighbour b0 (suc (suc (suc zero))) = b2
r3Neighbour b1 zero = a0
r3Neighbour b1 (suc zero) = a1
r3Neighbour b1 (suc (suc zero)) = b0
r3Neighbour b1 (suc (suc (suc zero))) = b2
r3Neighbour b2 zero = a0
r3Neighbour b2 (suc zero) = a1
r3Neighbour b2 (suc (suc zero)) = b0
r3Neighbour b2 (suc (suc (suc zero))) = b1

R3Positive : Positive.PositiveFiniteNeighbourSystem P11Fine5
R3Positive =
  record
    { Positive.arity = 4
    ; Positive.neighbour = r3Neighbour
    }

r3ProjectionCommutes :
  (fine : P11Fine5) →
  (edge : Fin 4) →
  projectFine5 (r3Neighbour fine edge)
  ≡ Brandt.ell3Neighbour (projectFine5 fine) edge
r3ProjectionCommutes a0 zero = refl
r3ProjectionCommutes a0 (suc zero) = refl
r3ProjectionCommutes a0 (suc (suc zero)) = refl
r3ProjectionCommutes a0 (suc (suc (suc zero))) = refl
r3ProjectionCommutes a1 zero = refl
r3ProjectionCommutes a1 (suc zero) = refl
r3ProjectionCommutes a1 (suc (suc zero)) = refl
r3ProjectionCommutes a1 (suc (suc (suc zero))) = refl
r3ProjectionCommutes b0 zero = refl
r3ProjectionCommutes b0 (suc zero) = refl
r3ProjectionCommutes b0 (suc (suc zero)) = refl
r3ProjectionCommutes b0 (suc (suc (suc zero))) = refl
r3ProjectionCommutes b1 zero = refl
r3ProjectionCommutes b1 (suc zero) = refl
r3ProjectionCommutes b1 (suc (suc zero)) = refl
r3ProjectionCommutes b1 (suc (suc (suc zero))) = refl
r3ProjectionCommutes b2 zero = refl
r3ProjectionCommutes b2 (suc zero) = refl
r3ProjectionCommutes b2 (suc (suc zero)) = refl
r3ProjectionCommutes b2 (suc (suc (suc zero))) = refl

------------------------------------------------------------------------
-- ell = 5: positive multigraph lift.
------------------------------------------------------------------------

r5Neighbour : P11Fine5 → Fin 6 → P11Fine5
r5Neighbour a0 zero = a1
r5Neighbour a0 (suc zero) = a1
r5Neighbour a0 (suc (suc zero)) = a1
r5Neighbour a0 (suc (suc (suc zero))) = b0
r5Neighbour a0 (suc (suc (suc (suc zero)))) = b1
r5Neighbour a0 (suc (suc (suc (suc (suc zero))))) = b2
r5Neighbour a1 zero = a0
r5Neighbour a1 (suc zero) = a0
r5Neighbour a1 (suc (suc zero)) = a0
r5Neighbour a1 (suc (suc (suc zero))) = b0
r5Neighbour a1 (suc (suc (suc (suc zero)))) = b1
r5Neighbour a1 (suc (suc (suc (suc (suc zero))))) = b2
r5Neighbour b0 zero = a0
r5Neighbour b0 (suc zero) = a1
r5Neighbour b0 (suc (suc zero)) = b1
r5Neighbour b0 (suc (suc (suc zero))) = b1
r5Neighbour b0 (suc (suc (suc (suc zero)))) = b2
r5Neighbour b0 (suc (suc (suc (suc (suc zero))))) = b2
r5Neighbour b1 zero = a0
r5Neighbour b1 (suc zero) = a1
r5Neighbour b1 (suc (suc zero)) = b0
r5Neighbour b1 (suc (suc (suc zero))) = b0
r5Neighbour b1 (suc (suc (suc (suc zero)))) = b2
r5Neighbour b1 (suc (suc (suc (suc (suc zero))))) = b2
r5Neighbour b2 zero = a0
r5Neighbour b2 (suc zero) = a1
r5Neighbour b2 (suc (suc zero)) = b0
r5Neighbour b2 (suc (suc (suc zero))) = b0
r5Neighbour b2 (suc (suc (suc (suc zero)))) = b1
r5Neighbour b2 (suc (suc (suc (suc (suc zero))))) = b1

R5Positive : Positive.PositiveFiniteNeighbourSystem P11Fine5
R5Positive =
  record
    { Positive.arity = 6
    ; Positive.neighbour = r5Neighbour
    }

r5ProjectionCommutes :
  (fine : P11Fine5) →
  (edge : Fin 6) →
  projectFine5 (r5Neighbour fine edge)
  ≡ Brandt.ell5Neighbour (projectFine5 fine) edge
r5ProjectionCommutes a0 zero = refl
r5ProjectionCommutes a0 (suc zero) = refl
r5ProjectionCommutes a0 (suc (suc zero)) = refl
r5ProjectionCommutes a0 (suc (suc (suc zero))) = refl
r5ProjectionCommutes a0 (suc (suc (suc (suc zero)))) = refl
r5ProjectionCommutes a0 (suc (suc (suc (suc (suc zero))))) = refl
r5ProjectionCommutes a1 zero = refl
r5ProjectionCommutes a1 (suc zero) = refl
r5ProjectionCommutes a1 (suc (suc zero)) = refl
r5ProjectionCommutes a1 (suc (suc (suc zero))) = refl
r5ProjectionCommutes a1 (suc (suc (suc (suc zero)))) = refl
r5ProjectionCommutes a1 (suc (suc (suc (suc (suc zero))))) = refl
r5ProjectionCommutes b0 zero = refl
r5ProjectionCommutes b0 (suc zero) = refl
r5ProjectionCommutes b0 (suc (suc zero)) = refl
r5ProjectionCommutes b0 (suc (suc (suc zero))) = refl
r5ProjectionCommutes b0 (suc (suc (suc (suc zero)))) = refl
r5ProjectionCommutes b0 (suc (suc (suc (suc (suc zero))))) = refl
r5ProjectionCommutes b1 zero = refl
r5ProjectionCommutes b1 (suc zero) = refl
r5ProjectionCommutes b1 (suc (suc zero)) = refl
r5ProjectionCommutes b1 (suc (suc (suc zero))) = refl
r5ProjectionCommutes b1 (suc (suc (suc (suc zero)))) = refl
r5ProjectionCommutes b1 (suc (suc (suc (suc (suc zero))))) = refl
r5ProjectionCommutes b2 zero = refl
r5ProjectionCommutes b2 (suc zero) = refl
r5ProjectionCommutes b2 (suc (suc zero)) = refl
r5ProjectionCommutes b2 (suc (suc (suc zero))) = refl
r5ProjectionCommutes b2 (suc (suc (suc (suc zero)))) = refl
r5ProjectionCommutes b2 (suc (suc (suc (suc (suc zero))))) = refl

------------------------------------------------------------------------
-- Quotient-stability derived from edge-by-edge projection, not assumed.
------------------------------------------------------------------------

r2QuotientStable :
  Descent.QuotientStablePositiveNeighbourSystem fine5Quotient R2Positive
r2QuotientStable =
  record
    { Descent.exactPresentation = fine5ExactPresentation
    ; Descent.neighbourRespectsEquiv =
        λ {left} {right} same edge →
          trans
            (r2ProjectionCommutes left edge)
            (trans
              (cong (λ coarse → Brandt.ell2Neighbour coarse edge) same)
              (sym (r2ProjectionCommutes right edge)))
    }

r3QuotientStable :
  Descent.QuotientStablePositiveNeighbourSystem fine5Quotient R3Positive
r3QuotientStable =
  record
    { Descent.exactPresentation = fine5ExactPresentation
    ; Descent.neighbourRespectsEquiv =
        λ {left} {right} same edge →
          trans
            (r3ProjectionCommutes left edge)
            (trans
              (cong (λ coarse → Brandt.ell3Neighbour coarse edge) same)
              (sym (r3ProjectionCommutes right edge)))
    }

r5QuotientStable :
  Descent.QuotientStablePositiveNeighbourSystem fine5Quotient R5Positive
r5QuotientStable =
  record
    { Descent.exactPresentation = fine5ExactPresentation
    ; Descent.neighbourRespectsEquiv =
        λ {left} {right} same edge →
          trans
            (r5ProjectionCommutes left edge)
            (trans
              (cong (λ coarse → Brandt.ell5Neighbour coarse edge) same)
              (sym (r5ProjectionCommutes right edge)))
    }

------------------------------------------------------------------------
-- Consequently every coarse observable satisfies exact positive descent.
------------------------------------------------------------------------

r2ObservableCommutes :
  (observable : Geo.P11SupersingularJ → Nat) →
  (fine : P11Fine5) →
  Positive.positiveOperator R2Positive (λ x → observable (projectFine5 x)) fine
  ≡
  Positive.positiveOperator
    (Descent.inducedPositiveNeighbourSystem r2QuotientStable)
    observable (projectFine5 fine)
r2ObservableCommutes = Descent.projectedPositiveOperatorCommutes r2QuotientStable

r3ObservableCommutes :
  (observable : Geo.P11SupersingularJ → Nat) →
  (fine : P11Fine5) →
  Positive.positiveOperator R3Positive (λ x → observable (projectFine5 x)) fine
  ≡
  Positive.positiveOperator
    (Descent.inducedPositiveNeighbourSystem r3QuotientStable)
    observable (projectFine5 fine)
r3ObservableCommutes = Descent.projectedPositiveOperatorCommutes r3QuotientStable

r5ObservableCommutes :
  (observable : Geo.P11SupersingularJ → Nat) →
  (fine : P11Fine5) →
  Positive.positiveOperator R5Positive (λ x → observable (projectFine5 x)) fine
  ≡
  Positive.positiveOperator
    (Descent.inducedPositiveNeighbourSystem r5QuotientStable)
    observable (projectFine5 fine)
r5ObservableCommutes = Descent.projectedPositiveOperatorCommutes r5QuotientStable

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record P11FiveStatePositiveLiftBoundary : Set where
  field
    minimalTwoThreeFineCarrierConstructed : Bool
    minimalTwoThreeFineCarrierConstructedIsTrue :
      minimalTwoThreeFineCarrierConstructed ≡ true

    threePrimePositiveNeighbourSystemsConstructed : Bool
    threePrimePositiveNeighbourSystemsConstructedIsTrue :
      threePrimePositiveNeighbourSystemsConstructed ≡ true

    projectionCommutesNeighbourByNeighbour : Bool
    projectionCommutesNeighbourByNeighbourIsTrue :
      projectionCommutesNeighbourByNeighbour ≡ true

    positiveQuotientDescentConstructed : Bool
    positiveQuotientDescentConstructedIsTrue :
      positiveQuotientDescentConstructed ≡ true

    sectionGeneratedSignedLiftUsed : Bool
    sectionGeneratedSignedLiftUsedIsFalse :
      sectionGeneratedSignedLiftUsed ≡ false

    quaternionOrBruhatTitsIdentificationConstructed : Bool
    quaternionOrBruhatTitsIdentificationConstructedIsFalse :
      quaternionOrBruhatTitsIdentificationConstructed ≡ false

canonicalP11FiveStatePositiveLiftBoundary : P11FiveStatePositiveLiftBoundary
canonicalP11FiveStatePositiveLiftBoundary =
  record
    { minimalTwoThreeFineCarrierConstructed = true
    ; minimalTwoThreeFineCarrierConstructedIsTrue = refl
    ; threePrimePositiveNeighbourSystemsConstructed = true
    ; threePrimePositiveNeighbourSystemsConstructedIsTrue = refl
    ; projectionCommutesNeighbourByNeighbour = true
    ; projectionCommutesNeighbourByNeighbourIsTrue = refl
    ; positiveQuotientDescentConstructed = true
    ; positiveQuotientDescentConstructedIsTrue = refl
    ; sectionGeneratedSignedLiftUsed = false
    ; sectionGeneratedSignedLiftUsedIsFalse = refl
    ; quaternionOrBruhatTitsIdentificationConstructed = false
    ; quaternionOrBruhatTitsIdentificationConstructedIsFalse = refl
    }
