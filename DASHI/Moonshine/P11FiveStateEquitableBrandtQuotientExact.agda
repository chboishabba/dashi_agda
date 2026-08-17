module DASHI.Moonshine.P11FiveStateEquitableBrandtQuotientExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Chris Godsil and Gordon Royle,
-- "Algebraic Graph Theory", Graduate Texts in Mathematics 207,
-- Springer, 2001.
-- DOI: 10.1007/978-1-4613-0163-9.
--
-- DASHI CONTRIBUTION
--
-- Show that the five-state positive p=11 model is an equitable graph quotient
-- of the actual supersingular Brandt operators at ell=2,3,5.
--
-- This is deliberately weaker than edge-label descent and stronger than matrix
-- resemblance: every Nat-valued coarse observable has the same fine adjacency
-- readout on vertices in the same 2+3 fibre, and the induced coarse operator is
-- definitionally the source-verified Brandt neighbour-count operator.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive
import DASHI.Moonshine.EquitablePositiveQuotientExact as Equitable
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11PositiveBrandtNeighbourSystemsExact as Brandt
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as Geo

------------------------------------------------------------------------
-- ell=2 equitability.
------------------------------------------------------------------------

r2CoarseObservableCongruent :
  ∀ {left right : Fine.P11Fine5} →
  Fine.projectFine5 left ≡ Fine.projectFine5 right →
  (observable : Geo.P11SupersingularJ → Nat) →
  Positive.positiveOperator Fine.R2Positive
    (λ state → observable (Fine.projectFine5 state)) left
  ≡
  Positive.positiveOperator Fine.R2Positive
    (λ state → observable (Fine.projectFine5 state)) right
r2CoarseObservableCongruent {Fine.a0} {Fine.a0} equality observable = refl
r2CoarseObservableCongruent {Fine.a0} {Fine.a1} equality observable = refl
r2CoarseObservableCongruent {Fine.a0} {Fine.b0} () observable
r2CoarseObservableCongruent {Fine.a0} {Fine.b1} () observable
r2CoarseObservableCongruent {Fine.a0} {Fine.b2} () observable
r2CoarseObservableCongruent {Fine.a1} {Fine.a0} equality observable = refl
r2CoarseObservableCongruent {Fine.a1} {Fine.a1} equality observable = refl
r2CoarseObservableCongruent {Fine.a1} {Fine.b0} () observable
r2CoarseObservableCongruent {Fine.a1} {Fine.b1} () observable
r2CoarseObservableCongruent {Fine.a1} {Fine.b2} () observable
r2CoarseObservableCongruent {Fine.b0} {Fine.a0} () observable
r2CoarseObservableCongruent {Fine.b0} {Fine.a1} () observable
r2CoarseObservableCongruent {Fine.b0} {Fine.b0} equality observable = refl
r2CoarseObservableCongruent {Fine.b0} {Fine.b1} equality observable = refl
r2CoarseObservableCongruent {Fine.b0} {Fine.b2} equality observable = refl
r2CoarseObservableCongruent {Fine.b1} {Fine.a0} () observable
r2CoarseObservableCongruent {Fine.b1} {Fine.a1} () observable
r2CoarseObservableCongruent {Fine.b1} {Fine.b0} equality observable = refl
r2CoarseObservableCongruent {Fine.b1} {Fine.b1} equality observable = refl
r2CoarseObservableCongruent {Fine.b1} {Fine.b2} equality observable = refl
r2CoarseObservableCongruent {Fine.b2} {Fine.a0} () observable
r2CoarseObservableCongruent {Fine.b2} {Fine.a1} () observable
r2CoarseObservableCongruent {Fine.b2} {Fine.b0} equality observable = refl
r2CoarseObservableCongruent {Fine.b2} {Fine.b1} equality observable = refl
r2CoarseObservableCongruent {Fine.b2} {Fine.b2} equality observable = refl

r2Equitable :
  Equitable.EquitablePositiveQuotient Fine.fine5Quotient Fine.R2Positive
r2Equitable =
  record
    { Equitable.coarseObservableCongruent = r2CoarseObservableCongruent
    }

------------------------------------------------------------------------
-- ell=3 and ell=5 have the same fibre-invariance shape.
------------------------------------------------------------------------

r3CoarseObservableCongruent :
  ∀ {left right : Fine.P11Fine5} →
  Fine.projectFine5 left ≡ Fine.projectFine5 right →
  (observable : Geo.P11SupersingularJ → Nat) →
  Positive.positiveOperator Fine.R3Positive
    (λ state → observable (Fine.projectFine5 state)) left
  ≡
  Positive.positiveOperator Fine.R3Positive
    (λ state → observable (Fine.projectFine5 state)) right
r3CoarseObservableCongruent {Fine.a0} {Fine.a0} equality observable = refl
r3CoarseObservableCongruent {Fine.a0} {Fine.a1} equality observable = refl
r3CoarseObservableCongruent {Fine.a0} {Fine.b0} () observable
r3CoarseObservableCongruent {Fine.a0} {Fine.b1} () observable
r3CoarseObservableCongruent {Fine.a0} {Fine.b2} () observable
r3CoarseObservableCongruent {Fine.a1} {Fine.a0} equality observable = refl
r3CoarseObservableCongruent {Fine.a1} {Fine.a1} equality observable = refl
r3CoarseObservableCongruent {Fine.a1} {Fine.b0} () observable
r3CoarseObservableCongruent {Fine.a1} {Fine.b1} () observable
r3CoarseObservableCongruent {Fine.a1} {Fine.b2} () observable
r3CoarseObservableCongruent {Fine.b0} {Fine.a0} () observable
r3CoarseObservableCongruent {Fine.b0} {Fine.a1} () observable
r3CoarseObservableCongruent {Fine.b0} {Fine.b0} equality observable = refl
r3CoarseObservableCongruent {Fine.b0} {Fine.b1} equality observable = refl
r3CoarseObservableCongruent {Fine.b0} {Fine.b2} equality observable = refl
r3CoarseObservableCongruent {Fine.b1} {Fine.a0} () observable
r3CoarseObservableCongruent {Fine.b1} {Fine.a1} () observable
r3CoarseObservableCongruent {Fine.b1} {Fine.b0} equality observable = refl
r3CoarseObservableCongruent {Fine.b1} {Fine.b1} equality observable = refl
r3CoarseObservableCongruent {Fine.b1} {Fine.b2} equality observable = refl
r3CoarseObservableCongruent {Fine.b2} {Fine.a0} () observable
r3CoarseObservableCongruent {Fine.b2} {Fine.a1} () observable
r3CoarseObservableCongruent {Fine.b2} {Fine.b0} equality observable = refl
r3CoarseObservableCongruent {Fine.b2} {Fine.b1} equality observable = refl
r3CoarseObservableCongruent {Fine.b2} {Fine.b2} equality observable = refl

r3Equitable :
  Equitable.EquitablePositiveQuotient Fine.fine5Quotient Fine.R3Positive
r3Equitable =
  record
    { Equitable.coarseObservableCongruent = r3CoarseObservableCongruent
    }

r5CoarseObservableCongruent :
  ∀ {left right : Fine.P11Fine5} →
  Fine.projectFine5 left ≡ Fine.projectFine5 right →
  (observable : Geo.P11SupersingularJ → Nat) →
  Positive.positiveOperator Fine.R5Positive
    (λ state → observable (Fine.projectFine5 state)) left
  ≡
  Positive.positiveOperator Fine.R5Positive
    (λ state → observable (Fine.projectFine5 state)) right
r5CoarseObservableCongruent {Fine.a0} {Fine.a0} equality observable = refl
r5CoarseObservableCongruent {Fine.a0} {Fine.a1} equality observable = refl
r5CoarseObservableCongruent {Fine.a0} {Fine.b0} () observable
r5CoarseObservableCongruent {Fine.a0} {Fine.b1} () observable
r5CoarseObservableCongruent {Fine.a0} {Fine.b2} () observable
r5CoarseObservableCongruent {Fine.a1} {Fine.a0} equality observable = refl
r5CoarseObservableCongruent {Fine.a1} {Fine.a1} equality observable = refl
r5CoarseObservableCongruent {Fine.a1} {Fine.b0} () observable
r5CoarseObservableCongruent {Fine.a1} {Fine.b1} () observable
r5CoarseObservableCongruent {Fine.a1} {Fine.b2} () observable
r5CoarseObservableCongruent {Fine.b0} {Fine.a0} () observable
r5CoarseObservableCongruent {Fine.b0} {Fine.a1} () observable
r5CoarseObservableCongruent {Fine.b0} {Fine.b0} equality observable = refl
r5CoarseObservableCongruent {Fine.b0} {Fine.b1} equality observable = refl
r5CoarseObservableCongruent {Fine.b0} {Fine.b2} equality observable = refl
r5CoarseObservableCongruent {Fine.b1} {Fine.a0} () observable
r5CoarseObservableCongruent {Fine.b1} {Fine.a1} () observable
r5CoarseObservableCongruent {Fine.b1} {Fine.b0} equality observable = refl
r5CoarseObservableCongruent {Fine.b1} {Fine.b1} equality observable = refl
r5CoarseObservableCongruent {Fine.b1} {Fine.b2} equality observable = refl
r5CoarseObservableCongruent {Fine.b2} {Fine.a0} () observable
r5CoarseObservableCongruent {Fine.b2} {Fine.a1} () observable
r5CoarseObservableCongruent {Fine.b2} {Fine.b0} equality observable = refl
r5CoarseObservableCongruent {Fine.b2} {Fine.b1} equality observable = refl
r5CoarseObservableCongruent {Fine.b2} {Fine.b2} equality observable = refl

r5Equitable :
  Equitable.EquitablePositiveQuotient Fine.fine5Quotient Fine.R5Positive
r5Equitable =
  record
    { Equitable.coarseObservableCongruent = r5CoarseObservableCongruent
    }

------------------------------------------------------------------------
-- The induced equitable operators are exactly the verified Brandt operators.
------------------------------------------------------------------------

r2InducedIsBrandt :
  (observable : Geo.P11SupersingularJ → Nat) →
  (coarse : Geo.P11SupersingularJ) →
  Equitable.inducedEquitableOperator r2Equitable observable coarse
  ≡ Positive.positiveOperator
      (Positive.fromClassicalPrime Brandt.B11ell2Positive)
      observable coarse
r2InducedIsBrandt observable Geo.jZeroSS = refl
r2InducedIsBrandt observable Geo.j1728SS = refl

r3InducedIsBrandt :
  (observable : Geo.P11SupersingularJ → Nat) →
  (coarse : Geo.P11SupersingularJ) →
  Equitable.inducedEquitableOperator r3Equitable observable coarse
  ≡ Positive.positiveOperator
      (Positive.fromClassicalPrime Brandt.B11ell3Positive)
      observable coarse
r3InducedIsBrandt observable Geo.jZeroSS = refl
r3InducedIsBrandt observable Geo.j1728SS = refl

r5InducedIsBrandt :
  (observable : Geo.P11SupersingularJ → Nat) →
  (coarse : Geo.P11SupersingularJ) →
  Equitable.inducedEquitableOperator r5Equitable observable coarse
  ≡ Positive.positiveOperator
      (Positive.fromClassicalPrime Brandt.B11ell5Positive)
      observable coarse
r5InducedIsBrandt observable Geo.jZeroSS = refl
r5InducedIsBrandt observable Geo.j1728SS = refl

record P11FiveStateEquitableBoundary : Set where
  field
    allThreePrimeSystemsEquitable : Bool
    allThreePrimeSystemsEquitableIsTrue : allThreePrimeSystemsEquitable ≡ true

    inducedOperatorsAreVerifiedBrandtOperators : Bool
    inducedOperatorsAreVerifiedBrandtOperatorsIsTrue :
      inducedOperatorsAreVerifiedBrandtOperators ≡ true

    individualGeneratorLabelsRequiredToDescend : Bool
    individualGeneratorLabelsRequiredToDescendIsFalse :
      individualGeneratorLabelsRequiredToDescend ≡ false

    fiveStateCarrierIdentifiedWithArithmeticIdealClasses : Bool
    fiveStateCarrierIdentifiedWithArithmeticIdealClassesIsFalse :
      fiveStateCarrierIdentifiedWithArithmeticIdealClasses ≡ false

canonicalP11FiveStateEquitableBoundary : P11FiveStateEquitableBoundary
canonicalP11FiveStateEquitableBoundary =
  record
    { allThreePrimeSystemsEquitable = true
    ; allThreePrimeSystemsEquitableIsTrue = refl
    ; inducedOperatorsAreVerifiedBrandtOperators = true
    ; inducedOperatorsAreVerifiedBrandtOperatorsIsTrue = refl
    ; individualGeneratorLabelsRequiredToDescend = false
    ; individualGeneratorLabelsRequiredToDescendIsFalse = refl
    ; fiveStateCarrierIdentifiedWithArithmeticIdealClasses = false
    ; fiveStateCarrierIdentifiedWithArithmeticIdealClassesIsFalse = refl
    }
