module DASHI.Mathematics.Complexity.CookLevinPolynomialSizeExact where

------------------------------------------------------------------------
-- POLYNOMIAL SIZE ACCOUNTING FOR THE FINITE TABLEAU/CNF LAYERS
--
-- Given an actual CookLevinFiniteRepresentation:
--
--   timeBound  : PolynomialBound
--   spaceBound : PolynomialBound
--
-- the tableau grid size is polynomial by native product closure.  Multiplying
-- by a fixed cell width or a fixed local CNF-template clause count preserves
-- polynomiality.  This pays the variable-count and local-clause-count size
-- obligations independently of the remaining semantic placement theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _*_)
open import Agda.Builtin.List using (List)

import DASHI.Core.EfficientRecoverableQuotientExact as ERQ
import DASHI.Mathematics.Complexity.FiniteLocalTableauEncodingExact as Tableau
import DASHI.Mathematics.Complexity.FixedWidthTruthTableCNFExact as CNF
import DASHI.Mathematics.Complexity.CookLevinGridReplicationExact as Grid
import DASHI.Mathematics.Complexity.PolynomialBoundClosureExact as Poly

gridPositionsAt :
  ∀ {code} →
  Tableau.CookLevinFiniteRepresentation code →
  Nat → Nat
gridPositionsAt representation inputSize =
  Tableau.timeBound representation inputSize
  * Tableau.spaceBound representation inputSize

gridPositionsPolynomial :
  ∀ {code}
    (representation : Tableau.CookLevinFiniteRepresentation code) →
  ERQ.PolynomialBound (gridPositionsAt representation)
gridPositionsPolynomial representation =
  Poly.productPolynomialBound
    (Tableau.timePolynomial representation)
    (Tableau.spacePolynomial representation)

tableauVariableCountAt :
  ∀ {code} →
  Tableau.CookLevinFiniteRepresentation code →
  Nat → Nat
tableauVariableCountAt {code} representation inputSize =
  gridPositionsAt representation inputSize
  * Tableau.cellWidth code

tableauVariableCountPolynomial :
  ∀ {code}
    (representation : Tableau.CookLevinFiniteRepresentation code) →
  ERQ.PolynomialBound
    (tableauVariableCountAt representation)
tableauVariableCountPolynomial {code} representation =
  Poly.rightConstantMultiplePolynomialBound
    (Tableau.cellWidth code)
    (gridPositionsPolynomial representation)

replicatedLocalClauseCountAt :
  ∀ {code width}
    (representation : Tableau.CookLevinFiniteRepresentation code)
    (template : CNF.CNF width) →
  Nat → Nat
replicatedLocalClauseCountAt representation template inputSize =
  gridPositionsAt representation inputSize
  * Grid.listLength template

replicatedLocalClauseCountPolynomial :
  ∀ {code width}
    (representation : Tableau.CookLevinFiniteRepresentation code)
    (template : CNF.CNF width) →
  ERQ.PolynomialBound
    (replicatedLocalClauseCountAt representation template)
replicatedLocalClauseCountPolynomial representation template =
  Poly.rightConstantMultiplePolynomialBound
    (Grid.listLength template)
    (gridPositionsPolynomial representation)

record CookLevinPolynomialSizeBoundary : Set where
  constructor cook-levin-polynomial-size-boundary
  field
    polynomialGridSizePaid : Agda.Builtin.Bool.Bool
    polynomialVariableCountPaid : Agda.Builtin.Bool.Bool
    fixedTemplatePolynomialClauseCountPaid : Agda.Builtin.Bool.Bool
    windowVariablePlacementSemanticsPaid : Agda.Builtin.Bool.Bool
    fullCookLevinReductionPaid : Agda.Builtin.Bool.Bool

canonicalCookLevinPolynomialSizeBoundary :
  CookLevinPolynomialSizeBoundary
canonicalCookLevinPolynomialSizeBoundary =
  cook-levin-polynomial-size-boundary
    Agda.Builtin.Bool.true
    Agda.Builtin.Bool.true
    Agda.Builtin.Bool.true
    Agda.Builtin.Bool.false
    Agda.Builtin.Bool.false
