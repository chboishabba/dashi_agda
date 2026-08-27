module DASHI.Core.LacanFregeTernaryRoleChartExact where

------------------------------------------------------------------------
-- LACAN / FREGE-DERIVED TERNARY ROLE CHART
--
-- SOURCE SCOPE
--
-- Jacques Lacan's Seminars IX (L'identification, 1961--62) and XIX (...ou
-- pire, 1971--72) motivate the source-bounded 0/1/2 role reading discussed in
-- the supplied DASHI reconstruction: zero/inexistence, unary trait / S1, and a
-- retroactive second-count position through which repetition becomes legible.
-- No DOI is asserted for the seminars here.
--
-- IMPORTANT S2 BOUNDARY
--
-- The historical constructor name `retroactiveSecondS2` is retained for branch
-- compatibility, but this module does NOT identify the Frege/genesis numeral
-- two with Seminar-XVII discourse-theory S2 (knowledge/signifying battery).
-- `LacanS2RoleSeparationExact` owns that distinction explicitly.
--
-- The role chart is intentionally NOT an anatomy chart and NOT Lacan's formulas
-- of sexuation.  In particular `code2` is not identified with testes or with
-- symbolic castration.  The optional `phallicOnePosition` below is a DASHI
-- interpretive overlay for the discussion's One-centred comparison with
-- Irigaray, not a claim that Lacan published a numbered phallus calculus.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.TernaryRoleCarrierExact as Ternary

------------------------------------------------------------------------
-- Source-grounded role layer.
------------------------------------------------------------------------

data LacanFregeRole : Set where
  zeroOfInexistence
  unaryTraitS1
  retroactiveSecondS2
  : LacanFregeRole

-- Preferred clarified alias: this value is a Frege/genesis second-count role.
fregeRetroactiveSecondCount : LacanFregeRole
fregeRetroactiveSecondCount = retroactiveSecondS2

lacanFregeRole : Ternary.TernaryRoleCode → LacanFregeRole
lacanFregeRole Ternary.code0 = zeroOfInexistence
lacanFregeRole Ternary.code1 = unaryTraitS1
lacanFregeRole Ternary.code2 = fregeRetroactiveSecondCount

lacanFregeChart : Ternary.RoleChart LacanFregeRole
lacanFregeChart = Ternary.role-chart lacanFregeRole

------------------------------------------------------------------------
-- Bounded comparison overlay used only for the Irigaray contrast.
------------------------------------------------------------------------

data LacanianComparisonRole : Set where
  lackPosition
  phallicOnePosition
  secondSignifierPosition
  : LacanianComparisonRole

lacanianComparisonRole :
  Ternary.TernaryRoleCode → LacanianComparisonRole
lacanianComparisonRole Ternary.code0 = lackPosition
lacanianComparisonRole Ternary.code1 = phallicOnePosition
lacanianComparisonRole Ternary.code2 = secondSignifierPosition

lacanianComparisonChart : Ternary.RoleChart LacanianComparisonRole
lacanianComparisonChart = Ternary.role-chart lacanianComparisonRole

------------------------------------------------------------------------
-- One-centred relational grammar.
--
-- This is a finite DASHI comparison grammar, not an assertion that Lacan's
-- complete signifying theory is this graph.  `code1` is the privileged hub;
-- the other two positions are represented relative to it.
------------------------------------------------------------------------

lacanOneCentredEdge :
  Ternary.TernaryRoleCode → Ternary.TernaryRoleCode → Bool
lacanOneCentredEdge Ternary.code1 Ternary.code0 = true
lacanOneCentredEdge Ternary.code1 Ternary.code2 = true
lacanOneCentredEdge _ _ = false

oneAddressesZero :
  lacanOneCentredEdge Ternary.code1 Ternary.code0 ≡ true
oneAddressesZero = refl

oneAddressesTwo :
  lacanOneCentredEdge Ternary.code1 Ternary.code2 ≡ true
oneAddressesTwo = refl

zeroDoesNotAddressOne :
  lacanOneCentredEdge Ternary.code0 Ternary.code1 ≡ false
zeroDoesNotAddressOne = refl

twoDoesNotAddressOne :
  lacanOneCentredEdge Ternary.code2 Ternary.code1 ≡ false
twoDoesNotAddressOne = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record LacanFregeTernaryRoleBoundary : Set where
  constructor lacan-frege-ternary-role-boundary
  field
    numeralTwoMeansTestes : Bool
    numeralTwoMeansTestesIsFalse : numeralTwoMeansTestes ≡ false
    phallusIsIdentifiedWithAnatomicalPenis : Bool
    phallusIsIdentifiedWithAnatomicalPenisIsFalse :
      phallusIsIdentifiedWithAnatomicalPenis ≡ false
    symbolicCastrationIsAnatomicalRemoval : Bool
    symbolicCastrationIsAnatomicalRemovalIsFalse :
      symbolicCastrationIsAnatomicalRemoval ≡ false
    fregeSecondCountIsDefinitionallyDiscourseS2 : Bool
    fregeSecondCountIsDefinitionallyDiscourseS2IsFalse :
      fregeSecondCountIsDefinitionallyDiscourseS2 ≡ false
    fregeDerivedChartIsFormulaOfSexuation : Bool
    fregeDerivedChartIsFormulaOfSexuationIsFalse :
      fregeDerivedChartIsFormulaOfSexuation ≡ false
    comparisonGraphExhaustsLacan : Bool
    comparisonGraphExhaustsLacanIsFalse : comparisonGraphExhaustsLacan ≡ false

canonicalLacanFregeTernaryRoleBoundary : LacanFregeTernaryRoleBoundary
canonicalLacanFregeTernaryRoleBoundary =
  lacan-frege-ternary-role-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
