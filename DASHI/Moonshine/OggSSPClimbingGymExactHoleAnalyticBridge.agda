module DASHI.Moonshine.OggSSPClimbingGymExactHoleAnalyticBridge where

------------------------------------------------------------------------
-- ANALYTIC HEIGHT -> EXACT FINITE HOLE ADDRESS
--
-- `OggSSPClimbingGymAnalyticRadixAdapterExact` already isolates arbitrary-real
-- phase quantisation behind explicit authority.  The hole vertices are easier:
-- their declared phase is m / p^a, so `ExactHoleRadixCodec` can construct the
-- finite address directly from m.
--
-- The only same-object payment needed to combine those views is that the
-- authority's quantisation of the rational vertex agrees with the exact Nat
-- codec.  Once that agreement is supplied, the figure-facing hole observer no
-- longer obtains its hole address by applying a real floor/frac quantiser.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Moonshine.OggSSPClimbingGymAnalyticRadixAdapterExact as Analytic
import DASHI.Moonshine.OggSSPClimbingGymExactHoleRadixCodec as Hole
import DASHI.Moonshine.OggSSPClimbingGymFigureObservationExact as Figure
import DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact as Gym

record ExactHoleAnalyticAgreement
    (R : Real.ConstructedOrderedCompleteReal)
    (E : Real.ConstructedRealExponential R)
    (L : Real.ConstructedRealLogarithm R E)
    (CE : Complex.ConstructedComplexExponential R E)
    (authority : Analytic.AnalyticRadixQuantisationAuthority R E L CE)
    : Set₁ where
  constructor exact-hole-analytic-agreement
  field
    vertexQuantisationAgreesWithNatCodec :
      (form : Gym.WallForm) →
      (m : Nat) →
      Analytic.analyticHoleAddress authority form m
      ≡ Hole.exactHoleRadialAddress form m

open ExactHoleAnalyticAgreement public

exactHoleAnalyticWallObserver :
  ∀ {R E L CE}
    {authority : Analytic.AnalyticRadixQuantisationAuthority R E L CE} →
  ExactHoleAnalyticAgreement R E L CE authority →
  (form : Gym.WallForm) →
  Figure.WallHeightHoleObserver form
exactHoleAnalyticWallObserver {R} {authority = authority} agreement form = record
  { Height = Real.Real R
  ; phaseAddress = Analytic.analyticPhaseAddress authority form
  ; holeHeight = Analytic.analyticHoleHeight authority form
  ; holeAddress = Hole.exactHoleRadialAddress form
  ; holeAtDeclaredVertex = λ m →
      trans
        (Analytic.analyticHoleLandsOnDeclaredVertex authority form m)
        (vertexQuantisationAgreesWithNatCodec agreement form m)
  ; phaseFormulaLabel = Figure.jmdPhaseFormulaLabel
  ; holeFormulaLabel = Figure.jmdHoleFormulaLabel
  ; spacingFormulaLabel = Figure.jmdHoleSpacingFormulaLabel
  }

record ExactHoleAnalyticBridgeBoundary : Set where
  constructor exact-hole-analytic-bridge-boundary
  field
    analyticHoleHeightReused : Bool
    exactNatHoleAddressReused : Bool
    sameObjectAddressAgreementExplicit : Bool
    holeAddressUsesExactNatRadixCodec : Bool
    holeAddressRequiresSecondRealFloor : Bool
    arbitraryHeightPhaseQuantiserStillSeparate : Bool

    agreementCreatesZetaParametrisation : Bool
    agreementCreatesMonsterSpecificity : Bool

open ExactHoleAnalyticBridgeBoundary public

canonicalExactHoleAnalyticBridgeBoundary : ExactHoleAnalyticBridgeBoundary
canonicalExactHoleAnalyticBridgeBoundary =
  exact-hole-analytic-bridge-boundary
    true true true true false true
    false false
