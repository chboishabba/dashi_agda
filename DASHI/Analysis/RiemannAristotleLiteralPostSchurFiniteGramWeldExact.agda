module DASHI.Analysis.RiemannAristotleLiteralPostSchurFiniteGramWeldExact where

------------------------------------------------------------------------
-- G1 CLOSURE, TYPE-CORRECT VERSION
--
-- The literal RH post-Schur response has three REAL coordinates (one per
-- taper).  NS Round180 happened to instantiate the same finite Gram algebra on
-- rational Complex3, but RH must not be coerced into that rational instance.
--
-- `FiniteSignedGramTelescopeExact` extracts the algebra from Round180.  Here we
-- weld the literal three-coordinate RH shape to that scalar-generic theorem.
-- The scalar implementation is intentionally abstract: it may later be the
-- exact constructive/real carrier used by the RH formalisation.
--
-- Consequently G1 is now a representation/algebra closure, not an analytic
-- assumption.  What remains is G2: a signed bound on the resulting `gramDebt`.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List)

import DASHI.Analysis.FiniteSignedGramTelescopeExact as Gram

record RHPostSchurCell (Scalar : Set) : Set where
  constructor rh-post-schur-cell
  field
    taper0 taper1 taper2 : Scalar

open RHPostSchurCell public

------------------------------------------------------------------------
-- Exact algebra supplied by the RH scalar carrier.
--
-- This is deliberately weaker than choosing a concrete number system.  It is
-- exactly the structure required by the generic finite Gram telescope.
------------------------------------------------------------------------

record RHPostSchurGramStructure : Set₁ where
  constructor rh-post-schur-gram-structure
  field
    Scalar : Set

    zeroScalar : Scalar
    addScalar : Scalar → Scalar → Scalar
    addAssoc : ∀ a b c →
      addScalar (addScalar a b) c ≡ addScalar a (addScalar b c)
    addComm : ∀ a b → addScalar a b ≡ addScalar b a
    addZeroLeft : ∀ a → addScalar zeroScalar a ≡ a

    zeroCell : RHPostSchurCell Scalar
    addCell : RHPostSchurCell Scalar → RHPostSchurCell Scalar → RHPostSchurCell Scalar

    mass : RHPostSchurCell Scalar → Scalar
    signedCrossIncrement :
      RHPostSchurCell Scalar → RHPostSchurCell Scalar → Scalar

    zeroMass : mass zeroCell ≡ zeroScalar
    polarization : ∀ u v →
      mass (addCell u v)
      ≡ addScalar
          (addScalar (mass u) (mass v))
          (signedCrossIncrement u v)

open RHPostSchurGramStructure public

asFiniteGramCarrier : RHPostSchurGramStructure → Gram.FiniteGramCarrier
asFiniteGramCarrier S = record
  { Scalar = Scalar S
  ; Vec = RHPostSchurCell (Scalar S)
  ; zeroScalar = zeroScalar S
  ; addScalar = addScalar S
  ; addAssoc = addAssoc S
  ; addComm = addComm S
  ; addZeroLeft = addZeroLeft S
  ; zeroVec = zeroCell S
  ; addVec = addCell S
  ; mass = mass S
  ; signedCrossIncrement = signedCrossIncrement S
  ; zeroMass = zeroMass S
  ; polarization = polarization S
  }

rhSumCells :
  (S : RHPostSchurGramStructure) →
  List (RHPostSchurCell (Scalar S)) →
  RHPostSchurCell (Scalar S)
rhSumCells S = Gram.sumCells (asFiniteGramCarrier S)

rhDiagonalMass :
  (S : RHPostSchurGramStructure) →
  List (RHPostSchurCell (Scalar S)) → Scalar S
rhDiagonalMass S = Gram.diagonalMass (asFiniteGramCarrier S)

rhGramDebt :
  (S : RHPostSchurGramStructure) →
  List (RHPostSchurCell (Scalar S)) → Scalar S
rhGramDebt S = Gram.gramDebt (asFiniteGramCarrier S)

------------------------------------------------------------------------
-- G1 theorem: once the literal three-coordinate RH carrier supplies its exact
-- polarization law, finite Gram decomposition is inherited mechanically.
------------------------------------------------------------------------

literalRHPostSchurFiniteGramIdentity :
  (S : RHPostSchurGramStructure) →
  (cells : List (RHPostSchurCell (Scalar S))) →
  mass S (rhSumCells S cells)
  ≡ addScalar S (rhDiagonalMass S cells) (rhGramDebt S cells)
literalRHPostSchurFiniteGramIdentity S cells =
  Gram.finiteGramLedger (asFiniteGramCarrier S) cells

record G1Boundary : Set where
  constructor g1-boundary
  field
    literalRHPostSchurCellIsThreeCoordinate : Bool
    literalRHPostSchurCellIsThreeCoordinateIsTrue :
      literalRHPostSchurCellIsThreeCoordinate ≡ true

    rationalNSCarrierRequiredForRH : Bool
    rationalNSCarrierRequiredForRHIsFalse :
      rationalNSCarrierRequiredForRH ≡ false

    genericRound180AlgebraExtracted : Bool
    genericRound180AlgebraExtractedIsTrue :
      genericRound180AlgebraExtracted ≡ true

    literalRHFiniteGramWeldClosed : Bool
    literalRHFiniteGramWeldClosedIsTrue :
      literalRHFiniteGramWeldClosed ≡ true

    finiteGramIdentityAutomaticAfterPolarization : Bool
    finiteGramIdentityAutomaticAfterPolarizationIsTrue :
      finiteGramIdentityAutomaticAfterPolarization ≡ true

    signedRHGramDebtEstimateClosed : Bool
    signedRHGramDebtEstimateClosedIsFalse :
      signedRHGramDebtEstimateClosed ≡ false

canonicalG1Boundary : G1Boundary
canonicalG1Boundary =
  g1-boundary
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
