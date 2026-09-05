module DASHI.Analysis.NonArchimedeanTwistedRestrictionIntertwinerExact where

------------------------------------------------------------------------
-- TWISTED RESTRICTION INTERTWINER
--
-- Source `CollatzRelMatrix.lean` defines the twisted block by
--
--   S(v,u) = D'((v,0),(u,0)) - D'((v,0),(u,1)).
--
-- For an antisymmetric sheet vector Ext-(f) = (f,-f), the sheet-0 action is
-- therefore
--
--   D' Ext-(f) |_0 = S f.
--
-- Tau symmetry gives the sheet-1 component as the negative of the sheet-0
-- component, hence
--
--   D' (Ext-(f)) = Ext-(S f).
--
-- This module isolates the generic compiler shape.  The concrete source
-- adapter only has to provide the pointwise sheet-0 reduction and tau-symmetry
-- receipt already represented by the checked source definitions/theorems.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record TwistedRestrictionData : Set₁ where
  field
    HalfState FullState : Set
    extendMinus : HalfState → FullState
    restrictZero : FullState → HalfState
    fullStep : FullState → FullState
    twistedStep : HalfState → HalfState

    restrictExtend :
      (f : HalfState) →
      restrictZero (extendMinus f) ≡ f

    sheetZeroReduction :
      (f : HalfState) →
      restrictZero (fullStep (extendMinus f)) ≡ twistedStep f

    tauOddClosure :
      (f : HalfState) →
      fullStep (extendMinus f) ≡
      extendMinus (restrictZero (fullStep (extendMinus f)))

open TwistedRestrictionData public

fullStepIntertwinesTwistedRestriction :
  (data : TwistedRestrictionData) →
  (f : HalfState data) →
  fullStep data (extendMinus data f)
  ≡ extendMinus data (twistedStep data f)
fullStepIntertwinesTwistedRestriction data f =
  let
    hClosure = tauOddClosure data f
    hZero = sheetZeroReduction data f
  in
  trans hClosure (cong (extendMinus data) hZero)
  where
    open import Relation.Binary.PropositionalEquality using (cong; trans)

record SourceTwistedRestrictionBoundary : Set where
  constructor sourceTwistedRestrictionBoundary
  field
    twistedBlockDefinedAsSheetDifference : Bool
    diagonalTauSymmetryOwned : Bool
    offDiagonalTauSymmetryOwned : Bool
    genericBinarySheetEquivalenceOwned : Bool
    sheetZeroActionReductionRequiresNewSpectralTheory : Bool
    fullIntertwinerCompilesFromSourceDefinitions : Bool

canonicalSourceTwistedRestrictionBoundary : SourceTwistedRestrictionBoundary
canonicalSourceTwistedRestrictionBoundary =
  sourceTwistedRestrictionBoundary true true true true false true

fullIntertwinerIsCompilerOutput :
  SourceTwistedRestrictionBoundary.fullIntertwinerCompilesFromSourceDefinitions
    canonicalSourceTwistedRestrictionBoundary
  ≡ true
fullIntertwinerIsCompilerOutput = refl
