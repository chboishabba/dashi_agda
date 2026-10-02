module DASHI.ComputerScience.TekumFieldRoleSSPAtlasExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Algebra.Trit as Trit
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.ComputerScience.TekumSSPFRACTRANBridgeExact as Bridge

------------------------------------------------------------------------
-- A concrete way to attach *field semantics* to SSP15 without asserting that
-- the fields are intrinsically Monster/Ogg objects.  Lane assignment is an
-- explicit atlas parameter and therefore inspectable/replacable.

data TekumFieldRole : Set where
  regimeRole : TekumFieldRole
  exponentRole : TekumFieldRole
  fractionRole : TekumFieldRole

record TekumFieldSSPAtlas : Set where
  constructor tekumFieldSSPAtlas
  field
    regimeLane : Signed.SSPPrime
    exponentLane : Signed.SSPPrime
    fractionLane : Signed.SSPPrime
open TekumFieldSSPAtlas public

canonicalRadixThreeAtlas : TekumFieldSSPAtlas
canonicalRadixThreeAtlas =
  tekumFieldSSPAtlas Signed.ssp3 Signed.ssp3 Signed.ssp3

separatedRoleAtlas : TekumFieldSSPAtlas
separatedRoleAtlas =
  tekumFieldSSPAtlas Signed.ssp3 Signed.ssp5 Signed.ssp7

laneFor : TekumFieldSSPAtlas → TekumFieldRole → Signed.SSPPrime
laneFor atlas regimeRole = regimeLane atlas
laneFor atlas exponentRole = exponentLane atlas
laneFor atlas fractionRole = fractionLane atlas

record FieldDigit : Set where
  constructor fieldDigit
  field
    role : TekumFieldRole
    position : Nat
    digit : Trit.Trit
open FieldDigit public

compileFieldDigit :
  TekumFieldSSPAtlas → FieldDigit → List Signed.WeaveInstruction
compileFieldDigit atlas (fieldDigit role k t) =
  Bridge.compilePositionedOn
    (laneFor atlas role)
    (Bridge.positionedTrit k t)

canonicalRegimePositiveUnit :
  compileFieldDigit canonicalRadixThreeAtlas
    (fieldDigit regimeRole 0 Trit.pos)
  ≡ Signed.introducePrime Signed.ssp3 ∷ []
canonicalRegimePositiveUnit = refl

separatedExponentPositiveUnit :
  compileFieldDigit separatedRoleAtlas
    (fieldDigit exponentRole 0 Trit.pos)
  ≡ Signed.introducePrime Signed.ssp5 ∷ []
separatedExponentPositiveUnit = refl

record FieldAtlasBoundary : Set where
  constructor fieldAtlasBoundary
  field
    allTekumFieldsCanUseOneRadixThreeLane : Bool
    rolesCanInsteadBeSeparatedAcrossSSP15Lanes : Bool
    laneAssignmentIsExplicitRepresentationSemantics : Bool

canonicalFieldAtlasBoundary : FieldAtlasBoundary
canonicalFieldAtlasBoundary =
  fieldAtlasBoundary true true true
