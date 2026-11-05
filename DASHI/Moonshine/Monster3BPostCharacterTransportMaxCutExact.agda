module DASHI.Moonshine.Monster3BPostCharacterTransportMaxCutExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Monster3BProofRelevantCurrentMaxCutExact as Prior
import DASHI.Moonshine.Monster3BCommonRepresentationTransportExact as Common
import DASHI.Moonshine.Monster3BSchrodingerLiteralCharacterReceiptExact as Character
import DASHI.Moonshine.Monster3BSchrodingerAdditiveCharacterOrthogonalityExact as Orthogonality

------------------------------------------------------------------------
-- POST-CHARACTER TERMINAL CUT
--
-- Character discovery is no longer the live H_zeta wall.  The literal model
-- action/irreducibility are paid, the complete finite character is exact-
-- executable, and the additive-character cancellation core is source-written.
--
-- The live same-object path is now:
--
--   literal Schrodinger model
--      -> common representation/character theory attachment
--   actual selected W_zeta|E constituent
--      -> SAME theory attachment
--   -> existing fixed-phase character compiler
--   -> actual H_zeta equivariant iso.
--
-- The executable character does not silently become an Agda-kernel trace
-- theorem, and neither degree 729 nor a matching character label constructs the
-- actual Monster constituent.
------------------------------------------------------------------------

record Boundary : Set where
  constructor boundary
  field
    literalActionPaid : Bool
    literalIrreducibilityPaid : Bool
    literalCharacterAllElementsExecuted : Bool
    additiveCharacterOrthogonalitySourceWritten : Bool
    commonTheoryAdapterTyped : Bool
    fixedPhaseIsoCompilerAvailable : Bool

    formalLiteralTraceBridgeInhabited : Bool
    commonRepresentationTheoryInhabited : Bool
    literalModelSameObjectAttachmentInhabited : Bool
    actualConstituentSameObjectAttachmentInhabited : Bool
    actualHZetaEquivariantIsoInhabited : Bool

    characterDiscoveryStillHighestAlpha : Bool
    commonRepresentationTransportIsHighestAlpha : Bool
    nextWall : String
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  (Prior.schrodingerExplicitActionPaid Prior.currentMonster3BMaxCut)
  (Prior.schrodingerIrreducibilityPaid Prior.currentMonster3BMaxCut)
  (Character.all1594323HeisenbergCoordinatesClassified Character.canonicalBoundary)
  (Orthogonality.factorizedAdditiveCharacterOrthogonalityPaid Orthogonality.canonicalBoundary)
  (Common.sameTheoryCompilerTyped Common.canonicalBoundary)
  (Prior.hZetaFixedPhaseIsoCompilerAvailable Prior.currentMonster3BMaxCut)
  (Common.formalLiteralTraceBridgeInhabited Common.canonicalBoundary)
  (Common.commonRepresentationTheoryInhabited Common.canonicalBoundary)
  (Common.literalModelAttachmentInhabited Common.canonicalBoundary)
  (Common.actualConstituentAttachmentInhabited Common.canonicalBoundary)
  (Common.actualHZetaSameObjectInhabited Common.canonicalBoundary)
  false true
  "Instantiate one common finite-group representation/character theory on the literal Schrodinger action and one actual selected W_zeta|E irreducible constituent. Pay the literal trace/character theorem in that theory and the actual constituent same-object/action binding; then consume the existing fixed-phase compiler."
