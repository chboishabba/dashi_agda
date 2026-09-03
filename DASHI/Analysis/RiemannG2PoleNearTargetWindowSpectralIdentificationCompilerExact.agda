module DASHI.Analysis.RiemannG2PoleNearTargetWindowSpectralIdentificationCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannExplicitFormula as Explicit
import DASHI.Analysis.RiemannAristotlePoleNearTargetModulationExact as Target
import DASHI.Analysis.RiemannAristotlePoleNearExplicitFormulaBridgeExact as Window

------------------------------------------------------------------------
-- LITERAL TARGET-WINDOW -> MODULATION SPECTRAL IDENTIFICATION
--
-- The explicit-formula owner already has the theorem-bearing object we need:
--
--   spectralZeroForm f_{t,J}
--     = cluster + (finitePoleNearSigned + farZeroRemainder).
--
-- The newer target-modulation owner asks for the same four scalar channels in
-- ModulationSpectralIdentification.  The only representation payment between
-- them is that the target-window test really is the SAME selected modulated
-- pole test.  Once this equality is supplied, the spectral identification is
-- compiler output; no second cluster/near/far theorem is required.
------------------------------------------------------------------------

record SameLiteralPoleNearWindowAttachment
    {space : Weil.WeilTestSpace}
    {formula : Explicit.RiemannExplicitFormula space}
    (m : Target.PoleNearTargetModulation space)
    (w : Window.PoleNearTargetWindow space formula) : Set where
  constructor same-literal-pole-near-window-attachment
  field
    sameSelectedTest :
      Window.targetWindowTest w ≡ Target.modulatedPoleTest m

    samePoleTaperReceipt : Set
    sameTargetRelativeGapReceipt : Set
    sameMultiplicityReceipt : Set
    sameNearOffFinsetReceipt : Set

    attachmentReference : String

open SameLiteralPoleNearWindowAttachment public

windowToModulationSpectralIdentification :
  ∀ {space formula} →
  (m : Target.PoleNearTargetModulation space) →
  (w : Window.PoleNearTargetWindow space formula) →
  SameLiteralPoleNearWindowAttachment m w →
  Target.ModulationSpectralIdentification space m
windowToModulationSpectralIdentification {space} m w attachment =
  Target.modulation-spectral-identification
    -- selected spectral value
    (Explicit.RiemannExplicitFormula.spectralZeroForm _
      (Window.targetWindowTest w))
    -- same-ordinate cluster
    (Window.sameOrdinateCluster w)
    -- finite signed pole-near response
    (Window.finitePoleNearSigned w)
    -- explicit far-zero remainder
    (Window.farZeroRemainder w)
    -- same scalar addition as the canonical Weil carrier
    (Weil.WeilTestSpace._+S_ space)
    -- theorem already owned by PoleNearTargetWindow
    (Window.spectralWindowDecomposition w)
    -- exact selected spectral form / same-object attachment receipts
    (SameLiteralPoleNearWindowAttachment m w)
    (sameTargetRelativeGapReceipt attachment)
    (sameMultiplicityReceipt attachment)
    (sameNearOffFinsetReceipt attachment)
    (attachmentReference attachment)

------------------------------------------------------------------------
-- Search consequences.
------------------------------------------------------------------------

data SpectralIdentificationSearchAction : Set where
  reproveClusterNearFarDecomposition
  recoverLiteralPoleNearTargetWindow
  proveSameSelectedTargetWindow
  compileModulationSpectralIdentification
  compileHistoricalHW
  : SpectralIdentificationSearchAction

data SearchStatus : Set where
  live pruned downstream : SearchStatus

searchStatus : SpectralIdentificationSearchAction → SearchStatus
searchStatus reproveClusterNearFarDecomposition = pruned
searchStatus recoverLiteralPoleNearTargetWindow = live
searchStatus proveSameSelectedTargetWindow = live
searchStatus compileModulationSpectralIdentification = downstream
searchStatus compileHistoricalHW = downstream

reproveClusterNearFarPruned :
  searchStatus reproveClusterNearFarDecomposition ≡ pruned
reproveClusterNearFarPruned = refl

record PoleNearTargetWindowSpectralIdentificationBoundary : Set where
  constructor pole-near-target-window-spectral-identification-boundary
  field
    explicitFormulaWindowAlreadyOwnsClusterNearFarEquality : Bool
    explicitFormulaWindowAlreadyOwnsClusterNearFarEqualityIsTrue :
      explicitFormulaWindowAlreadyOwnsClusterNearFarEquality ≡ true

    secondSpectralDecompositionTheoremRequired : Bool
    secondSpectralDecompositionTheoremRequiredIsFalse :
      secondSpectralDecompositionTheoremRequired ≡ false

    sameSelectedTargetWindowEqualityRequired : Bool
    sameSelectedTargetWindowEqualityRequiredIsTrue :
      sameSelectedTargetWindowEqualityRequired ≡ true

    modulationSpectralIdentificationCompilerClosedConditionally : Bool
    modulationSpectralIdentificationCompilerClosedConditionallyIsTrue :
      modulationSpectralIdentificationCompilerClosedConditionally ≡ true

    literalTargetWindowRecoveredHere : Bool
    literalTargetWindowRecoveredHereIsFalse :
      literalTargetWindowRecoveredHere ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    highestAlphaReading : String

canonicalPoleNearTargetWindowSpectralIdentificationBoundary :
  PoleNearTargetWindowSpectralIdentificationBoundary
canonicalPoleNearTargetWindowSpectralIdentificationBoundary =
  pole-near-target-window-spectral-identification-boundary
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    "The canonical PoleNearTargetWindow already carries the exact spectralZeroForm = same-ordinate cluster + finite signed near + far-zero remainder theorem. Do not reprove that decomposition merely to populate ModulationSpectralIdentification. Recover the literal selected target-window object, prove that its targetWindowTest is the same modulatedPoleTest chosen by PoleNearTargetModulation, and compile the existing equality and preservation receipts forward. RH is not derived."
