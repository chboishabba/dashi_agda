module DASHI.Analysis.NonArchimedeanTwistedSpatialPowerCompilerExact where

------------------------------------------------------------------------
-- GENERIC COMPILER IS NOW CLOSED BY EXISTING DASHI MACHINERY
--
-- Once a concrete twisted-block / character rechart is supplied, together
-- with the character-space power identity already produced by the monomial
-- orbit machinery, the literal spatial scalar-power identity is compiler
-- output.  No additional matrix-power theorem is required.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Analysis.NonArchimedeanSpatialCharacterIntertwinerReuseExact as Rechart

record TwistedSpatialPowerInputs : Set₁ where
  field
    rechart : Rechart.SpatialCharacterRechart
    exponent : Nat
    scalar : Rechart.Scalar rechart

    characterPower :
      (state : Rechart.Character rechart) →
      Rechart.iterate exponent
        (Rechart.characterStep rechart)
        state
      ≡ Rechart.scaleCharacter rechart scalar state

    concreteGroupLabellingReceipt : Set
    concretePeriodReceipt : Set
    concreteOrbitWeightReceipt : Set

open TwistedSpatialPowerInputs public

compileSpatialPower :
  (inputs : TwistedSpatialPowerInputs) →
  (state : Rechart.Spatial (rechart inputs)) →
  Rechart.iterate
    (exponent inputs)
    (Rechart.spatialStep (rechart inputs))
    state
  ≡ Rechart.scaleSpatial
      (rechart inputs)
      (scalar inputs)
      state
compileSpatialPower inputs =
  Rechart.characterScalarPowerToSpatialScalarPower
    (rechart inputs)
    (exponent inputs)
    (scalar inputs)
    (characterPower inputs)

------------------------------------------------------------------------
-- Reverse acquisition surface.  The compiler itself is no longer a search
-- target; only the concrete source-specific attachments are.
------------------------------------------------------------------------

data CompilerInputObligation : Set where
  concreteTwistedCharacterRechart : CompilerInputObligation
  concreteGroupLabelling : CompilerInputObligation
  concreteScalarActionCompatibility : CompilerInputObligation
  concretePeriodAttachment : CompilerInputObligation
  concreteOrbitWeightAttachment : CompilerInputObligation
  characterPowerTheoremAttachment : CompilerInputObligation

compilerInputCutset : List CompilerInputObligation
compilerInputCutset =
  concreteTwistedCharacterRechart ∷
  concreteGroupLabelling ∷
  concreteScalarActionCompatibility ∷
  concretePeriodAttachment ∷
  concreteOrbitWeightAttachment ∷
  characterPowerTheoremAttachment ∷
  []

record TwistedSpatialPowerCompilerBoundary : Set where
  constructor twistedSpatialPowerCompilerBoundary
  field
    newMatrixPowerProofRequired : Bool
    newGenericIntertwinerProofRequired : Bool
    sourceSpecificRechartRequired : Bool
    sourceSpecificGroupLabellingRequired : Bool
    sourceSpecificScalarCompatibilityRequired : Bool
    spatialPowerIsCompilerOutputAfterInputs : Bool

canonicalTwistedSpatialPowerCompilerBoundary :
  TwistedSpatialPowerCompilerBoundary
canonicalTwistedSpatialPowerCompilerBoundary =
  twistedSpatialPowerCompilerBoundary
    false
    false
    true
    true
    true
    true
