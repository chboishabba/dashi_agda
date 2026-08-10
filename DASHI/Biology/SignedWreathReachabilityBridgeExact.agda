module DASHI.Biology.SignedWreathReachabilityBridgeExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Integrate three Round-8 layers into one executable proof pattern:
--
--   signed multiplicity defect
--          -> three-way sign/orientation shadow
--          -> FRACTRAN-controlled finite wreath step
--          -> finite-step reachability obstruction.
--
-- A spectral update must explicitly prove that it preserves the signed defect.
-- Once that proof is supplied, both the integer defect and its ternary sign are
-- invariants of every finite controlled path.  Endpoints with different defect
-- (or already different sign) are therefore unreachable under that transition
-- system.  This is a generic invariant theorem, not a permanent/determinant,
-- Monster, or P-vs-NP lower bound.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer.Base using (ℤ)

import DASHI.Biology.SignedMultiplicityObstructionExact as Defect
import DASHI.Biology.FRACTRANWreathControlledSymmetryExact as Controlled
import DASHI.Biology.SpectralReachabilityComplexityExact as Reach

record SpectralControlledState (I : Set) : Set where
  constructor spectralControlledState
  field
    leftSpectrum : Defect.Multiplicity I
    rightSpectrum : Defect.Multiplicity I
    controlState : Controlled.ControlledState

open SpectralControlledState public

defectAt :
  ∀ {I} → I → SpectralControlledState I → ℤ
defectAt i state =
  Defect.delta (leftSpectrum state) (rightSpectrum state) i

orientationAt :
  ∀ {I} → I → SpectralControlledState I → Defect.DefectOrientation
orientationAt i state = Defect.orientationOfInteger (defectAt i state)

------------------------------------------------------------------------
-- An allowed spectral update carries the proof obligation that its quantitative
-- multiplicity difference is preserved coordinatewise.
------------------------------------------------------------------------

record DefectPreservingUpdate (I : Set) : Set₁ where
  constructor defectPreservingUpdate
  field
    updateLeft : Defect.Multiplicity I → Defect.Multiplicity I
    updateRight : Defect.Multiplicity I → Defect.Multiplicity I
    defectPreserved :
      (A B : Defect.Multiplicity I) (i : I) →
      Defect.delta (updateLeft A) (updateRight B) i
      ≡ Defect.delta A B i

open DefectPreservingUpdate public

identityDefectPreservingUpdate :
  ∀ {I} → DefectPreservingUpdate I
identityDefectPreservingUpdate =
  defectPreservingUpdate (λ A → A) (λ B → B) (λ A B i → refl)

controlledSpectralStep :
  ∀ {I} → DefectPreservingUpdate I →
  SpectralControlledState I → SpectralControlledState I
controlledSpectralStep update state =
  spectralControlledState
    (updateLeft update (leftSpectrum state))
    (updateRight update (rightSpectrum state))
    (Controlled.controlledStep (controlState state))

data Step {I : Set} (update : DefectPreservingUpdate I) :
  SpectralControlledState I → SpectralControlledState I → Set where
  controlledSpectralStepWitness :
    (state : SpectralControlledState I) →
    Step update state (controlledSpectralStep update state)

------------------------------------------------------------------------
-- Fine signed invariant and its ternary coarse shadow.
------------------------------------------------------------------------

defectInvariant :
  ∀ {I} (update : DefectPreservingUpdate I) (i : I) →
  Reach.StepInvariant (Step update) ℤ
defectInvariant update i =
  Reach.stepInvariant
    (defectAt i)
    (λ where
      (controlledSpectralStepWitness state) →
        defectPreserved update
          (leftSpectrum state)
          (rightSpectrum state)
          i)

orientationInvariant :
  ∀ {I} (update : DefectPreservingUpdate I) (i : I) →
  Reach.StepInvariant (Step update) Defect.DefectOrientation
orientationInvariant update i =
  Reach.stepInvariant
    (orientationAt i)
    (λ where
      (controlledSpectralStepWitness state) →
        cong Defect.orientationOfInteger
          (defectPreserved update
            (leftSpectrum state)
            (rightSpectrum state)
            i))

defectPreservedAlongReach :
  ∀ {I} (update : DefectPreservingUpdate I) (i : I)
    {n x y} → Reach.ReachIn (Step update) n x y →
  defectAt i x ≡ defectAt i y
defectPreservedAlongReach update i =
  Reach.reachPreservesInvariant (defectInvariant update i)

orientationPreservedAlongReach :
  ∀ {I} (update : DefectPreservingUpdate I) (i : I)
    {n x y} → Reach.ReachIn (Step update) n x y →
  orientationAt i x ≡ orientationAt i y
orientationPreservedAlongReach update i =
  Reach.reachPreservesInvariant (orientationInvariant update i)

signedDefectSeparatesNoReach :
  ∀ {I} (update : DefectPreservingUpdate I) (i : I)
    {n x y} →
  ¬ (defectAt i x ≡ defectAt i y) →
  ¬ Reach.ReachIn (Step update) n x y
signedDefectSeparatesNoReach update i =
  Reach.invariantSeparatesNoReach (defectInvariant update i)

orientationSeparatesNoReach :
  ∀ {I} (update : DefectPreservingUpdate I) (i : I)
    {n x y} →
  ¬ (orientationAt i x ≡ orientationAt i y) →
  ¬ Reach.ReachIn (Step update) n x y
orientationSeparatesNoReach update i =
  Reach.invariantSeparatesNoReach (orientationInvariant update i)

------------------------------------------------------------------------
-- The sign quotient is explicitly a coarse shadow: integer preservation
-- implies orientation preservation by congruence.  The converse is not claimed;
-- many nonzero multiplicity defects can share the same orientation.
------------------------------------------------------------------------

record SignedWreathReachabilityClaimScope : Set where
  constructor signedWreathReachabilityClaimScope
  field
    signedDefectReachabilityObstructionConstructed : Bool
    signedDefectReachabilityObstructionConstructedIsTrue :
      signedDefectReachabilityObstructionConstructed ≡ true

    ternaryOrientationObstructionConstructed : Bool
    ternaryOrientationObstructionConstructedIsTrue :
      ternaryOrientationObstructionConstructed ≡ true

    signShadowDeterminesFullMultiplicityDifference : Bool
    signShadowDeterminesFullMultiplicityDifferenceIsFalse :
      signShadowDeterminesFullMultiplicityDifference ≡ false

    gctLowerBoundConstructed : Bool
    gctLowerBoundConstructedIsFalse : gctLowerBoundConstructed ≡ false

    pVersusNPResolved : Bool
    pVersusNPResolvedIsFalse : pVersusNPResolved ≡ false

canonicalSignedWreathReachabilityClaimScope :
  SignedWreathReachabilityClaimScope
canonicalSignedWreathReachabilityClaimScope =
  signedWreathReachabilityClaimScope
    true refl
    true refl
    false refl
    false refl
    false refl
