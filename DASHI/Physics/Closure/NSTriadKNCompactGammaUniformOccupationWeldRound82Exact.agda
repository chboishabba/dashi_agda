module DASHI.Physics.Closure.NSTriadKNCompactGammaUniformOccupationWeldRound82Exact where

------------------------------------------------------------------------
-- ROUND82 / UNIFORM OCCUPATION WELD
--
-- The repository already proves a cutoff/shell/state-uniform compact-Gamma
-- residence theorem once every family member supplies an absorbed-residence
-- input and the endpoint/remainder bound is controlled by one common scalar.
--
-- Round82's deterministic danger-occupation record supplies exactly such a
-- member through `deterministicDangerOccupationAsAbsorbedResidence`.  This file
-- performs that same-object adapter once, so the source-facing C5 theorem no
-- longer needs a second occupation/residence framework.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption as Absorb
import DASHI.Physics.Closure.NSCompactGammaUniformFamilyResidence as Uniform
import DASHI.Physics.Closure.NSTriadKNDeterministicDangerOccupationRound82Exact as Occupation

record DeterministicDangerOccupationFamily
    (A : Absorb.AbsorptionArithmetic)
    (P : Occupation.AbsorptionProductArithmetic A) : Set₁ where
  field
    Cutoff Shell State : Set

    member : Cutoff → Shell → State →
      Occupation.DeterministicDangerOccupationInputs A P

    uniformUpper : Absorb.Scalar A

    memberEndpointRemainderUpper :
      (cutoff : Cutoff) →
      (shell : Shell) →
      (state : State) →
      Absorb._≤_ A
        (Absorb._+_ A
          (Absorb.initialPotential
            (Occupation.absorption (member cutoff shell state)))
          (Absorb.remainderConstant
            (Occupation.absorption (member cutoff shell state))))
        uniformUpper

open DeterministicDangerOccupationFamily public

asUniformCompactGammaResidenceFamily :
  ∀ {A : Absorb.AbsorptionArithmetic}
    {P : Occupation.AbsorptionProductArithmetic A} →
  DeterministicDangerOccupationFamily A P →
  Uniform.CompactGammaCutoffShellFamily A
asUniformCompactGammaResidenceFamily F = record
  { Uniform.Cutoff = Cutoff F
  ; Uniform.Shell = Shell F
  ; Uniform.State = State F
  ; Uniform.member = λ cutoff shell state →
      Occupation.deterministicDangerOccupationAsAbsorbedResidence
        (member F cutoff shell state)
  ; Uniform.uniformUpper = uniformUpper F
  ; Uniform.memberUpperBound = memberEndpointRemainderUpper F
  }

uniformDeterministicDangerOccupationBound :
  ∀ {A : Absorb.AbsorptionArithmetic}
    {P : Occupation.AbsorptionProductArithmetic A} →
  (F : DeterministicDangerOccupationFamily A P) →
  (cutoff : Cutoff F) →
  (shell : Shell F) →
  (state : State F) →
  Absorb._≤_ A
    (Occupation._*_ P
      (Occupation.dangerCost (member F cutoff shell state))
      (Occupation.dangerousResidence (member F cutoff shell state)))
    (uniformUpper F)
uniformDeterministicDangerOccupationBound {A = A} F cutoff shell state =
  Uniform.uniformCompactGammaResidenceBound A
    (asUniformCompactGammaResidenceFamily F) cutoff shell state

round82UniformOccupationUsesExistingResidenceTheorem : Bool
round82UniformOccupationUsesExistingResidenceTheorem = true

round82UniformOccupationUsesExistingResidenceTheoremIsTrue :
  round82UniformOccupationUsesExistingResidenceTheorem ≡ true
round82UniformOccupationUsesExistingResidenceTheoremIsTrue = refl
