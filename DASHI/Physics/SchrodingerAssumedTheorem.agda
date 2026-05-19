module DASHI.Physics.SchrodingerAssumedTheorem where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.SchrodingerGap as SG

------------------------------------------------------------------------
-- Assumption-guarded theorem surface over the concrete `SchrodingerGap`.
--
-- This module does not derive Schrödinger form. It only repackages a
-- supplied `schrodingerForm` witness already present in the gap surface.

record SchrodingerAssumedTheorem
  {ℓs ℓp ℓo ℓq ℓr : Level}
  {V : Set}
  (gap : SG.SchrodingerGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V)
  : Setω where
  field
    theoremLabel : String

    suppliedSchrodingerForm :
      SG.SchrodingerGap.schrodingerForm gap

    theoremConclusion :
      SG.SchrodingerGap.schrodingerForm gap

    usesOnlySuppliedWitness :
      theoremConclusion ≡ suppliedSchrodingerForm

    theoremBoundary : List String

open SchrodingerAssumedTheorem public

assumedTheoremFromGap :
  {ℓs ℓp ℓo ℓq ℓr : Level}
  {V : Set}
  (gap : SG.SchrodingerGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  SG.SchrodingerGap.schrodingerForm gap →
  SchrodingerAssumedTheorem gap
assumedTheoremFromGap gap suppliedWitness =
  record
    { theoremLabel = "schrodinger-assumed-theorem"
    ; suppliedSchrodingerForm = suppliedWitness
    ; theoremConclusion = suppliedWitness
    ; usesOnlySuppliedWitness = refl
    ; theoremBoundary =
        "Assumption-guarded theorem surface only"
        ∷ "Consumes a supplied schrodingerForm witness from SchrodingerGap"
        ∷ "No unconditional Schrodinger proof claim is made"
        ∷ SG.SchrodingerGap.nonClaimBoundary gap
    }

assumedTheoremInterfaceLabel :
  {ℓs ℓp ℓo ℓq ℓr : Level}
  {V : Set}
  {gap : SG.SchrodingerGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V} →
  SchrodingerAssumedTheorem gap →
  String
assumedTheoremInterfaceLabel {gap = gap} _ =
  SG.gapInterfaceLabel gap

assumedTheoremUsesGapWitness :
  {ℓs ℓp ℓo ℓq ℓr : Level}
  {V : Set}
  {gap : SG.SchrodingerGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V}
  (theorem : SchrodingerAssumedTheorem gap) →
  SchrodingerAssumedTheorem.theoremConclusion theorem
  ≡
  SchrodingerAssumedTheorem.suppliedSchrodingerForm theorem
assumedTheoremUsesGapWitness theorem =
  SchrodingerAssumedTheorem.usesOnlySuppliedWitness theorem
