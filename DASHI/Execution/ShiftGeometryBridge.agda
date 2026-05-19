module DASHI.Execution.ShiftGeometryBridge where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ)
open import Data.Vec using (Vec)

open import DASHI.Execution.Contract as Exec
open import DASHI.Geometry.Signature.HyperbolicFormZ as HFZ
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.Signature31InstanceShiftZ as S31Z

private
  variable
    ℓx ℓs ℓδ ℓπ ℓe : Level

record DeltaToShiftGeometry
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  (C : Exec.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe})
  : Set (lsuc (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe)) where
  field
    embedΔ : Exec.Contract.ΔSource C → Vec ℤ S31Z.m
    embedSource : Exec.Contract.Source C → Vec ℤ S31Z.m
    deltaArrow : Exec.Contract.ΔSource C → ℤ
    sourceArrow : Exec.Contract.Source C → ℤ
    deltaShape : Exec.Contract.ΔSource C → Vec ℤ (suc (suc (suc zero)))
    sourceShape : Exec.Contract.Source C → Vec ℤ (suc (suc (suc zero)))

    deltaArrow≡tau :
      ∀ δ →
      deltaArrow δ ≡ HFZ.tau (S31Z.toCounts (embedΔ δ))

    sourceArrow≡tau :
      ∀ s →
      sourceArrow s ≡ HFZ.tau (S31Z.toCounts (embedSource s))

    deltaShape≡sigma :
      ∀ δ →
      deltaShape δ ≡ HFZ.sigma (S31Z.toCounts (embedΔ δ))

    sourceShape≡sigma :
      ∀ s →
      sourceShape s ≡ HFZ.sigma (S31Z.toCounts (embedSource s))

open DeltaToShiftGeometry public

execDeltaVec4 :
  ∀ {ℓx ℓs ℓδ ℓπ ℓe}
  {C : Exec.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}} →
  DeltaToShiftGeometry C →
  Exec.Contract.State C →
  Vec ℤ S31Z.m
execDeltaVec4 {C = C} bridge x =
  DeltaToShiftGeometry.embedΔ bridge
    (Exec.Contract.projectΔ C (Exec.Contract.Δ C x))

execSourceVec4 :
  ∀ {ℓx ℓs ℓδ ℓπ ℓe}
  {C : Exec.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}} →
  DeltaToShiftGeometry C →
  Exec.Contract.State C →
  Vec ℤ S31Z.m
execSourceVec4 {C = C} bridge x =
  DeltaToShiftGeometry.embedSource bridge
    (Exec.Contract.π C x)

execDeltaArrow :
  ∀ {ℓx ℓs ℓδ ℓπ ℓe}
  {C : Exec.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}} →
  DeltaToShiftGeometry C →
  Exec.Contract.State C →
  ℤ
execDeltaArrow {C = C} bridge x =
  DeltaToShiftGeometry.deltaArrow bridge
    (Exec.Contract.projectΔ C (Exec.Contract.Δ C x))

execSourceArrow :
  ∀ {ℓx ℓs ℓδ ℓπ ℓe}
  {C : Exec.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}} →
  DeltaToShiftGeometry C →
  Exec.Contract.State C →
  ℤ
execSourceArrow {C = C} bridge x =
  DeltaToShiftGeometry.sourceArrow bridge
    (Exec.Contract.π C x)

mkTernaryVec4Bridge :
  ∀ {ℓx ℓs ℓδ ℓπ ℓe}
  {C : Exec.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}} →
  (δ4 : Exec.Contract.ΔSource C → RTC.Carrier S31Z.m) →
  (s4 : Exec.Contract.Source C → RTC.Carrier S31Z.m) →
  DeltaToShiftGeometry C
mkTernaryVec4Bridge δ4 s4 =
  record
    { embedΔ = λ δ → QP.vecℤ (δ4 δ)
    ; embedSource = λ s → QP.vecℤ (s4 s)
    ; deltaArrow = λ δ → HFZ.tau (S31Z.toCounts (QP.vecℤ (δ4 δ)))
    ; sourceArrow = λ s → HFZ.tau (S31Z.toCounts (QP.vecℤ (s4 s)))
    ; deltaShape = λ δ → HFZ.sigma (S31Z.toCounts (QP.vecℤ (δ4 δ)))
    ; sourceShape = λ s → HFZ.sigma (S31Z.toCounts (QP.vecℤ (s4 s)))
    ; deltaArrow≡tau = λ _ → refl
    ; sourceArrow≡tau = λ _ → refl
    ; deltaShape≡sigma = λ _ → refl
    ; sourceShape≡sigma = λ _ → refl
    }
