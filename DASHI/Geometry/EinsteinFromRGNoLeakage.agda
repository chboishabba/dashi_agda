module DASHI.Geometry.EinsteinFromRGNoLeakage where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

record RGGeometryData : Set₁ where
  field
    M : Set
    Point : Set
    Tensor2 : Set
    ℚ : Set
    0q : ℚ
    div : Tensor2 → Point → ℚ
    sym : Tensor2 → Set
    G : M → Tensor2
    T : M → Tensor2
    RGState : Set
    step : RGState → RGState
    geom : RGState → M
    Pτ : Tensor2 → Tensor2

open RGGeometryData public

DefectD : (D : RGGeometryData) → RGGeometryData.RGState D → RGGeometryData.Tensor2 D
DefectD D s = RGGeometryData.Pτ D (RGGeometryData.T D (RGGeometryData.geom D (RGGeometryData.step D s)))

record GR_NoLeakage (D : RGGeometryData) : Set₁ where
  field
    bianchi :
      ∀ s x →
        RGGeometryData.div D (RGGeometryData.G D (RGGeometryData.geom D s)) x ≡ RGGeometryData.0q D
    conserve :
      ∀ s x →
        RGGeometryData.div D (RGGeometryData.T D (RGGeometryData.geom D s)) x ≡ RGGeometryData.0q D
    defect-law :
      ∀ s →
        RGGeometryData.G D (RGGeometryData.geom D s) ≡ DefectD D s
    symG :
      ∀ s →
        RGGeometryData.sym D (RGGeometryData.G D (RGGeometryData.geom D s))
    symT :
      ∀ s →
        RGGeometryData.sym D (RGGeometryData.T D (RGGeometryData.geom D s))

open GR_NoLeakage public

record EinsteinConsequences {D} (A : GR_NoLeakage D) : Set₁ where
  field
    divergenceFree :
      ∀ s x →
        RGGeometryData.div D (RGGeometryData.G D (RGGeometryData.geom D s)) x ≡ RGGeometryData.0q D
    conservation :
      ∀ s x →
        RGGeometryData.div D (RGGeometryData.T D (RGGeometryData.geom D s)) x ≡ RGGeometryData.0q D
    einsteinEq :
      ∀ s →
        RGGeometryData.G D (RGGeometryData.geom D s) ≡ DefectD D s

EinsteinFromRG :
  ∀ {D} (A : GR_NoLeakage D) →
  EinsteinConsequences A
EinsteinFromRG A =
  record
    { divergenceFree = bianchi A
    ; conservation = conserve A
    ; einsteinEq = defect-law A
    }
