module DASHI.Physics.YangMills.BalabanP33Bridge where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.ProofTargetSurface

import DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility as ADC
import DASHI.Physics.YangMills.GraphCoreLemmaQueue as GraphCore
import DASHI.Physics.YangMills.P01P33ProofSurfaces as Surfaces

p33aSourceSurface : ProofTargetSurface
p33aSourceSurface = Surfaces.p33aUniformLinkEllipticitySurface

p33bInternalSurface : ProofTargetSurface
p33bInternalSurface = Surfaces.p33bWeightedTreeDistanceDominatesOrdinaryDiameterSurface

p33CompositeSurface : ProofTargetSurface
p33CompositeSurface = Surfaces.fieldRegularityImpliesSingleLinkPositivitySurface

record P33Bridge : Set where
  field
    p33aSurface : ProofTargetSurface
    p33aSurfaceIsClosed :
      proofTargetIsClosed p33aSurface ≡ true
    p33aImportedWitness : ADC.ImportedFieldRegularityImpliesSingleLinkPositivity
    p33aUniformLinkEllipticity :
      ∀ (k : ℕ) (X : ADC.Polymer) (e : ADC.Edge) →
      ADC.isEdgeOf e k X → ADC.m-link ≤ℝ ADC.w-weight k e
    p33aMinimumLinkEllipticity : 1ℝ ≤ℝ ADC.m-link
    p33bSurface : ProofTargetSurface
    p33bSurfaceIsClosed :
      proofTargetIsClosed p33bSurface ≡ true
    graphCoreQueue : GraphCore.P33bDiameterDominationBundle
    p33bWeightedDiameterDomination :
      ∀ (k : ℕ) (X : ADC.Polymer) → ADC.diam-ordinary k X ≤ℝ ADC.d-weighted k X
    compositeSurface : ProofTargetSurface
    compositeSurfaceIsClosed :
      proofTargetIsClosed compositeSurface ≡ true
    noClayPromotion : clayYangMillsPromoted ≡ false

currentP33Bridge : P33Bridge
currentP33Bridge = record
  { p33aSurface = p33aSourceSurface
  ; p33aSurfaceIsClosed = refl
  ; p33aImportedWitness = ADC.fieldRegularityImpliesSingleLinkPositivityWitness
  ; p33aUniformLinkEllipticity =
      ADC.ImportedFieldRegularityImpliesSingleLinkPositivity.linkEllipticity
        ADC.fieldRegularityImpliesSingleLinkPositivityWitness
  ; p33aMinimumLinkEllipticity =
      ADC.ImportedFieldRegularityImpliesSingleLinkPositivity.linkEllipticityMin
        ADC.fieldRegularityImpliesSingleLinkPositivityWitness
  ; p33bSurface = p33bInternalSurface
  ; p33bSurfaceIsClosed = refl
  ; graphCoreQueue = GraphCore.currentP33bDiameterDominationBundle
  ; p33bWeightedDiameterDomination =
      GraphCore.P33bDiameterDominationBundle.diameterDomination
        GraphCore.currentP33bDiameterDominationBundle
  ; compositeSurface = p33CompositeSurface
  ; compositeSurfaceIsClosed = refl
  ; noClayPromotion = refl
  }
