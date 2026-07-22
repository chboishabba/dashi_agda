module DASHI.Cognition.VisualPatternGeneratorMDL where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Vec using (Vec; []; _∷_)

import Base369 as Base
import DASHI.Biology.ObserverPerceptualManifoldResidual as Observer
import DASHI.Biology.RetinalPerturbationObservationBridge as Retinal
import DASHI.Combinatorics.PDA_MDL.Prelude as MDL

data VisualGenerator : Set where
  orientationWave : VisualGenerator
  lattice : VisualGenerator
  checker : VisualGenerator
  spiral : VisualGenerator
  tunnel : VisualGenerator
  cobweb : VisualGenerator
  semanticScene : VisualGenerator

Grid9 : Set
Grid9 = Vec Base.TriTruth 9

render : VisualGenerator → Grid9
render orientationWave =
  Base.tri-low ∷ Base.tri-mid ∷ Base.tri-high ∷
  Base.tri-low ∷ Base.tri-mid ∷ Base.tri-high ∷
  Base.tri-low ∷ Base.tri-mid ∷ Base.tri-high ∷ []
render lattice =
  Base.tri-high ∷ Base.tri-low ∷ Base.tri-high ∷
  Base.tri-low ∷ Base.tri-high ∷ Base.tri-low ∷
  Base.tri-high ∷ Base.tri-low ∷ Base.tri-high ∷ []
render checker =
  Base.tri-low ∷ Base.tri-high ∷ Base.tri-low ∷
  Base.tri-high ∷ Base.tri-low ∷ Base.tri-high ∷
  Base.tri-low ∷ Base.tri-high ∷ Base.tri-low ∷ []
render spiral =
  Base.tri-high ∷ Base.tri-high ∷ Base.tri-high ∷
  Base.tri-low ∷ Base.tri-mid ∷ Base.tri-high ∷
  Base.tri-low ∷ Base.tri-low ∷ Base.tri-high ∷ []
render tunnel =
  Base.tri-high ∷ Base.tri-high ∷ Base.tri-high ∷
  Base.tri-high ∷ Base.tri-low ∷ Base.tri-high ∷
  Base.tri-high ∷ Base.tri-high ∷ Base.tri-high ∷ []
render cobweb =
  Base.tri-high ∷ Base.tri-low ∷ Base.tri-high ∷
  Base.tri-low ∷ Base.tri-mid ∷ Base.tri-low ∷
  Base.tri-high ∷ Base.tri-low ∷ Base.tri-high ∷ []
render semanticScene =
  Base.tri-low ∷ Base.tri-mid ∷ Base.tri-high ∷
  Base.tri-high ∷ Base.tri-low ∷ Base.tri-mid ∷
  Base.tri-mid ∷ Base.tri-high ∷ Base.tri-low ∷ []

formConstant : VisualGenerator → Retinal.FormConstantGeometry
formConstant orientationWave = Retinal.directionalAxis
formConstant lattice = Retinal.latticeField
formConstant checker = Retinal.latticeField
formConstant spiral = Retinal.spiralField
formConstant tunnel = Retinal.tunnelField
formConstant cobweb = Retinal.cobwebField
formConstant semanticScene = Retinal.diffuseConfidenceField

generatorCode : VisualGenerator → MDL.CodeLength
generatorCode orientationWave = 2
generatorCode lattice = 3
generatorCode checker = 3
generatorCode spiral = 4
generatorCode tunnel = 4
generatorCode cobweb = 4
generatorCode semanticScene = 9

semanticBindingCode : VisualGenerator → MDL.CodeLength
semanticBindingCode semanticScene = 6
semanticBindingCode _ = 0

visualMDL : VisualGenerator → MDL.CodeLength → MDL.CodeLength
visualMDL generator fitCost =
  generatorCode generator + semanticBindingCode generator + fitCost

record GeometricAttractorWitness (generator : VisualGenerator) : Set where
  field
    belowSpiral : visualMDL generator 0 ≤ visualMDL spiral 0
    belowTunnel : visualMDL generator 0 ≤ visualMDL tunnel 0
    belowCobweb : visualMDL generator 0 ≤ visualMDL cobweb 0
    belowSemanticScene : visualMDL generator 0 ≤ visualMDL semanticScene 0

latticeAttractorWitness : GeometricAttractorWitness lattice
latticeAttractorWitness = record
  { belowSpiral = s≤s (s≤s (s≤s z≤n))
  ; belowTunnel = s≤s (s≤s (s≤s z≤n))
  ; belowCobweb = s≤s (s≤s (s≤s z≤n))
  ; belowSemanticScene = s≤s (s≤s (s≤s z≤n))
  }

orientationIsCheaperThanLattice :
  visualMDL orientationWave 0 ≤ visualMDL lattice 0
orientationIsCheaperThanLattice = s≤s (s≤s z≤n)

latticeIsCheaperThanSemanticBinding :
  visualMDL lattice 0 ≤ visualMDL semanticScene 0
latticeIsCheaperThanSemanticBinding = s≤s (s≤s (s≤s z≤n))

mapGrid :
  ∀ {n} →
  (Base.TriTruth → Base.TriTruth) →
  Vec Base.TriTruth n →
  Vec Base.TriTruth n
mapGrid f [] = []
mapGrid f (x ∷ xs) = f x ∷ mapGrid f xs

rotateRendered : VisualGenerator → Grid9
rotateRendered generator = mapGrid Base.rotateTri (render generator)

rotateRenderedThreeTimes :
  (generator : VisualGenerator) →
  mapGrid Base.rotateTri
    (mapGrid Base.rotateTri
      (mapGrid Base.rotateTri (render generator)))
  ≡ render generator
rotateRenderedThreeTimes orientationWave = refl
rotateRenderedThreeTimes lattice = refl
rotateRenderedThreeTimes checker = refl
rotateRenderedThreeTimes spiral = refl
rotateRenderedThreeTimes tunnel = refl
rotateRenderedThreeTimes cobweb = refl
rotateRenderedThreeTimes semanticScene = refl

humanGeneratorFibre : Observer.PerceptualFibre
humanGeneratorFibre = Observer.fibreFor Observer.humanObserver

humanGeneratorFibreIsVisual :
  humanGeneratorFibre ≡ Observer.humanVisionLanguageFibre
humanGeneratorFibreIsVisual = refl
