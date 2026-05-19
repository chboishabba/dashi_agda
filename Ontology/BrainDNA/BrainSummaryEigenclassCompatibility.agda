module Ontology.BrainDNA.BrainSummaryEigenclassCompatibility where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Vec using (Vec; []; _∷_)

open import Ontology.Brain.BrainVocabularySurface using (BrainState)
open import Ontology.BrainDNA.BrainSummaryPacketCompatibility as Summary using
  (BrainSummaryPacketView; BrainSummaryPacketCompatibilitySurface;
   brainSummaryPacketCompatibilitySurface; summaryStatePacketView)
open import Ontology.DNA.Supervoxel4Adic using (Base; A; C; G; T)
open import Ontology.DNA.EigenclassSurface as ES using
  (DNA3; DNA6x3; EigenClass3; MacroAdjacencySurface;
   ScanOrder; lineMajor; classify3; macroSurface)

------------------------------------------------------------------------
-- Summary-to-eigenclass compatibility surface.
--
-- This is intentionally theorem-thin and representative-only. The local
-- brain coarse summary does not determine the full DNA payload, so this
-- module does not claim payload recovery. Instead it defines a canonical
-- representative line/bundle derived from the existing summary packet view
-- and proves a few exact summary-boundary compatibilities into the local
-- DNA eigenclass and macro-adjacency surfaces.

summaryRepresentativeBase : Bool → Base
summaryRepresentativeBase true = G
summaryRepresentativeBase false = T

summaryRepresentative3 : Summary.BrainSummaryPacketView → DNA3
summaryRepresentative3 view =
  A ∷ C ∷ summaryRepresentativeBase (Summary.BrainSummaryPacketView.activeFlag view) ∷ []

summaryRepresentativeEigen : Summary.BrainSummaryPacketView → EigenClass3
summaryRepresentativeEigen view = classify3 (summaryRepresentative3 view)

summaryRepresentative6x3 : Summary.BrainSummaryPacketView → DNA6x3
summaryRepresentative6x3 view =
  let line = summaryRepresentative3 view in
  line ∷ line ∷ line ∷ line ∷ line ∷ line ∷ []

summaryRepresentativeMacro : Summary.BrainSummaryPacketView → MacroAdjacencySurface
summaryRepresentativeMacro view = macroSurface (summaryRepresentative6x3 view)

summaryRepresentativeOrder-compatible :
  ∀ {n} (st : BrainState n) →
  ES.MacroAdjacencySurface.scanOrder
    (summaryRepresentativeMacro (summaryStatePacketView st))
    ≡
  Summary.BrainSummaryPacketView.order (summaryStatePacketView st)
summaryRepresentativeOrder-compatible st = refl

summaryRepresentativeLineAdmissible-true :
  ∀ {n} (st : BrainState n) →
  ES.EigenClass3.lineAdmissible
    (summaryRepresentativeEigen (summaryStatePacketView st))
    ≡ true
summaryRepresentativeLineAdmissible-true st
  with Summary.BrainSummaryPacketView.activeFlag (summaryStatePacketView st)
... | true = refl
... | false = refl

summaryRepresentativeCoupledAdjacency-true :
  ∀ {n} (st : BrainState n) →
  ES.MacroAdjacencySurface.coupledAdjacency
    (summaryRepresentativeMacro (summaryStatePacketView st))
    ≡ true
summaryRepresentativeCoupledAdjacency-true st = refl

summaryRepresentativeAdjacencyScore-zero :
  ∀ {n} (st : BrainState n) →
  ES.MacroAdjacencySurface.adjacencyScore
    (summaryRepresentativeMacro (summaryStatePacketView st))
    ≡ zero
summaryRepresentativeAdjacencyScore-zero st
  with Summary.BrainSummaryPacketView.activeFlag (summaryStatePacketView st)
... | true = refl
... | false = refl

record BrainSummaryEigenclassCompatibilitySurface : Set₂ where
  field
    summaryPacketSurface : BrainSummaryPacketCompatibilitySurface
    representative3 : Summary.BrainSummaryPacketView → DNA3
    representativeEigen : Summary.BrainSummaryPacketView → EigenClass3
    representativeMacro : Summary.BrainSummaryPacketView → MacroAdjacencySurface

    representativeOrder :
      ∀ {n} → BrainState n → ScanOrder

    representativeAdjacencyScore :
      ∀ {n} → BrainState n → Nat

brainSummaryEigenclassCompatibilitySurface :
  BrainSummaryEigenclassCompatibilitySurface
brainSummaryEigenclassCompatibilitySurface = record
  { summaryPacketSurface = brainSummaryPacketCompatibilitySurface
  ; representative3 = summaryRepresentative3
  ; representativeEigen = summaryRepresentativeEigen
  ; representativeMacro = summaryRepresentativeMacro
  ; representativeOrder =
      ES.MacroAdjacencySurface.scanOrder ∘ summaryRepresentativeMacro ∘ summaryStatePacketView
  ; representativeAdjacencyScore =
      ES.MacroAdjacencySurface.adjacencyScore ∘ summaryRepresentativeMacro ∘ summaryStatePacketView
  }
  where
  infixr 9 _∘_
  _∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
        (B → C) → (A → B) → A → C
  (f ∘ g) x = f (g x)
