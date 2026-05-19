module DASHI.Physics.Closure.RGObservableInvariance where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (_≤_)

open import DASHI.Execution.Contract as EC
open import Ontology.Hecke.Scan as HS
open import Ontology.Hecke.PrimeHeckeEigenMotifPipeline as PHEM

private
  variable
    ℓx ℓs ℓδ ℓπ ℓe ℓa ℓb ℓc : Level

-- Typed observable carried by RG schedules. This bundles the explicit
-- closure-facing channels we want to keep invariant up to a chosen quotient.
record RGObservable
  (BasinLabel : Set ℓb)
  (Motif : Set)
  : Set ℓb where
  constructor rgObservable
  field
    mdlLevel : Nat
    basinLabel : BasinLabel
    heckeSignature : HS.Sig15
    eigenSummary : PHEM.EigenProfile
    motifClass : Motif

open RGObservable public

record RGObservableSurface
  {ℓx ℓs ℓδ ℓπ ℓe ℓb}
  (C : EC.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe})
  (HeckeState : Set)
  (BasinLabel : Set ℓb)
  (Motif : Set)
  : Set (lsuc (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe ⊔ ℓb)) where
  field
    toHeckeState : EC.Contract.State C → HeckeState
    classifyBasin : EC.Contract.Source C → BasinLabel
    pipeline : PHEM.PrimeHeckeEigenMotifPipelineOn HeckeState Motif
    coneWitness : EC.Contract.State C → Set

  signatureOf : EC.Contract.State C → HS.Sig15
  signatureOf x =
    HS.scanOn (PHEM.PrimeHeckeEigenMotifPipelineOn.hecke pipeline) (toHeckeState x)

  eigenProfileOf : EC.Contract.State C → PHEM.EigenProfile
  eigenProfileOf x =
    PHEM.PrimeHeckeEigenMotifPipelineOn.signatureEigenProfile pipeline (signatureOf x)

  motifOfState : EC.Contract.State C → Motif
  motifOfState x =
    PHEM.PrimeHeckeEigenMotifPipelineOn.motifOf pipeline (eigenProfileOf x)

  observe : EC.Contract.State C → RGObservable BasinLabel Motif
  observe x = rgObservable
    (EC.Contract.L C x)
    (classifyBasin (EC.Contract.π C x))
    (signatureOf x)
    (eigenProfileOf x)
    (motifOfState x)

open RGObservableSurface public

-- Coarse/evolve witness package with componentwise schedule laws.
record RGCoarseWitnessPackage
  {ℓx ℓs ℓδ ℓπ ℓe ℓa ℓb}
  (C : EC.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe})
  {HeckeState : Set}
  {BasinLabel : Set ℓb}
  {Motif : Set}
  (surface : RGObservableSurface C HeckeState BasinLabel Motif)
  : Set (lsuc (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe ⊔ ℓa ⊔ ℓb)) where
  field
    evolve : EC.Contract.State C → EC.Contract.State C
    coarse : EC.Contract.State C → EC.Contract.State C
    admissible : EC.Contract.State C → Set ℓa
    execution : EC.Contract.ExecutionAdmissible C

    -- Connect RG admissibility to the execution contract.
    admissible⇒basin :
      ∀ x →
      admissible x →
      EC.Contract.InBasin C (EC.Contract.π C x)

    admissible-evolve :
      ∀ x →
      admissible x →
      admissible (evolve x)

    admissible-coarse :
      ∀ x →
      admissible x →
      admissible (coarse x)

    -- Componentwise schedule preservation.
    mdl-schedule :
      ∀ x →
      admissible x →
      RGObservable.mdlLevel (RGObservableSurface.observe surface (coarse (evolve x)))
        ≡
      RGObservable.mdlLevel (RGObservableSurface.observe surface (evolve (coarse x)))

    basin-schedule :
      ∀ x →
      admissible x →
      RGObservable.basinLabel (RGObservableSurface.observe surface (coarse (evolve x)))
        ≡
      RGObservable.basinLabel (RGObservableSurface.observe surface (evolve (coarse x)))

    signature-schedule :
      ∀ x →
      admissible x →
      RGObservable.heckeSignature (RGObservableSurface.observe surface (coarse (evolve x)))
        ≡
      RGObservable.heckeSignature (RGObservableSurface.observe surface (evolve (coarse x)))

    eigen-schedule :
      ∀ x →
      admissible x →
      RGObservable.eigenSummary (RGObservableSurface.observe surface (coarse (evolve x)))
        ≡
      RGObservable.eigenSummary (RGObservableSurface.observe surface (evolve (coarse x)))

    motif-schedule :
      ∀ x →
      admissible x →
      RGObservable.motifClass (RGObservableSurface.observe surface (coarse (evolve x)))
        ≡
      RGObservable.motifClass (RGObservableSurface.observe surface (evolve (coarse x)))

    -- Cone witness preserved/reflected along both schedules.
    cone-preserved-left :
      ∀ x →
      admissible x →
      RGObservableSurface.coneWitness surface x →
      RGObservableSurface.coneWitness surface (coarse (evolve x))

    cone-preserved-right :
      ∀ x →
      admissible x →
      RGObservableSurface.coneWitness surface x →
      RGObservableSurface.coneWitness surface (evolve (coarse x))

    -- Observable quotient law (for motif/eigen class equivalence usage).
    Observable≈ : RGObservable BasinLabel Motif → RGObservable BasinLabel Motif → Set

    quotient-from-components :
      ∀ o₁ o₂ →
      RGObservable.mdlLevel o₁ ≡ RGObservable.mdlLevel o₂ →
      RGObservable.basinLabel o₁ ≡ RGObservable.basinLabel o₂ →
      RGObservable.heckeSignature o₁ ≡ RGObservable.heckeSignature o₂ →
      RGObservable.eigenSummary o₁ ≡ RGObservable.eigenSummary o₂ →
      RGObservable.motifClass o₁ ≡ RGObservable.motifClass o₂ →
      Observable≈ o₁ o₂

  execution-step-basin :
    ∀ x →
    admissible x →
    EC.Contract.InBasin C (EC.Contract.π C (EC.Contract.step C x))
  execution-step-basin x ax =
    EC.Contract.ExecutionAdmissible.basin-preserved execution x (admissible⇒basin x ax)

  execution-step-mdl :
    ∀ x →
    EC.Contract.L C (EC.Contract.step C x) ≤ EC.Contract.L C x
  execution-step-mdl x =
    EC.Contract.ExecutionAdmissible.mdl-descent execution x

  schedule-invariant :
    ∀ x →
    admissible x →
    RGObservableSurface.observe surface (coarse (evolve x))
      ≡
    RGObservableSurface.observe surface (evolve (coarse x))
  schedule-invariant x ax
    rewrite mdl-schedule x ax
          | basin-schedule x ax
          | signature-schedule x ax
          | eigen-schedule x ax
          | motif-schedule x ax
    = refl

  schedule-invariant-quotient :
    ∀ x →
    admissible x →
    Observable≈
      (RGObservableSurface.observe surface (coarse (evolve x)))
      (RGObservableSurface.observe surface (evolve (coarse x)))
  schedule-invariant-quotient x ax =
    quotient-from-components
      (RGObservableSurface.observe surface (coarse (evolve x)))
      (RGObservableSurface.observe surface (evolve (coarse x)))
      (mdl-schedule x ax)
      (basin-schedule x ax)
      (signature-schedule x ax)
      (eigen-schedule x ax)
      (motif-schedule x ax)

open RGCoarseWitnessPackage public

-- Legacy one-equation shell preserved for compatibility.
record ObservableRGInvariance
  {ℓs ℓo ℓa : Level}
  (State : Set ℓs)
  (Observable : Set ℓo)
  : Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa)) where
  field
    admissible0 : State → Set ℓa
    evolve0 : State → State
    coarse0 : State → State
    observe0 : State → Observable
    invariant0 :
      ∀ x →
      admissible0 x →
      observe0 (coarse0 (evolve0 x)) ≡ observe0 (evolve0 (coarse0 x))

open ObservableRGInvariance public

record ObservableRGUniversality
  {ℓs ℓo ℓa ℓq : Level}
  (State : Set ℓs)
  (Observable : Set ℓo)
  (_≈_ : Observable → Observable → Set ℓq)
  : Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa ⊔ ℓq)) where
  field
    admissibleU : State → Set ℓa
    evolveU : State → State
    coarseU : State → State
    observeU : State → Observable
    universalityU :
      ∀ x →
      admissibleU x →
      _≈_
        (observeU (coarseU (evolveU x)))
        (observeU (evolveU (coarseU x)))

open ObservableRGUniversality public

record ObservableRGOffsetUniversality
  {ℓs ℓo ℓa ℓq : Level}
  (State : Set ℓs)
  (Observable : Set ℓo)
  (_≈_ : Observable → Observable → Set ℓq)
  : Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa ⊔ ℓq)) where
  field
    admissibleO : State → Set ℓa
    evolveA : State → State
    coarseA : State → State
    evolveB : State → State
    coarseB : State → State
    observeO : State → Observable
    offset : State → State
    universalityOffset :
      ∀ x →
      admissibleO x →
      _≈_
        (observeO (coarseA (evolveA (offset x))))
        (observeO (coarseB (evolveB x)))

open ObservableRGOffsetUniversality public

record ProjectionDeltaCompatibility
  {ℓs ℓo ℓa ℓc ℓq : Level}
  (State : Set ℓs)
  (Observable : Set ℓo)
  (_≈_ : Observable → Observable → Set ℓq)
  : Set (lsuc (ℓs ⊔ ℓo ⊔ ℓa ⊔ ℓc ⊔ ℓq)) where
  field
    admissibleΔ : State → Set ℓa
    projectA : State → State
    projectB : State → State
    observeΔ : State → Observable
    coneΔ : State → Set ℓc

    cone-projectA :
      ∀ x →
      admissibleΔ x →
      coneΔ x →
      coneΔ (projectA x)

    cone-projectB :
      ∀ x →
      admissibleΔ x →
      coneΔ x →
      coneΔ (projectB x)

    universalityΔ :
      ∀ x →
      admissibleΔ x →
      _≈_
        (observeΔ (projectA x))
        (observeΔ (projectB x))

open ProjectionDeltaCompatibility public

fromRGCoarseWitnessPackage :
  {ℓx ℓs ℓδ ℓπ ℓe ℓa ℓb : Level}
  (C : EC.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe})
  {HeckeState : Set}
  {BasinLabel : Set ℓb}
  {Motif : Set}
  (surface : RGObservableSurface C HeckeState BasinLabel Motif)
  (pkg : RGCoarseWitnessPackage {ℓa = ℓa} C surface)
  → ObservableRGInvariance (EC.Contract.State C) (RGObservable BasinLabel Motif)
fromRGCoarseWitnessPackage C surface pkg = record
  { admissible0 = RGCoarseWitnessPackage.admissible pkg
  ; evolve0 = RGCoarseWitnessPackage.evolve pkg
  ; coarse0 = RGCoarseWitnessPackage.coarse pkg
  ; observe0 = RGObservableSurface.observe surface
  ; invariant0 = RGCoarseWitnessPackage.schedule-invariant pkg
  }

fromRGCoarseWitnessPackageUniversality :
  {ℓx ℓs ℓδ ℓπ ℓe ℓa ℓb : Level}
  (C : EC.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe})
  {HeckeState : Set}
  {BasinLabel : Set ℓb}
  {Motif : Set}
  (surface : RGObservableSurface C HeckeState BasinLabel Motif)
  (pkg : RGCoarseWitnessPackage {ℓa = ℓa} C surface)
  → ObservableRGUniversality
      (EC.Contract.State C)
      (RGObservable BasinLabel Motif)
      (RGCoarseWitnessPackage.Observable≈ pkg)
fromRGCoarseWitnessPackageUniversality C surface pkg = record
  { admissibleU = RGCoarseWitnessPackage.admissible pkg
  ; evolveU = RGCoarseWitnessPackage.evolve pkg
  ; coarseU = RGCoarseWitnessPackage.coarse pkg
  ; observeU = RGObservableSurface.observe surface
  ; universalityU = RGCoarseWitnessPackage.schedule-invariant-quotient pkg
  }
