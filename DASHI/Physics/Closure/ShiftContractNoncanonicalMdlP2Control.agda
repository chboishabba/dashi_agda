module DASHI.Physics.Closure.ShiftContractNoncanonicalMdlP2Control where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.Closure.RGObservableInvariance as RGOI
open import DASHI.Physics.Closure.ShiftContractCoarseObservable as SCCO
open import DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction as OB
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState)
open import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS

------------------------------------------------------------------------
-- Exact stronger package above π-max:
-- add the shift RG mdlLevel channel and test whether it can support a
-- narrow noncanonical p2-style control surface.
--
-- Positive control is not currently supportable from the available lemmas.
-- The sharpest compiling result for this exact stronger package is that it
-- separates the current obstruction pair, so the old coarse obstruction does
-- not survive unchanged.

MdlLevelMaximalCoarseObservable : Set
MdlLevelMaximalCoarseObservable = Nat × SCCO.MaximalCoarseObservable

π-mdl-max : ShiftContractState → MdlLevelMaximalCoarseObservable
π-mdl-max x =
  RGOI.RGObservable.mdlLevel
    (RGOI.RGObservableSurface.observe SRGOI.shiftRGSurface x)
  , SCCO.π-max x

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

π-mdl-max-separates-obstruction-pair :
  π-mdl-max OB.coarseCounterexampleLeft
    ≢
  π-mdl-max OB.coarseCounterexampleRight
π-mdl-max-separates-obstruction-pair eq with cong proj₁ eq
... | ()

record NoncanonicalMdlP2ControlSurface : Set₁ where
  field
    p2Key : ShiftContractState → FOS.DefectOrbitSummary
    coarse-controls-p2 :
      ∀ x y →
      π-mdl-max x ≡ π-mdl-max y →
      p2Key x ≡ p2Key y
    p2-controls-prime-image :
      ∀ x y →
      p2Key x ≡ p2Key y →
      SCSP.shiftContractStateTransportedPrimeEmbedding x
        ≡
      SCSP.shiftContractStateTransportedPrimeEmbedding y

