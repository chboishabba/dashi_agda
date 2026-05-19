module DASHI.Physics.Closure.ShiftContractNoncanonicalP2ControlObstruction where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Vec using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (cong)

open import Ontology.GodelLattice as GL using (FactorVec)
open import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS

open import DASHI.Algebra.Trit using (zer; pos)
open import DASHI.Physics.Closure.ShiftContractCoarseObservable as SCCO
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using (ShiftContractState; shiftContractStateTransportedPrimeEmbedding)

------------------------------------------------------------------------
-- Noncanonical p2-control obstruction.
--
-- The canonical closure fibre can use p2 orbit summaries as a control key
-- because the fibre is tiny.  On the full shift-contract carrier, the current
-- coarse observable surface is already too coarse: two explicit states share
-- the same coarse observable, but their transported prime images split.

coarseCounterexampleLeft : ShiftContractState
coarseCounterexampleLeft = zer ∷ zer ∷ zer ∷ zer ∷ []

coarseCounterexampleRight : ShiftContractState
coarseCounterexampleRight = zer ∷ pos ∷ zer ∷ zer ∷ []

sameCoarseObservable :
  SCCO.π-max coarseCounterexampleLeft
    ≡
  SCCO.π-max coarseCounterexampleRight
sameCoarseObservable = refl

primeImageSeparated :
  shiftContractStateTransportedPrimeEmbedding coarseCounterexampleLeft
    ≡
  shiftContractStateTransportedPrimeEmbedding coarseCounterexampleRight
    → ⊥
primeImageSeparated eq with cong GL.Vec15.e3 eq
... | ()

record NoncanonicalP2ControlSurface : Set₁ where
  field
    p2Key : ShiftContractState → FOS.DefectOrbitSummary
    coarse-controls-p2 :
      ∀ x y →
      SCCO.π-max x ≡ SCCO.π-max y →
      p2Key x ≡ p2Key y
    p2-controls-prime-image :
      ∀ x y →
      p2Key x ≡ p2Key y →
      shiftContractStateTransportedPrimeEmbedding x
        ≡
      shiftContractStateTransportedPrimeEmbedding y

noNoncanonicalP2ControlSurface :
  NoncanonicalP2ControlSurface → ⊥
noNoncanonicalP2ControlSurface surf =
  primeImageSeparated
    (NoncanonicalP2ControlSurface.p2-controls-prime-image surf
      coarseCounterexampleLeft
      coarseCounterexampleRight
      (NoncanonicalP2ControlSurface.coarse-controls-p2 surf
        coarseCounterexampleLeft
        coarseCounterexampleRight
        sameCoarseObservable))
