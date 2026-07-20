module DASHI.Physics.Closure.TriadicMatrixGenerationTheorem where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.FiniteAlgebraCandidates using (MatrixAlg; M2C)
open import DASHI.Physics.Closure.ShiftContractTriadicFamily as STF
  using (TriadicIndex; i0; i1; i2; triadicNext; triadicCycle)

-- Canonical compiler route for the exact quotient / character / modular-gate
-- tranche. DASHI.Everything already imports this triadic root, so both
-- regression surfaces below are included in the authoritative
-- `nix build .#check` typecheck without duplicating a new top-level lane.
import DASHI.Physics.Closure.TriadicArithmeticSpectralRegression
import DASHI.Physics.Closure.TriadicSpectralCompletionRegression

------------------------------------------------------------------------
-- Inhabited 3-6-9 matrix-generation bridge.
--
-- This is a concrete non-promoting target surface: the triadic carrier spine
-- already exists in the repo, and this module packages a canonical 4-slot
-- matrix basis bridge around it.  The `M3(C)` / `SU(3)` extension is left as a
-- future target.

data DialecticalStage : Set where
  thesis antithesis synthesis completion : DialecticalStage

data M2BasisElement : Set where
  e11 e12 e21 e22 : M2BasisElement

canonicalDialecticalStageOrder : List DialecticalStage
canonicalDialecticalStageOrder =
  thesis ∷ antithesis ∷ synthesis ∷ completion ∷ []

canonicalM2BasisOrder : List M2BasisElement
canonicalM2BasisOrder =
  e11 ∷ e12 ∷ e21 ∷ e22 ∷ []

stageToBasis : DialecticalStage → M2BasisElement
stageToBasis thesis = e11
stageToBasis antithesis = e12
stageToBasis synthesis = e21
stageToBasis completion = e22

triadicIndexToStage : TriadicIndex → DialecticalStage
triadicIndexToStage i0 = thesis
triadicIndexToStage i1 = antithesis
triadicIndexToStage i2 = synthesis

record TriadicMatrixGenerationTheorem : Set₁ where
  field
    matrixAlgebra :
      MatrixAlg

    matrixAlgebraIsM2C :
      matrixAlgebra ≡ M2C

    stageMap :
      DialecticalStage → M2BasisElement

    stageMapIsCanonical :
      stageMap ≡ stageToBasis

    thesisMapsToE11 :
      stageMap thesis ≡ e11

    antithesisMapsToE12 :
      stageMap antithesis ≡ e12

    synthesisMapsToE21 :
      stageMap synthesis ≡ e21

    completionMapsToE22 :
      stageMap completion ≡ e22

    stageOrder :
      List DialecticalStage

    stageOrderIsCanonical :
      stageOrder ≡ canonicalDialecticalStageOrder

    basisOrder :
      List M2BasisElement

    basisOrderIsCanonical :
      basisOrder ≡ canonicalM2BasisOrder

    triadicAnchor :
      TriadicIndex → DialecticalStage

    triadicAnchorIsCanonical :
      triadicAnchor ≡ triadicIndexToStage

    cycleLaw :
      ∀ i → triadicNext (triadicNext (triadicNext i)) ≡ i

canonicalTriadicMatrixGenerationTheorem :
  TriadicMatrixGenerationTheorem
canonicalTriadicMatrixGenerationTheorem =
  record
    { matrixAlgebra = M2C
    ; matrixAlgebraIsM2C = refl
    ; stageMap = stageToBasis
    ; stageMapIsCanonical = refl
    ; thesisMapsToE11 = refl
    ; antithesisMapsToE12 = refl
    ; synthesisMapsToE21 = refl
    ; completionMapsToE22 = refl
    ; stageOrder = canonicalDialecticalStageOrder
    ; stageOrderIsCanonical = refl
    ; basisOrder = canonicalM2BasisOrder
    ; basisOrderIsCanonical = refl
    ; triadicAnchor = triadicIndexToStage
    ; triadicAnchorIsCanonical = refl
    ; cycleLaw = triadicCycle
    }

open TriadicMatrixGenerationTheorem public
