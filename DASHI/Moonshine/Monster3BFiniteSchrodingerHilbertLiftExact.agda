module DASHI.Moonshine.Monster3BFiniteSchrodingerHilbertLiftExact where

------------------------------------------------------------------------
-- FINITE SCHRODINGER FUNCTION SPACE AS A REPO-NATIVE HILBERTLIFT
--
-- DASHI CONTRIBUTION
--
-- The exact function module already owns:
--
--   Vector = X6 -> Q(zeta_3)
--   zero, addition, cyclotomic scalar multiplication.
--
-- The generic ternary finite-function owner gives the exact Cube6 <-> X6
-- rechart.  This file adds the canonical finite cyclotomic pairing
--
--   <f,g> = sum_{x in X6} conjugate(f x) * g x
--
-- by recursion on TritCube, then packages the function module as the repo's
-- minimal HilbertLift.  Together with the full Heisenberg action law now paid,
-- this yields an actual LINEAR SCHRODINGER REPRESENTATION CANDIDATE.
--
-- Recognition as the Monster constituent H_zeta remains separate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import DASHI.Algebra.Trit using (neg; zer; pos)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as Schrodinger
import DASHI.Moonshine.Monster3BFiniteSchrodingerHeisenbergActionExact as Action
import DASHI.Moonshine.Monster3BFiniteSchrodingerFullActionLawExact as FullAction
import DASHI.Moonshine.TernaryFiniteFunctionDeltaBasisExact as Delta

------------------------------------------------------------------------
-- 1. Canonical ternary finite sum.
------------------------------------------------------------------------

sumCube :
  ∀ {n : Nat} →
  (Delta.TritCube n → C3.Cyclotomic3) →
  C3.Cyclotomic3
sumCube {zero} f =
  f Delta.cube0
sumCube {suc n} f =
  Schrodinger.addC3
    (sumCube (λ tail → f (Delta.cubeS neg tail)))
    (Schrodinger.addC3
      (sumCube (λ tail → f (Delta.cubeS zer tail)))
      (sumCube (λ tail → f (Delta.cubeS pos tail))))

sumX6 :
  (H0 : G.X6 → C3.Cyclotomic3) →
  C3.Cyclotomic3
sumX6 f =
  sumCube (λ cube → f (Delta.toX6 cube))

------------------------------------------------------------------------
-- 2. Canonical cyclotomic finite-function pairing.
------------------------------------------------------------------------

schrodingerPairing :
  Schrodinger.SchrodingerFunction →
  Schrodinger.SchrodingerFunction →
  C3.Cyclotomic3
schrodingerPairing f g =
  sumX6
    (λ x →
      C3.multiply
        (C3.conjugate (f x))
        (g x))

------------------------------------------------------------------------
-- 3. Exact HilbertLift packaging.
------------------------------------------------------------------------

schrodingerHilbertLift : Linear.HilbertLift
schrodingerHilbertLift =
  record
    { Vector = Schrodinger.SchrodingerFunction
    ; Scalar = C3.Cyclotomic3
    ; zero = Schrodinger.zeroFunction
    ; _+_ = Schrodinger.addFunction
    ; _·_ = Schrodinger.cyclotomicScaleFunction
    ; _∗_ = C3.multiply
    ; ⟪_,_⟫ = schrodingerPairing
    }

------------------------------------------------------------------------
-- 4. Exact finite-Heisenberg action on that same linear carrier.
------------------------------------------------------------------------

schrodingerHeisenbergLinearAction :
  Linear.LinearAction schrodingerHilbertLift
schrodingerHeisenbergLinearAction =
  record
    { Group = H.Heisenberg6
    ; act = Action.heisenbergAction
    }

fullHeisenbergActionLaw :
  Action.FullHeisenbergActionLawReceipt
fullHeisenbergActionLaw =
  FullAction.canonicalFullHeisenbergActionLawReceipt

------------------------------------------------------------------------
-- 5. Basis/spanning donor on the SAME vector carrier.
------------------------------------------------------------------------

deltaBasisBoundary :
  Delta.TernaryFiniteFunctionDeltaBasisBoundary
deltaBasisBoundary =
  Delta.canonicalTernaryFiniteFunctionDeltaBasisBoundary

all729DeltaLinesSpan :
  Delta.all729DeltasSpanEverySchrodingerFunction deltaBasisBoundary
  ≡ true
all729DeltaLinesSpan = refl

------------------------------------------------------------------------
-- 6. Recognition boundary.
------------------------------------------------------------------------

data FiniteSchrodingerLinearCarrierIsActualMonsterHZeta : Set where
data SameCyclotomicScalarCreatesActualHZetaRecognition : Set where
data Dimension729CreatesActualHZetaRecognition : Set where

finiteModelDoesNotCreateMonsterRecognition :
  FiniteSchrodingerLinearCarrierIsActualMonsterHZeta → ⊥
finiteModelDoesNotCreateMonsterRecognition ()

sameScalarDoesNotCreateRecognition :
  SameCyclotomicScalarCreatesActualHZetaRecognition → ⊥
sameScalarDoesNotCreateRecognition ()

dimensionDoesNotCreateRecognition :
  Dimension729CreatesActualHZetaRecognition → ⊥
dimensionDoesNotCreateRecognition ()

record SchrodingerHilbertLiftBoundary : Set where
  constructor schrodinger-hilbert-lift-boundary
  field
    exactFunctionCarrierReused : Bool
    canonicalTernaryFiniteSumOwned : Bool
    canonicalCyclotomicPairingOwned : Bool
    hilbertLiftPackaged : Bool
    fullHeisenbergLinearActionPackaged : Bool
    fullActionLawReceiptConsumed : Bool
    deltaSpanningDonorReused : Bool
    actualMonsterHZetaRecognitionPaid : Bool

canonicalSchrodingerHilbertLiftBoundary :
  SchrodingerHilbertLiftBoundary
canonicalSchrodingerHilbertLiftBoundary =
  schrodinger-hilbert-lift-boundary
    true true true true true true true false
