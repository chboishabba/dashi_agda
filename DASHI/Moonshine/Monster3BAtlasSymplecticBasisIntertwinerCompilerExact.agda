module DASHI.Moonshine.Monster3BAtlasSymplecticBasisIntertwinerCompilerExact where

------------------------------------------------------------------------
-- ATLAS SYMPLECTIC-12 -> REPOSITORY X6 + X6* INTERTWINER / HEISENBERG LIFT
--
-- The ATLAS source pays existence of a 12-dimensional GF(3) symplectic module
-- for 2.Suz.2.  The repository independently owns the explicit standard
-- symplectic carrier
--
--     Symplectic12 = X6 + X6*
--
-- with pairing
--
--     omega((a,b),(a',b')) = a.b' - a'.b.
--
-- This file isolates the exact remaining same-object datum: an imported source
-- matrix action plus a change of symplectic basis into the repository carrier.
--
-- A subtlety matters.  The repository Heisenberg group uses the asymmetric
-- cocycle
--
--     c((a,b),(a',b')) = b.a'.
--
-- A symplectic quotient map preserves the alternating commutator form but need
-- not preserve this chosen cocycle literally.  Therefore a lift to the central
-- extension requires a central correction q satisfying the cocycle-coboundary
-- equation below.  This prevents us from silently identifying an Sp(12,3)
-- matrix with a Heisenberg automorphism without paying the phase correction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Algebra.Trit using (Trit)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BAtlasSymplectic12SourceReceiptExact as Source

------------------------------------------------------------------------
-- 1. Quotient addition and the repository cocycle.
------------------------------------------------------------------------

addSymplectic12 : H.Symplectic12 → H.Symplectic12 → H.Symplectic12
addSymplectic12 left right =
  H.symplectic12
    (H.addX6 (H.translationPart left) (H.translationPart right))
    (H.addX6 (H.modulationPart left) (H.modulationPart right))

heisenbergCocycle : H.Symplectic12 → H.Symplectic12 → Trit
heisenbergCocycle left right =
  H.dot6 (H.modulationPart left) (H.translationPart right)

------------------------------------------------------------------------
-- 2. Imported 12-dimensional source action after a chosen basis change.
------------------------------------------------------------------------

record RepositorySymplecticAction : Set where
  field
    act : H.Symplectic12 → H.Symplectic12
    additive :
      (left right : H.Symplectic12) →
      act (addSymplectic12 left right)
      ≡ addSymplectic12 (act left) (act right)
    preservesPairing :
      (left right : H.Symplectic12) →
      H.symplecticPair (act left) (act right)
      ≡ H.symplecticPair left right
open RepositorySymplecticAction public

/-- A source-to-repository recognition is stronger than existence of a
symplectic 12-module: it carries the imported source action into the exact
X6+X6* basis used by the Heisenberg and hyperfabric owners. -/
record AtlasToRepositorySymplecticRecognition : Set₁ where
  field
    atlasSource : Source.Atlas3BNormalizerSourceReceipt
    generatorA : RepositorySymplecticAction
    generatorB : RepositorySymplecticAction
    -- Further source generators can be added without changing the compiler.
    matrixEntriesImported : Bool
    sourcePreservedAlternatingFormComputed : Bool
    basisChangeToRepositoryStandardFormComputed : Bool
    sameActionIntertwiningChecked : Bool
open AtlasToRepositorySymplecticRecognition public

------------------------------------------------------------------------
-- 3. Exact central-correction condition for lifting to the chosen Heisenberg
--    cocycle.
------------------------------------------------------------------------

record HeisenbergCentralCorrection (action : RepositorySymplecticAction) : Set where
  field
    correction : H.Symplectic12 → Trit
    cocycleCoboundary :
      (left right : H.Symplectic12) →
      G._+3_
        (correction (addSymplectic12 left right))
        (heisenbergCocycle left right)
      ≡
      G._+3_
        (G._+3_ (correction left) (correction right))
        (heisenbergCocycle (act action left) (act action right))
open HeisenbergCentralCorrection public

liftToHeisenberg :
  (action : RepositorySymplecticAction) →
  HeisenbergCentralCorrection action →
  H.Heisenberg6 → H.Heisenberg6
liftToHeisenberg action phase g =
  H.heisenberg6
    (act action (H.quotient g))
    (G._+3_ (H.centralPhase g) (correction phase (H.quotient g)))

/-- The above coboundary condition is exactly the additional datum required for
`liftToHeisenberg` to preserve the repository's central-extension composition.
The homomorphism theorem itself is left to the concrete imported matrices once
that correction is computed, rather than postulated from symplecticity alone. -/
record HeisenbergLiftRecognition
    (action : RepositorySymplecticAction)
    (phase : HeisenbergCentralCorrection action) : Set where
  field
    preservesComposition :
      (left right : H.Heisenberg6) →
      liftToHeisenberg action phase (H.compose left right)
      ≡ H.compose
          (liftToHeisenberg action phase left)
          (liftToHeisenberg action phase right)
open HeisenbergLiftRecognition public

------------------------------------------------------------------------
-- 4. Terminal acquisition/intertwining boundary.
------------------------------------------------------------------------

record Boundary : Set where
  constructor boundary
  field
    sourceSymplectic12ExistencePaid : Bool
    repositoryStandardSymplectic12Paid : Bool
    sourceToRepositoryBasisIntertwinerTyped : Bool
    asymmetricCocycleCorrectionExposed : Bool
    genericHeisenbergLiftTyped : Bool
    rawAtlasMatricesImported : Bool
    concreteSymplecticBasisChangePaid : Bool
    concreteCentralCorrectionPaid : Bool
    concreteHeisenbergConjugationPaid : Bool
    outputTranslationEquivarianceCanBeInstantiated : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary
    Source.canonicalBoundary.sourceSymplectic12ActionExists
    true
    true
    true
    true
    false
    false
    false
    false
    false
