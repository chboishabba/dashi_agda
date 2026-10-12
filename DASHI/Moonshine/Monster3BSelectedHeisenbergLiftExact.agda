module DASHI.Moonshine.Monster3BSelectedHeisenbergLiftExact where

------------------------------------------------------------------------
-- SELECTED ATLAS NORMALIZER WORD -> REPOSITORY HEISENBERG LIFT
--
-- Exact producer:
--   scripts/verify_monster3b_selected_heisenberg_lift.py
-- Receipt:
--   outputs/monster3b_selected_heisenberg_lift_20261012.json
--
-- Starting from the vendored ATLAS 2.Suz / 2.Suz:2 matrices, the producer
-- recomputes the invariant alternating form and the repository X6 + X6* basis.
-- For the already-selected field-producing source word
--
--     g2 g1 g2^-1 g1 g2^-1
--
-- the resulting 12x12 action M has strict symplectic multiplier one.  Writing C
-- for the repository asymmetric Heisenberg cocycle matrix
--
--     c((a,b),(a',b')) = b . a',
--
-- the exact defect
--
--     D = M^T C M - C
--
-- is symmetric.  Therefore, because 1/2 = 2 in F3,
--
--     q(x) = 2 x^T D x
--
-- has polarization D and pays the exact central-coboundary equation
--
--     q(x+y) + c(x,y)
--       = q(x) + q(y) + c(Mx,My).
--
-- This closes the CENTRAL CORRECTION for this selected source element at exact
-- finite-producer level.  It does not promote one word to the full 2.Suz:2
-- normalizer, identify downstream Monster orbit/stabilizer semantics, or claim
-- a physical Monster realization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

selectedSourceWord : String
selectedSourceWord = "g2 g1 g2^-1 g1 g2^-1"

producerPath : String
producerPath = "scripts/verify_monster3b_selected_heisenberg_lift.py"

receiptPath : String
receiptPath = "outputs/monster3b_selected_heisenberg_lift_20261012.json"

centralCorrectionFormula : String
centralCorrectionFormula = "q(x)=2*x^T*D*x over GF(3), D=M^T*C*M-C"

record SelectedHeisenbergLiftReceipt : Set where
  constructor selected-heisenberg-lift-receipt
  field
    selectedWordSymplecticMultiplier : Nat
    compressionMatchesSelectedFieldReceipt : Bool
    cocycleDefectSymmetric : Bool
    cocycleDefectRank : Nat
    quadraticPolarizationIdentityPaid : Bool
    heisenbergCoboundaryIdentityPaid : Bool
    bruteForcePairEnumerationUsed : Bool
open SelectedHeisenbergLiftReceipt public

canonicalReceipt : SelectedHeisenbergLiftReceipt
canonicalReceipt =
  selected-heisenberg-lift-receipt
    1 true true 12 true true false

record Boundary : Set where
  constructor boundary
  field
    atlasMatricesVendored : Bool
    repositorySymplecticBasisRuntimePaid : Bool
    selectedWordFullTwelveActionReconstructed : Bool
    selectedWordStrictSymplectic : Bool
    selectedWordCompressionMatchesGF729Selector : Bool
    asymmetricCocycleDefectComputedExactly : Bool
    symmetricDefectPaid : Bool
    quadraticCentralCorrectionPaidByExactProducer : Bool
    selectedWordHeisenbergLiftPaidByExactProducer : Bool
    selectedWordHeisenbergLiftAgdaKernelPaid : Bool
    fullNormalizerHeisenbergActionPaid : Bool
    outputTranslationEquivarianceInstantiatedForActualMonsterAction : Bool
    physicalMonster3BRealizationPaid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary
    true true true true true true true true true
    false false false false
