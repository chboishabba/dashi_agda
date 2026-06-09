module DASHI.Physics.Closure.LegendrePrimeLaneCliffordBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.DivMod using (_%_)
open import Data.Nat.Base using (NonZero; nonZero)
open import Data.Nat.Properties as NatP using (_≟_)
open import Relation.Nullary using (Dec; yes; no)

open import DASHI.Physics.FiniteAlgebraCandidates using (MatrixAlg; M2C)
open import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface using
  (MonsterPrimeLane; p7; p11; p13)
open import DASHI.Physics.Closure.TriadicMatrixGenerationTheorem using
  (DialecticalStage; thesis; antithesis; synthesis; completion
  ; M2BasisElement; e11; e12; e21; e22
  ; stageToBasis
  ; TriadicMatrixGenerationTheorem
  ; canonicalTriadicMatrixGenerationTheorem)

------------------------------------------------------------------------
-- Finite Legendre-sign bridge for the selected 7/11/13 lane triple.
--
-- This is an inhabited finite surface. It does not claim a general
-- Legendre-symbol library or a full quotient identification theorem. It
-- computes the selected-prime sign data with a terminating finite residue
-- search, records the concrete 7/11/13 route-B witness, and packages the
-- triadic M2 basis bridge already present in the repo.

data Sign : Set where
  pos neg : Sign

data SelectedPrimeLane : Set where
  lane7 lane11 lane13 : SelectedPrimeLane

canonicalSelectedPrimeLaneOrder : List SelectedPrimeLane
canonicalSelectedPrimeLaneOrder =
  lane7 ∷ lane11 ∷ lane13 ∷ []

selectedPrimeLaneToPrime :
  SelectedPrimeLane → MonsterPrimeLane
selectedPrimeLaneToPrime lane7 = p7
selectedPrimeLaneToPrime lane11 = p11
selectedPrimeLaneToPrime lane13 = p13

selectedPrimeLaneToNat :
  SelectedPrimeLane → Nat
selectedPrimeLaneToNat lane7 = 7
selectedPrimeLaneToNat lane11 = 11
selectedPrimeLaneToNat lane13 = 13

selectedPrimeLaneToStage :
  SelectedPrimeLane → DialecticalStage
selectedPrimeLaneToStage lane7 = thesis
selectedPrimeLaneToStage lane11 = antithesis
selectedPrimeLaneToStage lane13 = synthesis

selectedPrimeLaneToBasis :
  SelectedPrimeLane → M2BasisElement
selectedPrimeLaneToBasis lane7 = stageToBasis thesis
selectedPrimeLaneToBasis lane11 = stageToBasis antithesis
selectedPrimeLaneToBasis lane13 = stageToBasis synthesis

canonicalSelectedPrimeLanePrimeOrder : List MonsterPrimeLane
canonicalSelectedPrimeLanePrimeOrder =
  p7 ∷ p11 ∷ p13 ∷ []

canonicalSelectedPrimeLaneNatOrder : List Nat
canonicalSelectedPrimeLaneNatOrder =
  7 ∷ 11 ∷ 13 ∷ []

canonicalSelectedStageOrder : List DialecticalStage
canonicalSelectedStageOrder =
  thesis ∷ antithesis ∷ synthesis ∷ completion ∷ []

canonicalSelectedBasisOrder : List M2BasisElement
canonicalSelectedBasisOrder =
  e11 ∷ e12 ∷ e21 ∷ e22 ∷ []

isQuadraticResidueSearch :
  (a modulus : Nat) → ⦃ _ : NonZero modulus ⦄ →
  Nat → Nat → Bool
isQuadraticResidueSearch a modulus candidate zero = false
isQuadraticResidueSearch a modulus candidate (suc fuel)
  with ((candidate * candidate) % modulus) NatP.≟ (a % modulus)
... | yes _ = true
... | no _ = isQuadraticResidueSearch a modulus (suc candidate) fuel

isQuadraticResidueBool :
  Nat → Nat → Bool
isQuadraticResidueBool a zero = false
isQuadraticResidueBool a (suc p) =
  isQuadraticResidueSearch a (suc p) zero p
  where
    instance
      modulusIsNonZero : NonZero (suc p)
      modulusIsNonZero = nonZero

halfPred : Nat → Nat
halfPred zero = zero
halfPred (suc zero) = zero
halfPred (suc (suc n)) = suc (halfPred n)

pow : Nat → Nat → Nat
pow a zero = suc zero
pow a (suc n) = a * pow a n

eulerExpNonZero : (a p : Nat) → ⦃ _ : NonZero p ⦄ → Nat
eulerExpNonZero a p = (pow a (halfPred p)) % p

eulerExp : Nat → Nat → Nat
eulerExp a zero = zero
eulerExp a (suc p) =
  eulerExpNonZero a (suc p)
  where
    instance
      modulusIsNonZero : NonZero (suc p)
      modulusIsNonZero = nonZero

eulerSign : Nat → Nat → Sign
eulerSign a p with eulerExp a p NatP.≟ suc zero
... | yes _ = pos
... | no _ = neg

eulerWitness-7-11 :
  eulerExp 7 11 ≡ 10
eulerWitness-7-11 = refl

eulerWitness-7-13 :
  eulerExp 7 13 ≡ 12
eulerWitness-7-13 = refl

eulerWitness-11-13 :
  eulerExp 11 13 ≡ 12
eulerWitness-11-13 = refl

eulerSign-7-11 :
  eulerSign 7 11 ≡ neg
eulerSign-7-11 = refl

eulerSign-7-13 :
  eulerSign 7 13 ≡ neg
eulerSign-7-13 = refl

eulerSign-11-13 :
  eulerSign 11 13 ≡ neg
eulerSign-11-13 = refl

selectedLegendreSignNat :
  Nat → Nat → Sign
selectedLegendreSignNat a p with isQuadraticResidueBool a p
... | true = pos
... | false = neg

selectedLegendreSign :
  SelectedPrimeLane → SelectedPrimeLane → Sign
selectedLegendreSign lane7 lane7 = selectedLegendreSignNat 7 7
selectedLegendreSign lane7 lane11 = selectedLegendreSignNat 7 11
selectedLegendreSign lane7 lane13 = selectedLegendreSignNat 7 13
selectedLegendreSign lane11 lane7 = selectedLegendreSignNat 11 7
selectedLegendreSign lane11 lane11 = selectedLegendreSignNat 11 11
selectedLegendreSign lane11 lane13 = selectedLegendreSignNat 11 13
selectedLegendreSign lane13 lane7 = selectedLegendreSignNat 13 7
selectedLegendreSign lane13 lane11 = selectedLegendreSignNat 13 11
selectedLegendreSign lane13 lane13 = selectedLegendreSignNat 13 13

selectedSign7-11 :
  selectedLegendreSign lane7 lane11 ≡ neg
selectedSign7-11 = refl

selectedSign7-13 :
  selectedLegendreSign lane7 lane13 ≡ neg
selectedSign7-13 = refl

selectedSign11-13 :
  selectedLegendreSign lane11 lane13 ≡ neg
selectedSign11-13 = refl

record LegendreCliffordBridge : Set₁ where
  field
    triadicBridge :
      TriadicMatrixGenerationTheorem

    selectedPrimeLanes :
      List SelectedPrimeLane

    selectedPrimeLanesIsCanonical :
      selectedPrimeLanes ≡ canonicalSelectedPrimeLaneOrder

    selectedPrimeLanePrimeOrder :
      List MonsterPrimeLane

    selectedPrimeLanePrimeOrderIsCanonical :
      selectedPrimeLanePrimeOrder ≡ canonicalSelectedPrimeLanePrimeOrder

    selectedPrimeLaneNatOrder :
      List Nat

    selectedPrimeLaneNatOrderIsCanonical :
      selectedPrimeLaneNatOrder ≡ canonicalSelectedPrimeLaneNatOrder

    selectedPrimeLaneToPrimeMap :
      SelectedPrimeLane → MonsterPrimeLane

    selectedPrimeLaneToPrimeMapIsCanonical :
      selectedPrimeLaneToPrimeMap ≡ selectedPrimeLaneToPrime

    selectedPrimeLaneToStageMap :
      SelectedPrimeLane → DialecticalStage

    selectedPrimeLaneToStageMapIsCanonical :
      selectedPrimeLaneToStageMap ≡ selectedPrimeLaneToStage

    selectedPrimeLaneToBasisMap :
      SelectedPrimeLane → M2BasisElement

    selectedPrimeLaneToBasisMapIsCanonical :
      selectedPrimeLaneToBasisMap ≡ selectedPrimeLaneToBasis

    selectedSignTable :
      SelectedPrimeLane → SelectedPrimeLane → Sign

    selectedSign7-11IsNegative :
      selectedSignTable lane7 lane11 ≡ neg

    selectedSign7-13IsNegative :
      selectedSignTable lane7 lane13 ≡ neg

    selectedSign11-13IsNegative :
      selectedSignTable lane11 lane13 ≡ neg

    matrixAlgebra :
      MatrixAlg

    matrixAlgebraIsM2C :
      matrixAlgebra ≡ M2C

    stageOrder :
      List DialecticalStage

    stageOrderIsCanonical :
      stageOrder ≡ canonicalSelectedStageOrder

    basisOrder :
      List M2BasisElement

    basisOrderIsCanonical :
      basisOrder ≡ canonicalSelectedBasisOrder

    routeBoundary :
      List String

canonicalLegendreCliffordBridge :
  LegendreCliffordBridge
canonicalLegendreCliffordBridge =
  record
    { triadicBridge =
        canonicalTriadicMatrixGenerationTheorem
    ; selectedPrimeLanes =
        canonicalSelectedPrimeLaneOrder
    ; selectedPrimeLanesIsCanonical =
        refl
    ; selectedPrimeLanePrimeOrder =
        canonicalSelectedPrimeLanePrimeOrder
    ; selectedPrimeLanePrimeOrderIsCanonical =
        refl
    ; selectedPrimeLaneNatOrder =
        canonicalSelectedPrimeLaneNatOrder
    ; selectedPrimeLaneNatOrderIsCanonical =
        refl
    ; selectedPrimeLaneToPrimeMap =
        selectedPrimeLaneToPrime
    ; selectedPrimeLaneToPrimeMapIsCanonical =
        refl
    ; selectedPrimeLaneToStageMap =
        selectedPrimeLaneToStage
    ; selectedPrimeLaneToStageMapIsCanonical =
        refl
    ; selectedPrimeLaneToBasisMap =
        selectedPrimeLaneToBasis
    ; selectedPrimeLaneToBasisMapIsCanonical =
        refl
    ; selectedSignTable =
        selectedLegendreSign
    ; selectedSign7-11IsNegative =
        selectedSign7-11
    ; selectedSign7-13IsNegative =
        selectedSign7-13
    ; selectedSign11-13IsNegative =
        selectedSign11-13
    ; matrixAlgebra =
        M2C
    ; matrixAlgebraIsM2C =
        refl
    ; stageOrder =
        canonicalSelectedStageOrder
    ; stageOrderIsCanonical =
        refl
    ; basisOrder =
        canonicalSelectedBasisOrder
    ; basisOrderIsCanonical =
        refl
    ; routeBoundary =
        "finite selected-prime Legendre bridge for 7/11/13"
        ∷ "selected signs are inhabited by a terminating residue search, not a postulate"
        ∷ "triadic bridge into canonical M2(C) is consumed from the existing theorem"
        ∷ "completion slot remains the e22 basis element"
        ∷ "this records the route-B Clifford witness only; it does not claim full quotient or SM closure"
        ∷ []
    }

record PrimeLaneQuotientWitness : Set₁ where
  field
    selectedPrimeLanes :
      List SelectedPrimeLane

    selectedPrimeLanesIsCanonical :
      selectedPrimeLanes ≡ canonicalSelectedPrimeLaneOrder

    selectedPrimeLanePrimeOrder :
      List MonsterPrimeLane

    selectedPrimeLanePrimeOrderIsCanonical :
      selectedPrimeLanePrimeOrder ≡ canonicalSelectedPrimeLanePrimeOrder

    selectedSignTable :
      SelectedPrimeLane → SelectedPrimeLane → Sign

    selectedSign7-11IsNegative :
      selectedSignTable lane7 lane11 ≡ neg

    selectedSign7-13IsNegative :
      selectedSignTable lane7 lane13 ≡ neg

    selectedSign11-13IsNegative :
      selectedSignTable lane11 lane13 ≡ neg

    triadicBridge :
      TriadicMatrixGenerationTheorem

    matrixAlgebra :
      MatrixAlg

    matrixAlgebraIsM2C :
      matrixAlgebra ≡ M2C

    basisOrder :
      List M2BasisElement

    basisOrderIsCanonical :
      basisOrder ≡ canonicalSelectedBasisOrder

    routeBoundary :
      List String

canonicalPrimeLaneQuotientWitness :
  PrimeLaneQuotientWitness
canonicalPrimeLaneQuotientWitness =
  record
    { selectedPrimeLanes =
        canonicalSelectedPrimeLaneOrder
    ; selectedPrimeLanesIsCanonical =
        refl
    ; selectedPrimeLanePrimeOrder =
        canonicalSelectedPrimeLanePrimeOrder
    ; selectedPrimeLanePrimeOrderIsCanonical =
        refl
    ; selectedSignTable =
        selectedLegendreSign
    ; selectedSign7-11IsNegative =
        selectedSign7-11
    ; selectedSign7-13IsNegative =
        selectedSign7-13
    ; selectedSign11-13IsNegative =
        selectedSign11-13
    ; triadicBridge =
        canonicalTriadicMatrixGenerationTheorem
    ; matrixAlgebra =
        M2C
    ; matrixAlgebraIsM2C =
        refl
    ; basisOrder =
        canonicalSelectedBasisOrder
    ; basisOrderIsCanonical =
        refl
    ; routeBoundary =
        "concrete prime-lane quotient witness for selected lanes p7, p11, p13"
        ∷ "sign table is explicitly inhabited by finite computation, with the three off-diagonal negative entries recorded"
        ∷ "triadic basis theorem is consumed from the existing canonical theorem"
        ∷ "matrix algebra is the canonical M2(C) object already present in the repo"
        ∷ "this is a paper-facing witness package, not a quotient-isomorphism postulate"
        ∷ []
    }

open LegendreCliffordBridge public
open PrimeLaneQuotientWitness public
