module DASHI.Physics.Closure.ProductFormulaConstraint where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Abstract product formula constraint receipt.
--
-- This A2-only receipt records the abstract constraint
--
--   prod_p |x|_p * |x|_infty = 1
--
-- as a typed closure target.  It deliberately contains no concrete
-- p-adic valuation construction, no A1 dependency, and no physical,
-- Clay, or terminal promotion.  A concrete arithmetic implementation
-- must separately provide the finite-prime factors, the archimedean
-- factor, and the equality proof for a chosen carrier.

data ProductFormulaConstraintStatus : Set where
  failClosed_abstractConstraintRecorded_equalityProofExternal :
    ProductFormulaConstraintStatus

data ProductFormulaCarrier : Set where
  abstractGlobalFieldElement :
    ProductFormulaCarrier

data FinitePlaceFamily : Set where
  finitePrimeAdicAbsoluteValueFactors :
    FinitePlaceFamily

data ArchimedeanFactor : Set where
  archimedeanAbsoluteValueFactor :
    ArchimedeanFactor

data NormalizedProduct : Set where
  normalizedFiniteProductTimesArchimedean :
    NormalizedProduct

data ProductFormulaEquation : Set where
  productOverFinitePAbsXPTimesAbsXInfinityEqualsOne :
    ProductFormulaEquation

data ProductFormulaProofState : Set where
  externalProofRequired :
    ProductFormulaProofState

data ProductFormulaObligation : Set where
  defineFinitePrimeIndexSet :
    ProductFormulaObligation

  definePadicAbsoluteValues :
    ProductFormulaObligation

  defineArchimedeanAbsoluteValue :
    ProductFormulaObligation

  defineNormalizedFiniteProduct :
    ProductFormulaObligation

  proveProductFormulaEqualsOne :
    ProductFormulaObligation

  keepIndependentOfA1 :
    ProductFormulaObligation

  blockPhysicalClayAndTerminalPromotion :
    ProductFormulaObligation

canonicalProductFormulaObligations :
  List ProductFormulaObligation
canonicalProductFormulaObligations =
  defineFinitePrimeIndexSet
  ∷ definePadicAbsoluteValues
  ∷ defineArchimedeanAbsoluteValue
  ∷ defineNormalizedFiniteProduct
  ∷ proveProductFormulaEqualsOne
  ∷ keepIndependentOfA1
  ∷ blockPhysicalClayAndTerminalPromotion
  ∷ []

data PhysicalPromotionToken : Set where

data ClayPromotionToken : Set where

data TerminalPromotionToken : Set where

physicalPromotionImpossibleHere :
  PhysicalPromotionToken →
  ⊥
physicalPromotionImpossibleHere ()

clayPromotionImpossibleHere :
  ClayPromotionToken →
  ⊥
clayPromotionImpossibleHere ()

terminalPromotionImpossibleHere :
  TerminalPromotionToken →
  ⊥
terminalPromotionImpossibleHere ()

constraintStatement :
  String
constraintStatement =
  "Abstract product formula constraint: prod_p |x|_p * |x|_infty = 1."

finiteFactorStatement :
  String
finiteFactorStatement =
  "The finite component is the family of p-adic absolute-value factors |x|_p indexed by finite primes p."

archimedeanFactorStatement :
  String
archimedeanFactorStatement =
  "The archimedean component is the real/infinite absolute-value factor |x|_infty."

normalizedProductStatement :
  String
normalizedProductStatement =
  "The normalized product target is the finite prime product multiplied by the archimedean factor."

boundaryStatement :
  String
boundaryStatement =
  "Fail-closed A2 receipt only: no concrete equality proof, no A1 dependency, and no physical, Clay, or terminal promotion."

record ProductFormulaConstraintReceipt : Set where
  field
    status :
      ProductFormulaConstraintStatus

    statusIsFailClosed :
      status
      ≡ failClosed_abstractConstraintRecorded_equalityProofExternal

    carrier :
      ProductFormulaCarrier

    carrierIsAbstractGlobalFieldElement :
      carrier ≡ abstractGlobalFieldElement

    finitePadicFactors :
      FinitePlaceFamily

    finitePadicFactorsAreAbstract :
      finitePadicFactors ≡ finitePrimeAdicAbsoluteValueFactors

    archimedeanFactor :
      ArchimedeanFactor

    archimedeanFactorIsAbstract :
      archimedeanFactor ≡ archimedeanAbsoluteValueFactor

    normalizedProduct :
      NormalizedProduct

    normalizedProductIsFiniteTimesArchimedean :
      normalizedProduct ≡ normalizedFiniteProductTimesArchimedean

    constraintEquation :
      ProductFormulaEquation

    constraintEquationIsProductFormula :
      constraintEquation
      ≡ productOverFinitePAbsXPTimesAbsXInfinityEqualsOne

    proofState :
      ProductFormulaProofState

    proofStateRequiresExternalProof :
      proofState ≡ externalProofRequired

    obligations :
      List ProductFormulaObligation

    obligationsAreCanonical :
      obligations ≡ canonicalProductFormulaObligations

    finiteFactorSummary :
      String

    finiteFactorSummaryIsCanonical :
      finiteFactorSummary ≡ finiteFactorStatement

    archimedeanFactorSummary :
      String

    archimedeanFactorSummaryIsCanonical :
      archimedeanFactorSummary ≡ archimedeanFactorStatement

    normalizedProductSummary :
      String

    normalizedProductSummaryIsCanonical :
      normalizedProductSummary ≡ normalizedProductStatement

    constraintSummary :
      String

    constraintSummaryIsCanonical :
      constraintSummary ≡ constraintStatement

    boundarySummary :
      String

    boundarySummaryIsCanonical :
      boundarySummary ≡ boundaryStatement

    importsA1 :
      Bool

    importsA1IsFalse :
      importsA1 ≡ false

    concreteEqualityProofProvidedHere :
      Bool

    concreteEqualityProofProvidedHereIsFalse :
      concreteEqualityProofProvidedHere ≡ false

    physicalPromotion :
      Bool

    physicalPromotionIsFalse :
      physicalPromotion ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

canonicalProductFormulaConstraintReceipt :
  ProductFormulaConstraintReceipt
canonicalProductFormulaConstraintReceipt = record
  { status =
      failClosed_abstractConstraintRecorded_equalityProofExternal
  ; statusIsFailClosed =
      refl
  ; carrier =
      abstractGlobalFieldElement
  ; carrierIsAbstractGlobalFieldElement =
      refl
  ; finitePadicFactors =
      finitePrimeAdicAbsoluteValueFactors
  ; finitePadicFactorsAreAbstract =
      refl
  ; archimedeanFactor =
      archimedeanAbsoluteValueFactor
  ; archimedeanFactorIsAbstract =
      refl
  ; normalizedProduct =
      normalizedFiniteProductTimesArchimedean
  ; normalizedProductIsFiniteTimesArchimedean =
      refl
  ; constraintEquation =
      productOverFinitePAbsXPTimesAbsXInfinityEqualsOne
  ; constraintEquationIsProductFormula =
      refl
  ; proofState =
      externalProofRequired
  ; proofStateRequiresExternalProof =
      refl
  ; obligations =
      canonicalProductFormulaObligations
  ; obligationsAreCanonical =
      refl
  ; finiteFactorSummary =
      finiteFactorStatement
  ; finiteFactorSummaryIsCanonical =
      refl
  ; archimedeanFactorSummary =
      archimedeanFactorStatement
  ; archimedeanFactorSummaryIsCanonical =
      refl
  ; normalizedProductSummary =
      normalizedProductStatement
  ; normalizedProductSummaryIsCanonical =
      refl
  ; constraintSummary =
      constraintStatement
  ; constraintSummaryIsCanonical =
      refl
  ; boundarySummary =
      boundaryStatement
  ; boundarySummaryIsCanonical =
      refl
  ; importsA1 =
      false
  ; importsA1IsFalse =
      refl
  ; concreteEqualityProofProvidedHere =
      false
  ; concreteEqualityProofProvidedHereIsFalse =
      refl
  ; physicalPromotion =
      false
  ; physicalPromotionIsFalse =
      refl
  ; clayPromotion =
      false
  ; clayPromotionIsFalse =
      refl
  ; terminalPromotion =
      false
  ; terminalPromotionIsFalse =
      refl
  }

canonicalStatus :
  ProductFormulaConstraintStatus
canonicalStatus =
  ProductFormulaConstraintReceipt.status
    canonicalProductFormulaConstraintReceipt
