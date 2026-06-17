module DASHI.Physics.Closure.GRPerturbationBoundShapeCore where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (ℕ; _≤_)

import DASHI.Physics.Closure.ContinuumLimitTheorem as Continuum
import DASHI.Physics.Closure.GRDiscreteBianchiFiniteR as Bianchi
import DASHI.Physics.Closure.GRDiscreteRicciCandidateFromCurvature as Ricci
import DASHI.Physics.Closure.GROrderedRationalFiniteSlotBoundCore as OrderedRational

------------------------------------------------------------------------
-- GR perturbation bound shape core.
--
-- This module is carrier/receipt only.  It records canonical receipts for
-- the Christoffel and Ricci perturbation routes plus explicit fail-closed
-- promotion blockers.  It does not fabricate local analytic theorems.

data GRPerturbationBoundShapeCoreStatus : Set where
  carrierOnlyFailClosed :
    GRPerturbationBoundShapeCoreStatus

record GRPerturbationBoundShapeCore : Setω where
  field
    carrier :
      Set

    status :
      GRPerturbationBoundShapeCoreStatus

    statusIsFailClosed :
      status ≡ carrierOnlyFailClosed

    christoffelPerturbBoundName :
      String

    christoffelPerturbBoundShape :
      String

    christoffelPerturbationRoute :
      Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt

    christoffelPerturbationRouteIsCanonical :
      christoffelPerturbationRoute
      ≡
      Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt

    christoffelPerturbationTermCount :
      ℕ

    christoffelPerturbationTermCountIs2 :
      christoffelPerturbationTermCount ≡ 2

    christoffelFiniteSlotFactor :
      ℕ

    christoffelFiniteSlotFactorIs4 :
      christoffelFiniteSlotFactor ≡ 4

    christoffelPerturbationSplitExposed :
      Bool

    christoffelPerturbationSplitExposedIsTrue :
      christoffelPerturbationSplitExposed ≡ true

    christoffelFullOrderedQQEstimatePromoted :
      Bool

    christoffelFullOrderedQQEstimatePromotedIsFalse :
      christoffelFullOrderedQQEstimatePromoted ≡ false

    christoffelFormula22Le48 :
      22 ≤ 48

    christoffelFormula22Le48IsCanonical :
      christoffelFormula22Le48
      ≡
      Continuum.symbolicRationalKernelShellAChristoffelFormula22Le48

    ricciBoundName :
      String

    ricciBoundShape :
      String

    ricciPerturbationReceiptReferenced :
      Bool

    ricciPerturbationReceiptReferencedIsTrue :
      ricciPerturbationReceiptReferenced ≡ true

    ricciPerturbationBound :
      ℕ

    ricciPerturbationBoundIs640 :
      ricciPerturbationBound ≡ 640

    ricciTightNumerator :
      ℕ

    ricciTightNumeratorIs112 :
      ricciTightNumerator ≡ 112

    ricciTightDenominator :
      ℕ

    ricciTightDenominatorIs3008 :
      ricciTightDenominator ≡ 3008

    ricciTightRadialPower :
      ℕ

    ricciTightRadialPowerIs27 :
      ricciTightRadialPower ≡ 27

    connectionErrorBoundExtractionDependencyName :
      String

    connectionErrorBoundExtractionDependencyNameIsCanonical :
      connectionErrorBoundExtractionDependencyName
      ≡
      "ContinuumLimitTheorem.SymbolicRationalChristoffelC0StabilityKernel.connectionErrorBoundExtraction"

    ricciConvergencePromoted :
      Bool

    ricciConvergencePromotedIsFalse :
      ricciConvergencePromoted ≡ false

    ricciExternalSchwarzschildAuthorityClaimed :
      Bool

    ricciExternalSchwarzschildAuthorityClaimedIsFalse :
      ricciExternalSchwarzschildAuthorityClaimed ≡ false

    ricciContractedBianchiPromoted :
      Bool

    ricciContractedBianchiPromotedIsFalse :
      ricciContractedBianchiPromoted ≡ false

    ricciContractedBianchiExactBlocker :
      Bianchi.GRDiscreteBianchiFiniteRMissingIngredient

    ricciContractedBianchiExactBlockerIsCarrierConnection :
      ricciContractedBianchiExactBlocker
      ≡
      Bianchi.missingCarrierConnectionIsLeviCivita

    selectedConnectionLeviCivitaDependencyAvailable :
      Bool

    selectedConnectionLeviCivitaDependencyAvailableIsFalse :
      selectedConnectionLeviCivitaDependencyAvailable ≡ false

    selectedConnectionLeviCivitaDependencyName :
      String

    selectedConnectionLeviCivitaDependencyNameIsCanonical :
      selectedConnectionLeviCivitaDependencyName
      ≡
      Bianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.exactSelectedConnectionDependencyName
        Bianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt

    ricciShellA2144Over27Le80Le640Law :
      Ricci.GRDiscreteRicciShellAConstantLawShape

    ricciShellA2144Over27Le80Le640LawIsCanonical :
      ricciShellA2144Over27Le80Le640Law
      ≡
      Ricci.grDiscreteRicciShellA2144Over27≤80Law

    constant22Le48Name :
      String

    constant22Le48Shape :
      String

    constant22Le48Witness :
      22 ≤ 48

    constant22Le48WitnessIsCanonical :
      constant22Le48Witness
      ≡
      Continuum.symbolicRationalKernelShellAChristoffelFormula22Le48

    constant2144Over27Le80Le640Name :
      String

    constant2144Over27Le80Le640Shape :
      String

    christoffelC0InverseMetricClosenessHypothesis :
      String

    christoffelC0InverseMetricClosenessHypothesisIsCanonical :
      christoffelC0InverseMetricClosenessHypothesis
      ≡
      "h_gi"

    christoffelC0StaticHypothesis :
      String

    christoffelC0StaticHypothesisIsCanonical :
      christoffelC0StaticHypothesis
      ≡
      "h_static"

    christoffelC0DiagonalHypothesis :
      String

    christoffelC0DiagonalHypothesisIsCanonical :
      christoffelC0DiagonalHypothesis
      ≡
      "h_diag"

    christoffelC0StaticDiagonalClosenessHypothesis :
      String

    christoffelC0StaticDiagonalClosenessHypothesisIsCanonical :
      christoffelC0StaticDiagonalClosenessHypothesis
      ≡
      "h_static && h_diag"

    christoffelC0DiagonalNonzeroSlotObligation :
      String

    christoffelC0DiagonalNonzeroSlotObligationIsCanonical :
      christoffelC0DiagonalNonzeroSlotObligation
      ≡
      "DiagonalNonzeroSlot?"

    christoffelC0DiagonalZeroLemmaObligation :
      String

    christoffelC0DiagonalZeroLemmaObligationIsCanonical :
      christoffelC0DiagonalZeroLemmaObligation
      ≡
      "diagonalZeroLemma"

    christoffelC0ChristoffelBilinearSplitObligation :
      String

    christoffelC0ChristoffelBilinearSplitObligationIsCanonical :
      christoffelC0ChristoffelBilinearSplitObligation
      ≡
      "christoffelBilinearSplit"

    christoffelC0DiagonalZeroLemmaReceipt :
      String

    christoffelC0DiagonalZeroLemmaReceiptIsCanonical :
      christoffelC0DiagonalZeroLemmaReceipt
      ≡
      "10 explicit nonzero triples / 54 zero triples (symmetric triples counted)"

    christoffelC0DiagonalZeroLemmaNonzeroTripleCount :
      ℕ

    christoffelC0DiagonalZeroLemmaNonzeroTripleCountIs10 :
      christoffelC0DiagonalZeroLemmaNonzeroTripleCount ≡ 10

    christoffelC0DiagonalZeroLemmaZeroTripleCount :
      ℕ

    christoffelC0DiagonalZeroLemmaZeroTripleCountIs54 :
      christoffelC0DiagonalZeroLemmaZeroTripleCount ≡ 54

    christoffelC0DiagonalZeroLemmaSymmetricTripleCount :
      ℕ

    christoffelC0DiagonalZeroLemmaSymmetricTripleCountIs64 :
      christoffelC0DiagonalZeroLemmaSymmetricTripleCount ≡ 64

    christoffelC0ChristoffelBilinearSplitReceipt :
      String

    christoffelC0ChristoffelBilinearSplitReceiptIsCanonical :
      christoffelC0ChristoffelBilinearSplitReceipt
      ≡
      "|δΓ| <= 1/2(|δgi||∂g|+|gi||∂δg|)"

    christoffelC0ChristoffelBilinearSplitStaticDiagonalReceipt :
      String

    christoffelC0ChristoffelBilinearSplitStaticDiagonalReceiptIsCanonical :
      christoffelC0ChristoffelBilinearSplitStaticDiagonalReceipt
      ≡
      "h_static && h_diag"

    christoffelC0ChristoffelBilinearSplitSlackReceipt :
      String

    christoffelC0ChristoffelBilinearSplitSlackReceiptIsCanonical :
      christoffelC0ChristoffelBilinearSplitSlackReceipt
      ≡
      "11/2 ε <= 48 ε"

    christoffelC0StaticDiagonalClosenessHypothesisPromoted :
      Bool

    christoffelC0StaticDiagonalClosenessHypothesisPromotedIsFalse :
      christoffelC0StaticDiagonalClosenessHypothesisPromoted
      ≡
      false

    christoffelC0InverseMetricClosenessSocket :
      (kernel : Continuum.SymbolicRationalChristoffelC0StabilityKernel) →
      Continuum.OrderedRationalShellADenominatorReciprocalReceipt.inverseMetricAbsMax
        (Continuum.SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
          kernel)
      ≡
      4

    christoffelC0InverseMetricClosenessPromoted :
      Bool

    christoffelC0InverseMetricClosenessPromotedIsFalse :
      christoffelC0InverseMetricClosenessPromoted
      ≡
      false

    christoffelC0PerSlotBound :
      String

    christoffelC0PerSlotBoundIsCanonical :
      christoffelC0PerSlotBound
      ≡
      "11/2 ε"

    christoffelC0PerSlotBoundObligation :
      String

    christoffelC0PerSlotBoundObligationIsCanonical :
      christoffelC0PerSlotBoundObligation
      ≡
      "11/2 ε <= 48 ε"

    christoffelC0PerSlotChain :
      String

    christoffelC0PerSlotChainIsCanonical :
      christoffelC0PerSlotChain
      ≡
      OrderedRational.orderedRationalChristoffel16p5Le22Le48ArithmeticChainName

    christoffelFormulaC0StableSurfaceName :
      String

    christoffelFormulaC0StableSurfaceNameIsCanonical :
      christoffelFormulaC0StableSurfaceName
      ≡
      "ChristoffelFormulaC0Stable"

    christoffelFormulaC0StableInverseMetricClosenessName :
      String

    christoffelFormulaC0StableInverseMetricClosenessNameIsCanonical :
      christoffelFormulaC0StableInverseMetricClosenessName
      ≡
      "h_gi"

    christoffelFormulaC0StableZeroSlotLedgerDependencyName :
      String

    christoffelFormulaC0StableZeroSlotLedgerDependencyNameIsCanonical :
      christoffelFormulaC0StableZeroSlotLedgerDependencyName
      ≡
      "diagonalZeroLemma"

    christoffelFormulaC0StableZeroSlotLedgerReceipt :
      String

    christoffelFormulaC0StableZeroSlotLedgerReceiptIsCanonical :
      christoffelFormulaC0StableZeroSlotLedgerReceipt
      ≡
      "10 explicit nonzero triples / 54 zero triples (symmetric triples counted)"

    christoffelFormulaC0StableBilinearSplitReceipt :
      String

    christoffelFormulaC0StableBilinearSplitReceiptIsCanonical :
      christoffelFormulaC0StableBilinearSplitReceipt
      ≡
      "|δΓ| <= 1/2(|δgi||∂g|+|gi||∂δg|)"

    christoffelFormulaC0StableShellAConstantName :
      String

    christoffelFormulaC0StableShellAConstantNameIsCanonical :
      christoffelFormulaC0StableShellAConstantName
      ≡
      "22<=48"

    christoffelFormulaC0StableShellAConstantWitness :
      22 ≤ 48

    christoffelFormulaC0StableShellAConstantWitnessIsCanonical :
      christoffelFormulaC0StableShellAConstantWitness
      ≡
      Continuum.symbolicRationalKernelShellAChristoffelFormula22Le48

    christoffelFormulaC0StableSlackReceipt :
      String

    christoffelFormulaC0StableSlackReceiptIsCanonical :
      christoffelFormulaC0StableSlackReceipt
      ≡
      "11/2 ε <= 48 ε"

    christoffelFormulaC0StablePerSlotBound :
      String

    christoffelFormulaC0StablePerSlotBoundIsCanonical :
      christoffelFormulaC0StablePerSlotBound
      ≡
      "11/2 ε"

    christoffelFormulaC0StablePerSlotBoundObligation :
      String

    christoffelFormulaC0StablePerSlotBoundObligationIsCanonical :
      christoffelFormulaC0StablePerSlotBoundObligation
      ≡
      "11/2 ε <= 48 ε"

    christoffelFormulaC0StableTenNonzeroSlotsName :
      String

    christoffelFormulaC0StableTenNonzeroSlotsNameIsCanonical :
      christoffelFormulaC0StableTenNonzeroSlotsName
      ≡
      "10 nonzero slots"

    christoffelFormulaC0StableSymmetricTripleCountName :
      String

    christoffelFormulaC0StableSymmetricTripleCountNameIsCanonical :
      christoffelFormulaC0StableSymmetricTripleCountName
      ≡
      OrderedRational.coord4SixtyFourTriplesLawName

    christoffelFormulaC0StableTenNonzeroObligation :
      String

    christoffelFormulaC0StableTenNonzeroObligationIsCanonical :
      christoffelFormulaC0StableTenNonzeroObligation
      ≡
      "10 nonzero"

    christoffelFormulaC0StableFiftyFourZeroSlotsName :
      String

    christoffelFormulaC0StableFiftyFourZeroSlotsNameIsCanonical :
      christoffelFormulaC0StableFiftyFourZeroSlotsName
      ≡
      "54 zero slots"

    christoffelFormulaC0StableFiftyFourZeroObligation :
      String

    christoffelFormulaC0StableFiftyFourZeroObligationIsCanonical :
      christoffelFormulaC0StableFiftyFourZeroObligation
      ≡
      "54 zero"

    christoffelFormulaC0StableNonzeroSlotCount :
      ℕ

    christoffelFormulaC0StableNonzeroSlotCountIs10 :
      christoffelFormulaC0StableNonzeroSlotCount ≡ 10

    christoffelFormulaC0StableZeroSlotCount :
      ℕ

    christoffelFormulaC0StableZeroSlotCountIs54 :
      christoffelFormulaC0StableZeroSlotCount ≡ 54

    christoffelFormulaC0StableSymmetricTripleCount :
      ℕ

    christoffelFormulaC0StableSymmetricTripleCountIs64 :
      christoffelFormulaC0StableSymmetricTripleCount ≡ 64

    christoffelFormulaC0StableEpsilonSlack :
      String

    christoffelFormulaC0StableEpsilonSlackIsCanonical :
      christoffelFormulaC0StableEpsilonSlack
      ≡
      "48 ε"

    christoffelFormulaC0StableReceiptPromoted :
      Bool

    christoffelFormulaC0StableReceiptPromotedIsFalse :
      christoffelFormulaC0StableReceiptPromoted
      ≡
      false

    ricciSecondPartialC0DistHypothesis :
      String

    ricciSecondPartialC0DistHypothesisIsCanonical :
      ricciSecondPartialC0DistHypothesis
      ≡
      "h_p2g"

    ricciLoosePgiHypothesis :
      String

    ricciLoosePgiHypothesisIsCanonical :
      ricciLoosePgiHypothesis
      ≡
      "h_pgi"

    ricciLoosePgiHypothesisPromoted :
      Bool

    ricciLoosePgiHypothesisPromotedIsFalse :
      ricciLoosePgiHypothesisPromoted
      ≡
      false

    ricciSecondPartialC0DistSocket :
      (kernel : Continuum.SymbolicRationalChristoffelC0StabilityKernel) →
      Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt.shellAMetricDerivativeMax
        (Continuum.SymbolicRationalChristoffelC0StabilityKernel.orderedShellAPerturbationRoute
          kernel)
      ≡
      Continuum.OrderedRationalShellADenominatorReciprocalReceipt.metricDerivativeAbsMax
        (Continuum.SymbolicRationalChristoffelC0StabilityKernel.shellADenominatorReciprocal
          kernel)

    ricciSecondPartialC0DistPromoted :
      Bool

    ricciSecondPartialC0DistPromotedIsFalse :
      ricciSecondPartialC0DistPromoted
      ≡
      false

    ricciLooseDeltaGammaPartialBound :
      String

    ricciLooseDeltaGammaPartialBoundIsCanonical :
      ricciLooseDeltaGammaPartialBound
      ≡
      "∂δΓ <= 19/2 ε"

    ricciLooseDeltaGammaPartialBoundPromoted :
      Bool

    ricciLooseDeltaGammaPartialBoundPromotedIsFalse :
      ricciLooseDeltaGammaPartialBoundPromoted
      ≡
      false

    ricciLooseDeltaRBound :
      String

    ricciLooseDeltaRBoundIsCanonical :
      ricciLooseDeltaRBound
      ≡
      "δR <= 252 ε"

    ricciLooseDeltaRBoundChain :
      String

    ricciLooseDeltaRBoundChainIsCanonical :
      ricciLooseDeltaRBoundChain
      ≡
      "252 ε <= 640 ε"

    christoffelC0ThirtyTwoLEFortyEightRouteIsAlgebraic :
      Bool

    christoffelC0ThirtyTwoLEFortyEightRouteIsAlgebraicIsTrue :
      christoffelC0ThirtyTwoLEFortyEightRouteIsAlgebraic
      ≡
      true

    christoffelC0ThirtyTwoLEFortyEightRouteWitness :
      22 ≤ 48

    christoffelC0ThirtyTwoLEFortyEightRouteWitnessIsCanonical :
      christoffelC0ThirtyTwoLEFortyEightRouteWitness
      ≡
      Continuum.symbolicRationalKernelShellAChristoffelFormula22Le48

    christoffelC0ThirtyTwoRouteNotInversionRoute :
      String

    christoffelC0ThirtyTwoRouteNotInversionRouteIsCanonical :
      christoffelC0ThirtyTwoRouteNotInversionRoute
      ≡
      "22ε route is algebraic in independent sockets (h_gi, h_pgi, h_p2g, static/diagonal structure), not derived by metric inversion"

    concreteChristoffelTensorFormulaLaw :
      Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt

    concreteChristoffelTensorFormulaLawIsCanonical :
      concreteChristoffelTensorFormulaLaw
      ≡
      Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt

    concreteRicciTensorFormulaLawReferenced :
      Bool

    concreteRicciTensorFormulaLawReferencedIsTrue :
      concreteRicciTensorFormulaLawReferenced ≡ true

    boundary :
      List String

open GRPerturbationBoundShapeCore public

canonicalGRPerturbationBoundShapeCore :
  GRPerturbationBoundShapeCore
canonicalGRPerturbationBoundShapeCore =
  record
    { carrier =
        Bool
    ; status =
        carrierOnlyFailClosed
    ; statusIsFailClosed =
        refl
    ; christoffelPerturbBoundName =
        "ordered-Rational-ShellA-Christoffel-perturbation-route"
    ; christoffelPerturbBoundShape =
        "Conservative/tight Shell A Christoffel perturbation route with finite-slot and split-exposure clauses."
    ; christoffelPerturbationRoute =
        Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
    ; christoffelPerturbationRouteIsCanonical =
        refl
    ; christoffelPerturbationTermCount =
        Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt.perturbationTermCount
          Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
    ; christoffelPerturbationTermCountIs2 =
        Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt.perturbationTermCountIs2
          Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
    ; christoffelFiniteSlotFactor =
        Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt.finiteSumSlotFactor
          Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
    ; christoffelFiniteSlotFactorIs4 =
        Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt.finiteSumSlotFactorIs4
          Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
    ; christoffelPerturbationSplitExposed =
        Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt.perturbationSplitExposed
          Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
    ; christoffelPerturbationSplitExposedIsTrue =
        Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt.perturbationSplitExposedIsTrue
          Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
    ; christoffelFullOrderedQQEstimatePromoted =
        Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt.fullOrderedQQEstimatePromoted
          Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
    ; christoffelFullOrderedQQEstimatePromotedIsFalse =
        Continuum.OrderedRationalShellAChristoffelPerturbationRouteReceipt.fullOrderedQQEstimatePromotedIsFalse
          Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
    ; christoffelFormula22Le48 =
        Continuum.symbolicRationalKernelShellAChristoffelFormula22Le48
    ; christoffelFormula22Le48IsCanonical =
        refl
    ; ricciBoundName =
        "GRSchwarzschildFiniteRicciBianchiPerturbation"
    ; ricciBoundShape =
        "Ricci perturbation bound path through Bianchi/selected-connection dependency with explicit blockers."
    ; ricciPerturbationReceiptReferenced =
        true
    ; ricciPerturbationReceiptReferencedIsTrue =
        refl
    ; ricciPerturbationBound =
        Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.lRicciPerturbationBound
          Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt
    ; ricciPerturbationBoundIs640 =
        Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.lRicciPerturbationBoundIs640
          Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt
    ; ricciTightNumerator =
        Ricci.GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt.tightNumerator
          (Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.tightRicciPerturbationArithmeticReceipt
            Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt)
    ; ricciTightNumeratorIs112 =
        Ricci.GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt.tightNumeratorIs112
          (Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.tightRicciPerturbationArithmeticReceipt
            Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt)
    ; ricciTightDenominator =
        Ricci.GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt.tightDenominator
          (Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.tightRicciPerturbationArithmeticReceipt
            Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt)
    ; ricciTightDenominatorIs3008 =
        Ricci.GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt.tightDenominatorIs3008
          (Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.tightRicciPerturbationArithmeticReceipt
            Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt)
    ; ricciTightRadialPower =
        Ricci.GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt.tightRadialPower
          (Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.tightRicciPerturbationArithmeticReceipt
            Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt)
    ; ricciTightRadialPowerIs27 =
        Ricci.GRSchwarzschildFiniteRicciPerturbationTightArithmeticReceipt.tightRadialPowerIs27
          (Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.tightRicciPerturbationArithmeticReceipt
            Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt)
    ; connectionErrorBoundExtractionDependencyName =
        Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.connectionErrorBoundExtractionDependencyName
          Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt
    ; connectionErrorBoundExtractionDependencyNameIsCanonical =
        Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.connectionErrorBoundExtractionDependencyNameIsCanonical
          Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt
    ; ricciConvergencePromoted =
        Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.ricciPerturbationBoundPromotedAsConvergence
          Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt
    ; ricciConvergencePromotedIsFalse =
        Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.ricciPerturbationBoundPromotedAsConvergenceIsFalse
          Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt
    ; ricciExternalSchwarzschildAuthorityClaimed =
        Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.externalContinuumSchwarzschildAuthorityClaimed
          Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt
    ; ricciExternalSchwarzschildAuthorityClaimedIsFalse =
        Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.externalContinuumSchwarzschildAuthorityClaimedIsFalse
          Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt
    ; ricciContractedBianchiPromoted =
        Bianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.contractedBianchiPromoted
          (Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.contractedBianchiRoute
            Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt)
    ; ricciContractedBianchiPromotedIsFalse =
        Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.contractedBianchiRoutePromoted
          Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt
    ; ricciContractedBianchiExactBlocker =
        Bianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.exactSelectedConnectionDependencyBlocker
          (Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.contractedBianchiRoute
            Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt)
    ; ricciContractedBianchiExactBlockerIsCarrierConnection =
        Bianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.exactSelectedConnectionDependencyBlockerIsCarrierConnectionLeviCivita
          (Ricci.GRSchwarzschildFiniteRicciBianchiPerturbationReceipt.contractedBianchiRoute
            Ricci.canonicalGRSchwarzschildFiniteRicciBianchiPerturbationReceipt)
    ; selectedConnectionLeviCivitaDependencyAvailable =
        Bianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.selectedConnectionLeviCivitaDependencyAvailable
          Bianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; selectedConnectionLeviCivitaDependencyAvailableIsFalse =
        Bianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.selectedConnectionLeviCivitaDependencyAvailableIsFalse
          Bianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; selectedConnectionLeviCivitaDependencyName =
        Bianchi.GRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt.exactSelectedConnectionDependencyName
          Bianchi.canonicalGRGate4ContractedBianchiAfterSelectedLeviCivitaDependencyReceipt
    ; selectedConnectionLeviCivitaDependencyNameIsCanonical =
        refl
    ; ricciShellA2144Over27Le80Le640Law =
        Ricci.grDiscreteRicciShellA2144Over27≤80Law
    ; ricciShellA2144Over27Le80Le640LawIsCanonical =
        refl
    ; constant22Le48Name =
        "22<=48"
    ; constant22Le48Shape =
        "symbolic-rational kernel obstruction lemma: formula 22<=48"
    ; constant22Le48Witness =
        Continuum.symbolicRationalKernelShellAChristoffelFormula22Le48
    ; constant22Le48WitnessIsCanonical =
        refl
    ; constant2144Over27Le80Le640Name =
        "2144/27<=80<=640"
    ; constant2144Over27Le80Le640Shape =
        "Ricci shell-A constant law shape grDiscreteRicciShellA2144Over27≤80Law"
    ; christoffelC0InverseMetricClosenessHypothesis =
        "h_gi"
    ; christoffelC0InverseMetricClosenessHypothesisIsCanonical =
        refl
    ; christoffelC0StaticHypothesis =
        "h_static"
    ; christoffelC0StaticHypothesisIsCanonical =
        refl
    ; christoffelC0DiagonalHypothesis =
        "h_diag"
    ; christoffelC0DiagonalHypothesisIsCanonical =
        refl
    ; christoffelC0StaticDiagonalClosenessHypothesis =
        "h_static && h_diag"
    ; christoffelC0StaticDiagonalClosenessHypothesisIsCanonical =
        refl
    ; christoffelC0DiagonalNonzeroSlotObligation =
        "DiagonalNonzeroSlot?"
    ; christoffelC0DiagonalNonzeroSlotObligationIsCanonical =
        refl
    ; christoffelC0DiagonalZeroLemmaObligation =
        "diagonalZeroLemma"
    ; christoffelC0DiagonalZeroLemmaObligationIsCanonical =
        refl
    ; christoffelC0ChristoffelBilinearSplitObligation =
        "christoffelBilinearSplit"
    ; christoffelC0ChristoffelBilinearSplitObligationIsCanonical =
        refl
    ; christoffelC0DiagonalZeroLemmaReceipt =
        "10 explicit nonzero triples / 54 zero triples (symmetric triples counted)"
    ; christoffelC0DiagonalZeroLemmaReceiptIsCanonical =
        refl
    ; christoffelC0DiagonalZeroLemmaNonzeroTripleCount =
        10
    ; christoffelC0DiagonalZeroLemmaNonzeroTripleCountIs10 =
        refl
    ; christoffelC0DiagonalZeroLemmaZeroTripleCount =
        54
    ; christoffelC0DiagonalZeroLemmaZeroTripleCountIs54 =
        refl
    ; christoffelC0DiagonalZeroLemmaSymmetricTripleCount =
        64
    ; christoffelC0DiagonalZeroLemmaSymmetricTripleCountIs64 =
        refl
    ; christoffelC0ChristoffelBilinearSplitReceipt =
        "|δΓ| <= 1/2(|δgi||∂g|+|gi||∂δg|)"
    ; christoffelC0ChristoffelBilinearSplitReceiptIsCanonical =
        refl
    ; christoffelC0ChristoffelBilinearSplitStaticDiagonalReceipt =
        "h_static && h_diag"
    ; christoffelC0ChristoffelBilinearSplitStaticDiagonalReceiptIsCanonical =
        refl
    ; christoffelC0ChristoffelBilinearSplitSlackReceipt =
        "11/2 ε <= 48 ε"
    ; christoffelC0ChristoffelBilinearSplitSlackReceiptIsCanonical =
        refl
    ; christoffelC0StaticDiagonalClosenessHypothesisPromoted =
        false
    ; christoffelC0StaticDiagonalClosenessHypothesisPromotedIsFalse =
        refl
    ; christoffelC0InverseMetricClosenessSocket =
        Continuum.symbolicRationalKernelShellAInverseMetricAbsMaxIs4
    ; christoffelC0InverseMetricClosenessPromoted =
        false
    ; christoffelC0InverseMetricClosenessPromotedIsFalse =
        refl
    ; christoffelC0PerSlotBound =
        "11/2 ε"
    ; christoffelC0PerSlotBoundIsCanonical =
        refl
    ; christoffelC0PerSlotBoundObligation =
        "11/2 ε <= 48 ε"
    ; christoffelC0PerSlotBoundObligationIsCanonical =
        refl
    ; christoffelC0PerSlotChain =
        OrderedRational.orderedRationalChristoffel16p5Le22Le48ArithmeticChainName
    ; christoffelC0PerSlotChainIsCanonical =
        refl
    ; christoffelFormulaC0StableSurfaceName =
        "ChristoffelFormulaC0Stable"
    ; christoffelFormulaC0StableSurfaceNameIsCanonical =
        refl
    ; christoffelFormulaC0StableInverseMetricClosenessName =
        "h_gi"
    ; christoffelFormulaC0StableInverseMetricClosenessNameIsCanonical =
        refl
    ; christoffelFormulaC0StableZeroSlotLedgerDependencyName =
        "diagonalZeroLemma"
    ; christoffelFormulaC0StableZeroSlotLedgerDependencyNameIsCanonical =
        refl
    ; christoffelFormulaC0StableZeroSlotLedgerReceipt =
        "10 explicit nonzero triples / 54 zero triples (symmetric triples counted)"
    ; christoffelFormulaC0StableZeroSlotLedgerReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableBilinearSplitReceipt =
        "|δΓ| <= 1/2(|δgi||∂g|+|gi||∂δg|)"
    ; christoffelFormulaC0StableBilinearSplitReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableShellAConstantName =
        "22<=48"
    ; christoffelFormulaC0StableShellAConstantNameIsCanonical =
        refl
    ; christoffelFormulaC0StableShellAConstantWitness =
        Continuum.symbolicRationalKernelShellAChristoffelFormula22Le48
    ; christoffelFormulaC0StableShellAConstantWitnessIsCanonical =
        refl
    ; christoffelFormulaC0StableSlackReceipt =
        "11/2 ε <= 48 ε"
    ; christoffelFormulaC0StableSlackReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StablePerSlotBound =
        "11/2 ε"
    ; christoffelFormulaC0StablePerSlotBoundIsCanonical =
        refl
    ; christoffelFormulaC0StablePerSlotBoundObligation =
        "11/2 ε <= 48 ε"
    ; christoffelFormulaC0StablePerSlotBoundObligationIsCanonical =
        refl
    ; christoffelFormulaC0StableTenNonzeroSlotsName =
        "10 nonzero slots"
    ; christoffelFormulaC0StableTenNonzeroSlotsNameIsCanonical =
        refl
    ; christoffelFormulaC0StableSymmetricTripleCountName =
        OrderedRational.coord4SixtyFourTriplesLawName
    ; christoffelFormulaC0StableSymmetricTripleCountNameIsCanonical =
        refl
    ; christoffelFormulaC0StableTenNonzeroObligation =
        "10 nonzero"
    ; christoffelFormulaC0StableTenNonzeroObligationIsCanonical =
        refl
    ; christoffelFormulaC0StableFiftyFourZeroSlotsName =
        "54 zero slots"
    ; christoffelFormulaC0StableFiftyFourZeroSlotsNameIsCanonical =
        refl
    ; christoffelFormulaC0StableFiftyFourZeroObligation =
        "54 zero"
    ; christoffelFormulaC0StableFiftyFourZeroObligationIsCanonical =
        refl
    ; christoffelFormulaC0StableNonzeroSlotCount =
        10
    ; christoffelFormulaC0StableNonzeroSlotCountIs10 =
        refl
    ; christoffelFormulaC0StableZeroSlotCount =
        54
    ; christoffelFormulaC0StableZeroSlotCountIs54 =
        refl
    ; christoffelFormulaC0StableSymmetricTripleCount =
        64
    ; christoffelFormulaC0StableSymmetricTripleCountIs64 =
        refl
    ; christoffelFormulaC0StableEpsilonSlack =
        "48 ε"
    ; christoffelFormulaC0StableEpsilonSlackIsCanonical =
        refl
    ; christoffelFormulaC0StableReceiptPromoted =
        false
    ; christoffelFormulaC0StableReceiptPromotedIsFalse =
        refl
    ; ricciSecondPartialC0DistHypothesis =
        "h_p2g"
    ; ricciSecondPartialC0DistHypothesisIsCanonical =
        refl
    ; ricciLoosePgiHypothesis =
        "h_pgi"
    ; ricciLoosePgiHypothesisIsCanonical =
        refl
    ; ricciLoosePgiHypothesisPromoted =
        false
    ; ricciLoosePgiHypothesisPromotedIsFalse =
        refl
    ; ricciSecondPartialC0DistSocket =
        Continuum.symbolicRationalKernelPerturbationRouteDerivativeMaxMatchesDenominatorReceipt
    ; ricciSecondPartialC0DistPromoted =
        false
    ; ricciSecondPartialC0DistPromotedIsFalse =
        refl
    ; ricciLooseDeltaGammaPartialBound =
        "∂δΓ <= 19/2 ε"
    ; ricciLooseDeltaGammaPartialBoundIsCanonical =
        refl
    ; ricciLooseDeltaGammaPartialBoundPromoted =
        false
    ; ricciLooseDeltaGammaPartialBoundPromotedIsFalse =
        refl
    ; ricciLooseDeltaRBound =
        "δR <= 252 ε"
    ; ricciLooseDeltaRBoundIsCanonical =
        refl
    ; ricciLooseDeltaRBoundChain =
        "252 ε <= 640 ε"
    ; ricciLooseDeltaRBoundChainIsCanonical =
        refl
    ; christoffelC0ThirtyTwoLEFortyEightRouteIsAlgebraic =
        true
    ; christoffelC0ThirtyTwoLEFortyEightRouteIsAlgebraicIsTrue =
        refl
    ; christoffelC0ThirtyTwoLEFortyEightRouteWitness =
        Continuum.symbolicRationalKernelShellAChristoffelFormula22Le48
    ; christoffelC0ThirtyTwoLEFortyEightRouteWitnessIsCanonical =
        refl
    ; christoffelC0ThirtyTwoRouteNotInversionRoute =
        "22ε route is algebraic in independent sockets (h_gi, h_pgi, h_p2g, static/diagonal structure), not derived by metric inversion"
    ; christoffelC0ThirtyTwoRouteNotInversionRouteIsCanonical =
        refl
    ; concreteChristoffelTensorFormulaLaw =
        Continuum.canonicalOrderedRationalShellAChristoffelPerturbationRouteReceipt
    ; concreteChristoffelTensorFormulaLawIsCanonical =
        refl
    ; concreteRicciTensorFormulaLawReferenced =
        true
    ; concreteRicciTensorFormulaLawReferencedIsTrue =
        refl
    ; boundary =
        "This module is carrier/receipt only and fail-closed."
        ∷ "Christoffel perturbation caveat: two-term split exposed at the linearization level; four-slot finite sum factor; no promotion of full ordered QQ estimate."
        ∷ "Per-slot algebraic control is recorded as 11/2 ε and the explicit next inequality 11/2 ε <= 48 ε."
        ∷ "DiagonalZeroLemma and christoffelBilinearSplit are recorded with h_static && h_diag, 10 explicit nonzero triples, 54 zero triples, and the exact bilinear split |δΓ| <= 1/2(|δgi||∂g|+|gi||∂δg|)."
        ∷ "ChristoffelFormulaC0Stable now exposes concrete receipt names for independent inverse-metric closeness, zero-slot ledger dependency, the bilinear split, Shell A constant 22<=48, and the 11/2 ε <= 48 ε slack gate."
        ∷ "Ricci perturbation route is carried by the canonical Schwarzschild finite Ricci/Bianchi receipt; convergence and authority promotions are blocked."
        ∷ "Contracted-Bianchi still blocks at selected-connection dependency with exact blocker: missingCarrierConnectionIsLeviCivita."
        ∷ "Exact boundary arithmetic shapes are carried by symbolic-rational and shell-A law shapes, not by fabricated proofs."
        ∷ "Theorem-socket h_gi is recorded via symbolicRationalKernelShellAInverseMetricAbsMaxIs4 and is typed as a kernel-level inverse-metric max witness."
        ∷ "Theorem-socket h_static is recorded as a canonical static-hypothesis receipt."
        ∷ "Theorem-socket h_diag is recorded as a canonical diagonal-hypothesis receipt."
        ∷ "Theorem-socket h_p2g is recorded via symbolicRationalKernelPerturbationRouteDerivativeMaxMatchesDenominatorReceipt and is typed as the route derivative-max matching witness."
        ∷ "Structural sockets for the Christoffel-C0 correction route additionally record the separate static and diagonal assumptions plus the diagonal/nonzero split obligations and the 11/2 ε <= 48 ε slack gate."
        ∷ "Ricci loose route hypotheses now include h_pgi and h_p2g; the derivative control is logged as ∂δΓ <= 19/2 ε with loose Ricci control δR <= 252 ε <= 640 ε."
        ∷ "The 22ε route is explicitly marked algebraic in independent inputs, not a metric inversion argument."
        ∷ []
    }
