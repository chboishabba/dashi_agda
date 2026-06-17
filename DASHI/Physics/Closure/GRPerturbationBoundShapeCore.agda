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
      "13 explicit nonzero triples / 51 zero triples (symmetric triples counted)"

    christoffelC0GammaChristoffelDiagonalName :
      String

    christoffelC0GammaChristoffelDiagonalNameIsCanonical :
      christoffelC0GammaChristoffelDiagonalName
      ≡
      "Γ_christoffel_diagonal"

    christoffelC0GammaChristoffelDiagonalReceipt :
      String

    christoffelC0GammaChristoffelDiagonalReceiptIsCanonical :
      christoffelC0GammaChristoffelDiagonalReceipt
      ≡
      "diagonalZeroLemma <- [bracket_zero_of_not_nonzero, partialDeriv_of_zero]"

    christoffelC0DiagonalZeroLemmaNonzeroTripleCount :
      ℕ

    christoffelC0DiagonalZeroLemmaNonzeroTripleCountIs10 :
      christoffelC0DiagonalZeroLemmaNonzeroTripleCount ≡ 13

    christoffelC0DiagonalZeroLemmaZeroTripleCount :
      ℕ

    christoffelC0DiagonalZeroLemmaZeroTripleCountIs54 :
      christoffelC0DiagonalZeroLemmaZeroTripleCount ≡ 51

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

    christoffelC0ShellABracketLe8RouteName :
      String

    christoffelC0ShellABracketLe8RouteNameIsCanonical :
      christoffelC0ShellABracketLe8RouteName
      ≡
      "bracket_le=8"

    christoffelC0ShellABracketLe8RouteReceipt :
      String

    christoffelC0ShellABracketLe8RouteReceiptIsCanonical :
      christoffelC0ShellABracketLe8RouteReceipt
      ≡
      "bracket_le=8 is valid only for r_max=4M (M=1 units), with bracket_le = 2*r_max; theta-shell/cot-bound required for the new angular slots"

    christoffelC0ShellAFallbackThreeTermRouteName :
      String

    christoffelC0ShellAFallbackThreeTermRouteNameIsCanonical :
      christoffelC0ShellAFallbackThreeTermRouteName
      ≡
      "fallback 3-term route"

    christoffelC0ShellAFallbackThreeTermRouteReceipt :
      String

    christoffelC0ShellAFallbackThreeTermRouteReceiptIsCanonical :
      christoffelC0ShellAFallbackThreeTermRouteReceipt
      ≡
      "(1/2)(24ε+3ε)=27/2ε, 27/2<=22"

    christoffelC0ShellAConservativeRouteName :
      String

    christoffelC0ShellAConservativeRouteNameIsCanonical :
      christoffelC0ShellAConservativeRouteName
      ≡
      "33/2<=22<=48"

    christoffelC0ShellAConservativeRouteReceipt :
      String

    christoffelC0ShellAConservativeRouteReceiptIsCanonical :
      christoffelC0ShellAConservativeRouteReceipt
      ≡
      "33/2 <= 22 <= 48"

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

    christoffelFormulaC0StableInverseMetricMax :
      ℕ

    christoffelFormulaC0StableInverseMetricMaxIs3 :
      christoffelFormulaC0StableInverseMetricMax ≡ 3

    christoffelFormulaC0StableMetricDerivativeMax :
      ℕ

    christoffelFormulaC0StableMetricDerivativeMaxIs8 :
      christoffelFormulaC0StableMetricDerivativeMax ≡ 8

    christoffelFormulaC0StableBilinearSplitExposed :
      Bool

    christoffelFormulaC0StableBilinearSplitExposedIsTrue :
      christoffelFormulaC0StableBilinearSplitExposed ≡ true

    christoffelFormulaC0StableZeroSlotLedgerDependencyName :
      String

    christoffelFormulaC0StableZeroSlotLedgerDependencyNameIsCanonical :
      christoffelFormulaC0StableZeroSlotLedgerDependencyName
      ≡
      "diagonalZeroLemma"

    christoffelFormulaC0StableZeroSlotLedgerDependencyReceipt :
      String

    christoffelFormulaC0StableZeroSlotLedgerDependencyReceiptIsCanonical :
      christoffelFormulaC0StableZeroSlotLedgerDependencyReceipt
      ≡
      christoffelC0DiagonalZeroLemmaReceipt

    christoffelFormulaC0StableZeroSlotLedgerReceipt :
      String

    christoffelFormulaC0StableZeroSlotLedgerReceiptIsCanonical :
      christoffelFormulaC0StableZeroSlotLedgerReceipt
      ≡
      "13 explicit nonzero triples / 51 zero triples (symmetric triples counted)"

    christoffelFormulaC0StableZeroSlotDependencyName :
      String

    christoffelFormulaC0StableZeroSlotDependencyNameIsCanonical :
      christoffelFormulaC0StableZeroSlotDependencyName
      ≡
      "diagonalZeroLemma"

    christoffelFormulaC0StableZeroSlotDependencyReceipt :
      String

    christoffelFormulaC0StableZeroSlotDependencyReceiptIsCanonical :
      christoffelFormulaC0StableZeroSlotDependencyReceipt
      ≡
      christoffelC0DiagonalZeroLemmaReceipt

    christoffelFormulaC0StableBracketZeroOfNotNonzeroDependencyName :
      String

    christoffelFormulaC0StableBracketZeroOfNotNonzeroDependencyNameIsCanonical :
      christoffelFormulaC0StableBracketZeroOfNotNonzeroDependencyName
      ≡
      "bracket_zero_of_not_nonzero"

    christoffelFormulaC0StablePartialDerivOfZeroDependencyName :
      String

    christoffelFormulaC0StablePartialDerivOfZeroDependencyNameIsCanonical :
      christoffelFormulaC0StablePartialDerivOfZeroDependencyName
      ≡
      "partialDeriv_of_zero"

    christoffelFormulaC0StableDiagonalZeroLemmaDependencyChainName :
      String

    christoffelFormulaC0StableDiagonalZeroLemmaDependencyChainNameIsCanonical :
      christoffelFormulaC0StableDiagonalZeroLemmaDependencyChainName
      ≡
      "diagonalZeroLemma dependency chain"

    christoffelFormulaC0StableDiagonalZeroLemmaDependencyChainReceipt :
      String

    christoffelFormulaC0StableDiagonalZeroLemmaDependencyChainReceiptIsCanonical :
      christoffelFormulaC0StableDiagonalZeroLemmaDependencyChainReceipt
      ≡
      "diagonalZeroLemma <- [bracket_zero_of_not_nonzero, partialDeriv_of_zero]"

    christoffelFormulaC0StableGammaChristoffelDiagonalDependencyName :
      String

    christoffelFormulaC0StableGammaChristoffelDiagonalDependencyNameIsCanonical :
      christoffelFormulaC0StableGammaChristoffelDiagonalDependencyName
      ≡
      "Γ_christoffel_diagonal"

    christoffelFormulaC0StableGammaChristoffelDiagonalDependencyReceipt :
      String

    christoffelFormulaC0StableGammaChristoffelDiagonalDependencyReceiptIsCanonical :
      christoffelFormulaC0StableGammaChristoffelDiagonalDependencyReceipt
      ≡
      "diagonalZeroLemma <- [bracket_zero_of_not_nonzero, partialDeriv_of_zero]"

    christoffelFormulaC0StableBilinearSplitReceipt :
      String

    christoffelFormulaC0StableBilinearSplitReceiptIsCanonical :
      christoffelFormulaC0StableBilinearSplitReceipt
      ≡
      "|δΓ| <= 1/2(|δgi||∂g|+|gi||∂δg|)"

    christoffelFormulaC0StableBilinearSplitDependencyName :
      String

    christoffelFormulaC0StableBilinearSplitDependencyNameIsCanonical :
      christoffelFormulaC0StableBilinearSplitDependencyName
      ≡
      "christoffelBilinearSplit"

    christoffelFormulaC0StableBilinearSplitDependencyReceipt :
      String

    christoffelFormulaC0StableBilinearSplitDependencyReceiptIsCanonical :
      christoffelFormulaC0StableBilinearSplitDependencyReceipt
      ≡
      christoffelC0ChristoffelBilinearSplitReceipt

    christoffelFormulaC0StableChristoffelBilinearSplitTelescopingIdentityName :
      String

    christoffelFormulaC0StableChristoffelBilinearSplitTelescopingIdentityNameIsCanonical :
      christoffelFormulaC0StableChristoffelBilinearSplitTelescopingIdentityName
      ≡
      "christoffelBilinearSplit telescoping identity"

    christoffelFormulaC0StableChristoffelBilinearSplitTelescopingIdentityReceipt :
      String

    christoffelFormulaC0StableChristoffelBilinearSplitTelescopingIdentityReceiptIsCanonical :
      christoffelFormulaC0StableChristoffelBilinearSplitTelescopingIdentityReceipt
      ≡
      "telescoping decomposition gives |δΓ| <= 1/2(|δgi||∂g|+|gi||∂δg|)"

    christoffelFormulaC0StableFeed11HalfTo22ChainName :
      String

    christoffelFormulaC0StableFeed11HalfTo22ChainNameIsCanonical :
      christoffelFormulaC0StableFeed11HalfTo22ChainName
      ≡
      OrderedRational.orderedRationalChristoffel16p5Le22Le48ArithmeticChainName

    christoffelFormulaC0StableFeed11HalfTo22ChainReceipt :
      String

    christoffelFormulaC0StableFeed11HalfTo22ChainReceiptIsCanonical :
      christoffelFormulaC0StableFeed11HalfTo22ChainReceipt
      ≡
      "11/2<=33/2<=22<=48"

    christoffelFormulaC0StableShellABracketLe8RouteName :
      String

    christoffelFormulaC0StableShellABracketLe8RouteNameIsCanonical :
      christoffelFormulaC0StableShellABracketLe8RouteName
      ≡
      "bracket_le=8"

    christoffelFormulaC0StableShellABracketLe8RouteReceipt :
      String

    christoffelFormulaC0StableShellABracketLe8RouteReceiptIsCanonical :
      christoffelFormulaC0StableShellABracketLe8RouteReceipt
      ≡
      "bracket_le=8 is valid only for r_max=4M (M=1 units), with bracket_le = 2*r_max; theta-shell/cot-bound required for the new angular slots"

    christoffelFormulaC0StableShellAFallbackThreeTermRouteName :
      String

    christoffelFormulaC0StableShellAFallbackThreeTermRouteNameIsCanonical :
      christoffelFormulaC0StableShellAFallbackThreeTermRouteName
      ≡
      "fallback 3-term route"

    christoffelFormulaC0StableShellAFallbackThreeTermRouteReceipt :
      String

    christoffelFormulaC0StableShellAFallbackThreeTermRouteReceiptIsCanonical :
      christoffelFormulaC0StableShellAFallbackThreeTermRouteReceipt
      ≡
      "(1/2)(24ε+3ε)=27/2ε, 27/2<=22"

    christoffelFormulaC0StableShellAConservativeRouteName :
      String

    christoffelFormulaC0StableShellAConservativeRouteNameIsCanonical :
      christoffelFormulaC0StableShellAConservativeRouteName
      ≡
      "33/2<=22<=48"

    christoffelFormulaC0StableShellAConservativeRouteReceipt :
      String

    christoffelFormulaC0StableShellAConservativeRouteReceiptIsCanonical :
      christoffelFormulaC0StableShellAConservativeRouteReceipt
      ≡
      "33/2 <= 22 <= 48"

    christoffelFormulaC0StableFeed27Over2To22ChainName :
      String

    christoffelFormulaC0StableFeed27Over2To22ChainNameIsCanonical :
      christoffelFormulaC0StableFeed27Over2To22ChainName
      ≡
      OrderedRational.orderedRationalChristoffel27Over2Le22ArithmeticChainName

    christoffelFormulaC0StableFeed27Over2To22ChainReceipt :
      String

    christoffelFormulaC0StableFeed27Over2To22ChainReceiptIsCanonical :
      christoffelFormulaC0StableFeed27Over2To22ChainReceipt
      ≡
      "(1/2)(24ε+3ε)=27/2ε, 27/2<=22"

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

    christoffelFormulaC0StableShellAInverseMetricMax :
      ℕ

    christoffelFormulaC0StableShellAInverseMetricMaxIs3 :
      christoffelFormulaC0StableShellAInverseMetricMax ≡ 3

    christoffelFormulaC0StableShellAMetricDerivativeMax :
      ℕ

    christoffelFormulaC0StableShellAMetricDerivativeMaxIs8 :
      christoffelFormulaC0StableShellAMetricDerivativeMax ≡ 8

    christoffelFormulaC0StableShellALegacyLGamma :
      ℕ

    christoffelFormulaC0StableShellALegacyLGammaIs72 :
      christoffelFormulaC0StableShellALegacyLGamma ≡ 72

    christoffelFormulaC0StableShellAConservativeLGamma :
      ℕ

    christoffelFormulaC0StableShellAConservativeLGammaIs48 :
      christoffelFormulaC0StableShellAConservativeLGamma ≡ 48

    christoffelFormulaC0StableShellATightLGamma :
      ℕ

    christoffelFormulaC0StableShellATightLGammaIs44 :
      christoffelFormulaC0StableShellATightLGamma ≡ 44

    christoffelFormulaC0StableReceiptTable :
      List String

    christoffelFormulaC0StableReceiptTableIsCanonical :
      christoffelFormulaC0StableReceiptTable
      ≡
      "zero-slot dependency: diagonalZeroLemma"
      ∷ "zero-slot receipt: 13 explicit nonzero triples / 51 zero triples (symmetric triples counted)"
      ∷ "bilinear split dependency: christoffelBilinearSplit"
      ∷ "bilinear split receipt: |δΓ| <= 1/2(|δgi||∂g|+|gi||∂δg|)"
      ∷ "diagonalZeroLemma dependency chain: diagonalZeroLemma <- [bracket_zero_of_not_nonzero, partialDeriv_of_zero]"
      ∷ "Γ_christoffel_diagonal dependency: diagonalZeroLemma <- [bracket_zero_of_not_nonzero, partialDeriv_of_zero]"
      ∷ "christoffelBilinearSplit telescoping identity: telescoping decomposition gives |δΓ| <= 1/2(|δgi||∂g|+|gi||∂δg|)"
      ∷ "11/2 feed to 22: 11/2<=33/2<=22<=48"
      ∷ "27/2 feed to 22 (3-term bracket): (1/2)(24ε+3ε)=27/2ε, 27/2<=22"
      ∷ "direct Shell A bracket_le=8 route: bracket_le=8 is valid only for r_max=4M (M=1 units), with bracket_le = 2*r_max; theta-shell/cot-bound required for the new angular slots"
      ∷ "fallback 3-term route: (1/2)(24ε+3ε)=27/2ε, 27/2<=22"
      ∷ "conservative route: 33/2 <= 22 <= 48"
      ∷ "Shell A constants: inverseMetricMax=3, metricDerivativeMax=8, conservative L_Gamma=48, tight L_Gamma=44, legacy envelope=72"
      ∷ []

    christoffelFormulaC0StableSlackReceipt :
      String

    christoffelFormulaC0StableSlackReceiptIsCanonical :
      christoffelFormulaC0StableSlackReceipt
      ≡
      "11/2 ε <= 48 ε"

    christoffelFormulaC0StableSlackArithmeticChainName :
      String

    christoffelFormulaC0StableSlackArithmeticChainNameIsCanonical :
      christoffelFormulaC0StableSlackArithmeticChainName
      ≡
      OrderedRational.orderedRationalChristoffel16p5Le22Le48ArithmeticChainName

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

    christoffelFormulaC0StableSafePerSlotBound :
      String

    christoffelFormulaC0StableSafePerSlotBoundIsCanonical :
      christoffelFormulaC0StableSafePerSlotBound
      ≡
      "27/2 ε"

    christoffelFormulaC0StableSafePerSlotBoundObligation :
      String

    christoffelFormulaC0StableSafePerSlotBoundObligationIsCanonical :
      christoffelFormulaC0StableSafePerSlotBoundObligation
      ≡
      "27/2 ε <= 48 ε"

    christoffelFormulaC0StableTenNonzeroSlotsName :
      String

    christoffelFormulaC0StableTenNonzeroSlotsNameIsCanonical :
      christoffelFormulaC0StableTenNonzeroSlotsName
      ≡
      "13 nonzero slots"

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
      "13 nonzero"

    christoffelFormulaC0StableFiftyFourZeroSlotsName :
      String

    christoffelFormulaC0StableFiftyFourZeroSlotsNameIsCanonical :
      christoffelFormulaC0StableFiftyFourZeroSlotsName
      ≡
      "51 zero slots"

    christoffelFormulaC0StableFiftyFourZeroObligation :
      String

    christoffelFormulaC0StableFiftyFourZeroObligationIsCanonical :
      christoffelFormulaC0StableFiftyFourZeroObligation
      ≡
      "51 zero"

    christoffelFormulaC0StableNonzeroSlotCount :
      ℕ

    christoffelFormulaC0StableNonzeroSlotCountIs10 :
      christoffelFormulaC0StableNonzeroSlotCount ≡ 13

    christoffelFormulaC0StableZeroSlotCount :
      ℕ

    christoffelFormulaC0StableZeroSlotCountIs54 :
      christoffelFormulaC0StableZeroSlotCount ≡ 51

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
        "13 explicit nonzero triples / 51 zero triples (symmetric triples counted)"
    ; christoffelC0DiagonalZeroLemmaReceiptIsCanonical =
        refl
    ; christoffelC0GammaChristoffelDiagonalName =
        "Γ_christoffel_diagonal"
    ; christoffelC0GammaChristoffelDiagonalNameIsCanonical =
        refl
    ; christoffelC0GammaChristoffelDiagonalReceipt =
        "diagonalZeroLemma <- [bracket_zero_of_not_nonzero, partialDeriv_of_zero]"
    ; christoffelC0GammaChristoffelDiagonalReceiptIsCanonical =
        refl
    ; christoffelC0DiagonalZeroLemmaNonzeroTripleCount =
        13
    ; christoffelC0DiagonalZeroLemmaNonzeroTripleCountIs10 =
        refl
    ; christoffelC0DiagonalZeroLemmaZeroTripleCount =
        51
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
    ; christoffelC0ShellABracketLe8RouteName =
        "bracket_le=8"
    ; christoffelC0ShellABracketLe8RouteNameIsCanonical =
        refl
    ; christoffelC0ShellABracketLe8RouteReceipt =
        "bracket_le=8 is valid only for r_max=4M (M=1 units), with bracket_le = 2*r_max; theta-shell/cot-bound required for the new angular slots"
    ; christoffelC0ShellABracketLe8RouteReceiptIsCanonical =
        refl
    ; christoffelC0ShellAFallbackThreeTermRouteName =
        "fallback 3-term route"
    ; christoffelC0ShellAFallbackThreeTermRouteNameIsCanonical =
        refl
    ; christoffelC0ShellAFallbackThreeTermRouteReceipt =
        "(1/2)(24ε+3ε)=27/2ε, 27/2<=22"
    ; christoffelC0ShellAFallbackThreeTermRouteReceiptIsCanonical =
        refl
    ; christoffelC0ShellAConservativeRouteName =
        "33/2<=22<=48"
    ; christoffelC0ShellAConservativeRouteNameIsCanonical =
        refl
    ; christoffelC0ShellAConservativeRouteReceipt =
        "33/2 <= 22 <= 48"
    ; christoffelC0ShellAConservativeRouteReceiptIsCanonical =
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
    ; christoffelFormulaC0StableInverseMetricMax =
        3
    ; christoffelFormulaC0StableInverseMetricMaxIs3 =
        refl
    ; christoffelFormulaC0StableMetricDerivativeMax =
        8
    ; christoffelFormulaC0StableMetricDerivativeMaxIs8 =
        refl
    ; christoffelFormulaC0StableBilinearSplitExposed =
        true
    ; christoffelFormulaC0StableBilinearSplitExposedIsTrue =
        refl
    ; christoffelFormulaC0StableZeroSlotLedgerDependencyName =
        "diagonalZeroLemma"
    ; christoffelFormulaC0StableZeroSlotLedgerDependencyNameIsCanonical =
        refl
    ; christoffelFormulaC0StableZeroSlotLedgerDependencyReceipt =
        "13 explicit nonzero triples / 51 zero triples (symmetric triples counted)"
    ; christoffelFormulaC0StableZeroSlotLedgerDependencyReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableZeroSlotLedgerReceipt =
        "13 explicit nonzero triples / 51 zero triples (symmetric triples counted)"
    ; christoffelFormulaC0StableZeroSlotLedgerReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableZeroSlotDependencyName =
        "diagonalZeroLemma"
    ; christoffelFormulaC0StableZeroSlotDependencyNameIsCanonical =
        refl
    ; christoffelFormulaC0StableZeroSlotDependencyReceipt =
        "13 explicit nonzero triples / 51 zero triples (symmetric triples counted)"
    ; christoffelFormulaC0StableZeroSlotDependencyReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableBracketZeroOfNotNonzeroDependencyName =
        "bracket_zero_of_not_nonzero"
    ; christoffelFormulaC0StableBracketZeroOfNotNonzeroDependencyNameIsCanonical =
        refl
    ; christoffelFormulaC0StablePartialDerivOfZeroDependencyName =
        "partialDeriv_of_zero"
    ; christoffelFormulaC0StablePartialDerivOfZeroDependencyNameIsCanonical =
        refl
    ; christoffelFormulaC0StableDiagonalZeroLemmaDependencyChainName =
        "diagonalZeroLemma dependency chain"
    ; christoffelFormulaC0StableDiagonalZeroLemmaDependencyChainNameIsCanonical =
        refl
    ; christoffelFormulaC0StableDiagonalZeroLemmaDependencyChainReceipt =
        "diagonalZeroLemma <- [bracket_zero_of_not_nonzero, partialDeriv_of_zero]"
    ; christoffelFormulaC0StableDiagonalZeroLemmaDependencyChainReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableGammaChristoffelDiagonalDependencyName =
        "Γ_christoffel_diagonal"
    ; christoffelFormulaC0StableGammaChristoffelDiagonalDependencyNameIsCanonical =
        refl
    ; christoffelFormulaC0StableGammaChristoffelDiagonalDependencyReceipt =
        "diagonalZeroLemma <- [bracket_zero_of_not_nonzero, partialDeriv_of_zero]"
    ; christoffelFormulaC0StableGammaChristoffelDiagonalDependencyReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableBilinearSplitReceipt =
        "|δΓ| <= 1/2(|δgi||∂g|+|gi||∂δg|)"
    ; christoffelFormulaC0StableBilinearSplitReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableBilinearSplitDependencyName =
        "christoffelBilinearSplit"
    ; christoffelFormulaC0StableBilinearSplitDependencyNameIsCanonical =
        refl
    ; christoffelFormulaC0StableBilinearSplitDependencyReceipt =
        "|δΓ| <= 1/2(|δgi||∂g|+|gi||∂δg|)"
    ; christoffelFormulaC0StableBilinearSplitDependencyReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableChristoffelBilinearSplitTelescopingIdentityName =
        "christoffelBilinearSplit telescoping identity"
    ; christoffelFormulaC0StableChristoffelBilinearSplitTelescopingIdentityNameIsCanonical =
        refl
    ; christoffelFormulaC0StableChristoffelBilinearSplitTelescopingIdentityReceipt =
        "telescoping decomposition gives |δΓ| <= 1/2(|δgi||∂g|+|gi||∂δg|)"
    ; christoffelFormulaC0StableChristoffelBilinearSplitTelescopingIdentityReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableFeed11HalfTo22ChainName =
        OrderedRational.orderedRationalChristoffel16p5Le22Le48ArithmeticChainName
    ; christoffelFormulaC0StableFeed11HalfTo22ChainNameIsCanonical =
        refl
    ; christoffelFormulaC0StableFeed11HalfTo22ChainReceipt =
        "11/2<=33/2<=22<=48"
    ; christoffelFormulaC0StableFeed11HalfTo22ChainReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableShellABracketLe8RouteName =
        "bracket_le=8"
    ; christoffelFormulaC0StableShellABracketLe8RouteNameIsCanonical =
        refl
    ; christoffelFormulaC0StableShellABracketLe8RouteReceipt =
        "bracket_le=8 is valid only for r_max=4M (M=1 units), with bracket_le = 2*r_max; theta-shell/cot-bound required for the new angular slots"
    ; christoffelFormulaC0StableShellABracketLe8RouteReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableShellAFallbackThreeTermRouteName =
        "fallback 3-term route"
    ; christoffelFormulaC0StableShellAFallbackThreeTermRouteNameIsCanonical =
        refl
    ; christoffelFormulaC0StableShellAFallbackThreeTermRouteReceipt =
        "(1/2)(24ε+3ε)=27/2ε, 27/2<=22"
    ; christoffelFormulaC0StableShellAFallbackThreeTermRouteReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableShellAConservativeRouteName =
        "33/2<=22<=48"
    ; christoffelFormulaC0StableShellAConservativeRouteNameIsCanonical =
        refl
    ; christoffelFormulaC0StableShellAConservativeRouteReceipt =
        "33/2 <= 22 <= 48"
    ; christoffelFormulaC0StableShellAConservativeRouteReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableFeed27Over2To22ChainName =
        OrderedRational.orderedRationalChristoffel27Over2Le22ArithmeticChainName
    ; christoffelFormulaC0StableFeed27Over2To22ChainNameIsCanonical =
        refl
    ; christoffelFormulaC0StableFeed27Over2To22ChainReceipt =
        "(1/2)(24ε+3ε)=27/2ε, 27/2<=22"
    ; christoffelFormulaC0StableFeed27Over2To22ChainReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableShellAConstantName =
        "22<=48"
    ; christoffelFormulaC0StableShellAConstantNameIsCanonical =
        refl
    ; christoffelFormulaC0StableShellAConstantWitness =
        Continuum.symbolicRationalKernelShellAChristoffelFormula22Le48
    ; christoffelFormulaC0StableShellAConstantWitnessIsCanonical =
        refl
    ; christoffelFormulaC0StableShellAInverseMetricMax =
        3
    ; christoffelFormulaC0StableShellAInverseMetricMaxIs3 =
        refl
    ; christoffelFormulaC0StableShellAMetricDerivativeMax =
        8
    ; christoffelFormulaC0StableShellAMetricDerivativeMaxIs8 =
        refl
    ; christoffelFormulaC0StableShellALegacyLGamma =
        72
    ; christoffelFormulaC0StableShellALegacyLGammaIs72 =
        refl
    ; christoffelFormulaC0StableShellAConservativeLGamma =
        48
    ; christoffelFormulaC0StableShellAConservativeLGammaIs48 =
        refl
    ; christoffelFormulaC0StableShellATightLGamma =
        44
    ; christoffelFormulaC0StableShellATightLGammaIs44 =
        refl
    ; christoffelFormulaC0StableReceiptTable =
        "zero-slot dependency: diagonalZeroLemma"
        ∷ "zero-slot receipt: 13 explicit nonzero triples / 51 zero triples (symmetric triples counted)"
        ∷ "bilinear split dependency: christoffelBilinearSplit"
        ∷ "bilinear split receipt: |δΓ| <= 1/2(|δgi||∂g|+|gi||∂δg|)"
        ∷ "diagonalZeroLemma dependency chain: diagonalZeroLemma <- [bracket_zero_of_not_nonzero, partialDeriv_of_zero]"
        ∷ "Γ_christoffel_diagonal dependency: diagonalZeroLemma <- [bracket_zero_of_not_nonzero, partialDeriv_of_zero]"
        ∷ "christoffelBilinearSplit telescoping identity: telescoping decomposition gives |δΓ| <= 1/2(|δgi||∂g|+|gi||∂δg|)"
        ∷ "11/2 feed to 22: 11/2<=33/2<=22<=48"
        ∷ "27/2 feed to 22 (3-term bracket): (1/2)(24ε+3ε)=27/2ε, 27/2<=22"
        ∷ "direct Shell A bracket_le=8 route: bracket_le=8 is valid only for r_max=4M (M=1 units), with bracket_le = 2*r_max; theta-shell/cot-bound required for the new angular slots"
        ∷ "fallback 3-term route: (1/2)(24ε+3ε)=27/2ε, 27/2<=22"
        ∷ "conservative route: 33/2 <= 22 <= 48"
        ∷ "Shell A constants: inverseMetricMax=3, metricDerivativeMax=8, conservative L_Gamma=48, tight L_Gamma=44, legacy envelope=72"
        ∷ []
    ; christoffelFormulaC0StableReceiptTableIsCanonical =
        refl
    ; christoffelFormulaC0StableSlackReceipt =
        "11/2 ε <= 48 ε"
    ; christoffelFormulaC0StableSlackReceiptIsCanonical =
        refl
    ; christoffelFormulaC0StableSlackArithmeticChainName =
        OrderedRational.orderedRationalChristoffel16p5Le22Le48ArithmeticChainName
    ; christoffelFormulaC0StableSlackArithmeticChainNameIsCanonical =
        refl
    ; christoffelFormulaC0StablePerSlotBound =
        "11/2 ε"
    ; christoffelFormulaC0StablePerSlotBoundIsCanonical =
        refl
    ; christoffelFormulaC0StablePerSlotBoundObligation =
        "11/2 ε <= 48 ε"
    ; christoffelFormulaC0StablePerSlotBoundObligationIsCanonical =
        refl
    ; christoffelFormulaC0StableSafePerSlotBound =
        "27/2 ε"
    ; christoffelFormulaC0StableSafePerSlotBoundIsCanonical =
        refl
    ; christoffelFormulaC0StableSafePerSlotBoundObligation =
        "27/2 ε <= 48 ε"
    ; christoffelFormulaC0StableSafePerSlotBoundObligationIsCanonical =
        refl
    ; christoffelFormulaC0StableTenNonzeroSlotsName =
        "13 nonzero slots"
    ; christoffelFormulaC0StableTenNonzeroSlotsNameIsCanonical =
        refl
    ; christoffelFormulaC0StableSymmetricTripleCountName =
        OrderedRational.coord4SixtyFourTriplesLawName
    ; christoffelFormulaC0StableSymmetricTripleCountNameIsCanonical =
        refl
    ; christoffelFormulaC0StableTenNonzeroObligation =
        "13 nonzero"
    ; christoffelFormulaC0StableTenNonzeroObligationIsCanonical =
        refl
    ; christoffelFormulaC0StableFiftyFourZeroSlotsName =
        "51 zero slots"
    ; christoffelFormulaC0StableFiftyFourZeroSlotsNameIsCanonical =
        refl
    ; christoffelFormulaC0StableFiftyFourZeroObligation =
        "51 zero"
    ; christoffelFormulaC0StableFiftyFourZeroObligationIsCanonical =
        refl
    ; christoffelFormulaC0StableNonzeroSlotCount =
        13
    ; christoffelFormulaC0StableNonzeroSlotCountIs10 =
        refl
    ; christoffelFormulaC0StableZeroSlotCount =
        51
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
        ∷ "DiagonalZeroLemma and christoffelBilinearSplit are recorded with h_static && h_diag, 13 explicit nonzero triples, 51 zero triples, and the exact bilinear split |δΓ| <= 1/2(|δgi||∂g|+|gi||∂δg|)."
        ∷ "ChristoffelFormulaC0Stable now exposes concrete receipt names for independent inverse-metric closeness, zero-slot ledger dependency, the bilinear split, Shell A constant 22<=48, and the 11/2 ε <= 48 ε slack gate."
        ∷ "The local stable surface now also carries the zero-slot dependency alias, bilinear-split dependency alias, a tighter 11/2<=33/2<=22<=48 feed, and a canonical receipt table for the Shell A constants."
        ∷ "DiagonalZeroLemma is now threaded through an explicit local chain: bracket_zero_of_not_nonzero and partialDeriv_of_zero."
        ∷ "Christoffel bilinear split now also carries the telescoping identity route that expands the split estimate."
        ∷ "Γ_christoffel_diagonal is recorded as the diagonal receipt token for the zero-slot dependency chain."
        ∷ "Both per-slot routes are recorded: direct Shell A bracket_le=8 is valid only for r_max=4M (M=1 units), with bracket_le = 2*r_max and theta-shell/cot-bound required for the new angular slots; the 3-term fallback route via (1/2)(24ε+3ε)=27/2ε and 27/2<=22 remains."
        ∷ "The conservative route is recorded honestly as 33/2 <= 22 <= 48."
        ∷ "Ricci perturbation route is carried by the canonical Schwarzschild finite Ricci/Bianchi receipt; convergence and authority promotions are blocked."
        ∷ "Contracted-Bianchi still blocks at selected-connection dependency with exact blocker: missingCarrierConnectionIsLeviCivita."
        ∷ "Exact boundary arithmetic shapes are carried by symbolic-rational and shell-A law shapes, not by fabricated proofs."
        ∷ "Theorem-socket h_gi is recorded via symbolicRationalKernelShellAInverseMetricAbsMaxIs4 and is typed as a kernel-level inverse-metric max witness."
        ∷ "ChristoffelFormulaC0Stable now also records the audited shell-A bound surfaces |gi|<=3 and |∂g|<=8, the zero-slot ledger dependency receipt, and the explicit slack arithmetic chain."
        ∷ "Theorem-socket h_static is recorded as a canonical static-hypothesis receipt."
        ∷ "Theorem-socket h_diag is recorded as a canonical diagonal-hypothesis receipt."
        ∷ "Theorem-socket h_p2g is recorded via symbolicRationalKernelPerturbationRouteDerivativeMaxMatchesDenominatorReceipt and is typed as the route derivative-max matching witness."
        ∷ "Structural sockets for the Christoffel-C0 correction route additionally record the separate static and diagonal assumptions plus the diagonal/nonzero split obligations and the 11/2 ε <= 48 ε slack gate."
        ∷ "Ricci loose route hypotheses now include h_pgi and h_p2g; the derivative control is logged as ∂δΓ <= 19/2 ε with loose Ricci control δR <= 252 ε <= 640 ε."
        ∷ "The 22ε route is explicitly marked algebraic in independent inputs, not a metric inversion argument."
        ∷ []
    }
