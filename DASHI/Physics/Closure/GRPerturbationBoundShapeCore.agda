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
        ∷ "Ricci perturbation route is carried by the canonical Schwarzschild finite Ricci/Bianchi receipt; convergence and authority promotions are blocked."
        ∷ "Contracted-Bianchi still blocks at selected-connection dependency with exact blocker: missingCarrierConnectionIsLeviCivita."
        ∷ "Exact boundary arithmetic shapes are carried by symbolic-rational and shell-A law shapes, not by fabricated proofs."
        ∷ []
    }
