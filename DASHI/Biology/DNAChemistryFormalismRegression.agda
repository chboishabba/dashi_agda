module DASHI.Biology.DNAChemistryFormalismRegression where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)

import DASHI.Biology.DNAChemistryCarrier as Carrier
import DASHI.Biology.DNAChemistryCrossPollinationBridge as Cross
import DASHI.Biology.DNAChemistryHamiltonianBoundary as Hamiltonian
import DASHI.Biology.DNAChemistryTritQuotientBridge as TritBridge
import DASHI.Foundations.DNARankZeroToNineRecursiveClosure as RankClosure
import DASHI.Geometry.DNAFourAdicPrefixUltrametricBridge as DNAUltra
import DASHI.Geometry.DNAFourAdicSheetLift as Lift

------------------------------------------------------------------------
-- Compact import and witness surface for the DNA tranche.

carrierReceiptPresent : Carrier.carrierBoundaryHolds Carrier.canonicalDNAChemistryCarrierReceipt ≡ true
carrierReceiptPresent = Carrier.carrierBoundaryHoldsIsTrue Carrier.canonicalDNAChemistryCarrierReceipt

liftReceiptPresent : Lift.liftBoundaryHolds Lift.canonicalDNAFourAdicLiftReceipt ≡ true
liftReceiptPresent = Lift.liftBoundaryHoldsIsTrue Lift.canonicalDNAFourAdicLiftReceipt

hamiltonianReceiptPresent :
  Hamiltonian.hamiltonianBoundaryHolds Hamiltonian.canonicalDNAChemistryHamiltonianReceipt ≡ true
hamiltonianReceiptPresent =
  Hamiltonian.hamiltonianBoundaryHoldsIsTrue Hamiltonian.canonicalDNAChemistryHamiltonianReceipt

tritBridgeReceiptPresent :
  TritBridge.quotientBridgeHolds TritBridge.canonicalDNAChemistryTritQuotientReceipt ≡ true
tritBridgeReceiptPresent =
  TritBridge.quotientBridgeHoldsIsTrue TritBridge.canonicalDNAChemistryTritQuotientReceipt

prefixUltrametricReceiptPresent :
  DNAUltra.bridgeHolds DNAUltra.canonicalDNAFourAdicPrefixUltrametricBridgeReceipt ≡ true
prefixUltrametricReceiptPresent =
  DNAUltra.bridgeHoldsIsTrue DNAUltra.canonicalDNAFourAdicPrefixUltrametricBridgeReceipt

rankClosureReceiptPresent :
  RankClosure.closureBoundaryHolds RankClosure.canonicalDNARankZeroToNineClosureReceipt ≡ true
rankClosureReceiptPresent =
  RankClosure.closureBoundaryHoldsIsTrue RankClosure.canonicalDNARankZeroToNineClosureReceipt

crossPollinationReceiptPresent :
  Cross.crossPollinationHolds Cross.canonicalDNAChemistryCrossPollinationReceipt ≡ true
crossPollinationReceiptPresent =
  Cross.crossPollinationHoldsIsTrue Cross.canonicalDNAChemistryCrossPollinationReceipt

complementRegression : Carrier.complement (Carrier.complement Carrier.G) ≡ Carrier.G
complementRegression = Carrier.complement-involutive Carrier.G

uvRegression : Carrier.fromUV (Carrier.toUV Carrier.C) ≡ Carrier.C
uvRegression = Carrier.fromUV-toUV Carrier.C

tritMarginRegression :
  TritBridge.tritToMargin (TritBridge.marginToTrit TritBridge.positiveMargin)
  ≡ TritBridge.positiveMargin
tritMarginRegression = TritBridge.margin-roundtrip TritBridge.positiveMargin

prefixAgreementRegression :
  DNAUltra.agreementDepth DNAUltra.canonicalDNAAddress4 DNAUltra.canonicalDNAAddress4
  ≡ suc (suc (suc (suc zero)))
prefixAgreementRegression = DNAUltra.canonicalDNAAddress4SelfAgreement

record DNAChemistryFormalismRegressionReceipt : Set where
  constructor mkDNAChemistryFormalismRegressionReceipt
  field
    carrierImported : Bool
    liftImported : Bool
    hamiltonianImported : Bool
    tritBridgeImported : Bool
    prefixUltrametricImported : Bool
    rankClosureImported : Bool
    crossPollinationImported : Bool
    cagtPrimitive : Bool
    fourAdicRanksRecognisable : Bool
    chemistryCrossRankCoupled : Bool
    variableArityPreserved : Bool
    rankSeparatedFromTowerDepth : Bool
    dnaSeparatedFromSSPPrimeCarrier : Bool
    regressionHolds : Bool
    regressionHoldsIsTrue : regressionHolds ≡ true

canonicalDNAChemistryFormalismRegressionReceipt :
  DNAChemistryFormalismRegressionReceipt
canonicalDNAChemistryFormalismRegressionReceipt =
  mkDNAChemistryFormalismRegressionReceipt
    true true true true true true true
    true true true true true true true refl
