module DASHI.Education.DigitalESDEfSCanonicalReuseAdapterRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDEfSCanonicalReuseAdapterExact as Adapter
import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Braid
import DASHI.Education.DigitalESDEfSIndependentChallengeExact as EfS

collectiveTensionUsesCanonicalBraid :
  Adapter.relationFor (EfS.ComparisonReceipt.outcome EfS.collectiveComparison)
  ≡ Braid.productiveTension
collectiveTensionUsesCanonicalBraid = refl

ecologicalUnmatchedUsesScopeDifference :
  Adapter.relationFor (EfS.ComparisonReceipt.outcome EfS.ecologicalComparison)
  ≡ Braid.scopeDifference
ecologicalUnmatchedUsesScopeDifference = refl

reuseMatchesExistingRelation :
  Braid.TensionReceipt.relation (Adapter.EfSReuseReceipt.braid (Adapter.reuse EfS.valuesComparison))
  ≡ Braid.productiveTension
reuseMatchesExistingRelation = refl

canonicalNineteenCoordinates :
  Adapter.dbNativeCoordinateCount ≡ 19
canonicalNineteenCoordinates = refl

pairingDoesNotPayEmpiricalEffect :
  Adapter.SourcePairingIsEmpiricalEffect → ⊥
pairingDoesNotPayEmpiricalEffect = Adapter.sourcePairingDoesNotProveEffect
