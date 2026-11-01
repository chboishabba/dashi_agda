module DASHI.Moonshine.OggSSPP3DeligneRapoportLocalMultiplicityExact where

------------------------------------------------------------------------
-- p=3 DELIGNE--RAPOPORT LOCAL MULTIPLICITY WEIGHTS
--
-- CLASSICAL GEOMETRY
--
-- The special fibre of X0(p) in the Deligne--Rapoport model consists of two
-- reduced components meeting transversely at supersingular points.
--
-- Thus at the unique p=3 supersingular point:
--
--   * each Frobenius/Verschiebung branch occurs with generic multiplicity 1;
--   * the local branch intersection multiplicity is 1.
--
-- DASHI CROSS-WELD
--
-- The two preferred p=3 orbit sectors are:
--
--   node orbit,
--   exchanged branch-pair orbit.
--
-- Their existing weights 1,1 therefore admit a classical semistable-local
-- multiplicity interpretation.
--
-- FIREWALL
--
-- This does not identify semistable intersection/component multiplicity with
-- Urano DVR composition length or with a corrected Hauptmodul valuation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as P3
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Classical
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Classical local multiplicity surface.
------------------------------------------------------------------------

branchGenericMultiplicity : Nat
branchGenericMultiplicity = 1

nodeTransverseIntersectionMultiplicity : Nat
nodeTransverseIntersectionMultiplicity = 1

p3LocalGeometricMultiplicity :
  P3.P3LocalOrbit ->
  Nat
p3LocalGeometricMultiplicity P3.nodeOrbit =
  nodeTransverseIntersectionMultiplicity
p3LocalGeometricMultiplicity P3.branchOrbit =
  branchGenericMultiplicity

nodeMultiplicityIsOne :
  p3LocalGeometricMultiplicity P3.nodeOrbit ≡ 1
nodeMultiplicityIsOne = refl

branchPairMultiplicityIsOne :
  p3LocalGeometricMultiplicity P3.branchOrbit ≡ 1
branchPairMultiplicityIsOne = refl

------------------------------------------------------------------------
-- 2. Preferred p3 weights are exactly these local multiplicities.
------------------------------------------------------------------------

preferredP3WeightIsLocalGeometricMultiplicity :
  (sector : P3.P3LocalOrbit) ->
  Preferred.weight Preferred.p3PreferredPresentation sector
  ≡
  p3LocalGeometricMultiplicity sector
preferredP3WeightIsLocalGeometricMultiplicity P3.nodeOrbit = refl
preferredP3WeightIsLocalGeometricMultiplicity P3.branchOrbit = refl

p3LocalGeometricMultiplicityTotal : Nat
p3LocalGeometricMultiplicityTotal =
  p3LocalGeometricMultiplicity P3.nodeOrbit
  + p3LocalGeometricMultiplicity P3.branchOrbit

p3LocalGeometricMultiplicityTotalIsTwo :
  p3LocalGeometricMultiplicityTotal ≡ 2
p3LocalGeometricMultiplicityTotalIsTwo = refl

------------------------------------------------------------------------
-- 3. Attribution and non-promotion boundary.
------------------------------------------------------------------------

classicalSourcingBoundary :
  Classical.SmallCharacteristicClassicalSourcingBoundary
classicalSourcingBoundary =
  Classical.canonicalSmallCharacteristicClassicalSourcingBoundary

data SemistableMultiplicityIsUranoCompositionLength : Set where
data SemistableMultiplicityIsCorrectedHauptmodulValuation : Set where
data SemistableMultiplicityProvesMonsterResidual : Set where
data BranchPairOrbitMultiplicityIsSumOfTwoBranches : Set where

semistableMultiplicityNotIdentifiedWithUranoLength :
  SemistableMultiplicityIsUranoCompositionLength -> ⊥
semistableMultiplicityNotIdentifiedWithUranoLength ()

semistableMultiplicityNotIdentifiedWithHauptmodulValuation :
  SemistableMultiplicityIsCorrectedHauptmodulValuation -> ⊥
semistableMultiplicityNotIdentifiedWithHauptmodulValuation ()

semistableMultiplicityDoesNotProveMonsterResidual :
  SemistableMultiplicityProvesMonsterResidual -> ⊥
semistableMultiplicityDoesNotProveMonsterResidual ()

branchPairOrbitWeightIsNotNaiveTwoBranchSum :
  BranchPairOrbitMultiplicityIsSumOfTwoBranches -> ⊥
branchPairOrbitWeightIsNotNaiveTwoBranchSum ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record P3DeligneRapoportLocalMultiplicityBoundary : Set where
  constructor p3-deligne-rapoport-local-multiplicity-boundary
  field
    reducedTwoComponentSpecialFibreClassicallySourced : Bool
    transverseSupersingularIntersectionClassicallySourced : Bool
    branchGenericMultiplicityOne : Bool
    nodeIntersectionMultiplicityOne : Bool
    preferredP3WeightsIdentifiedWithLocalMultiplicities : Bool
    localMultiplicityTotalTwo : Bool
    multiplicityPromotedToUranoLength : Bool
    multiplicityPromotedToHauptmodulValuation : Bool
    multiplicityPromotedToMonsterCorrection : Bool
    attributionFirewallPreserved : Bool

canonicalP3DeligneRapoportLocalMultiplicityBoundary :
  P3DeligneRapoportLocalMultiplicityBoundary
canonicalP3DeligneRapoportLocalMultiplicityBoundary =
  p3-deligne-rapoport-local-multiplicity-boundary
    true true true true true true false false false true
