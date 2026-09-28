module DASHI.Moonshine.OggSSPP2InertiaStackDenominatorValuationExact where

------------------------------------------------------------------------
-- p=2 INERTIA-STACK ISOTROPY-DENOMINATOR VALUATION
--
-- STANDARD STACK/GROUPOID INPUT
--
-- For a quotient stack [*/G], inertia decomposes over conjugacy classes:
--
--     I([*/G]) = coproduct_[g] [*/C_G(g)].
--
-- For a finite groupoid, the standard groupoid-cardinality contribution of an
-- object is 1 / |Aut|.  Therefore the inertia sector [*/C_G(g)] carries
-- denominator |C_G(g)|.
--
-- DASHI RECONSTRUCTION
--
-- On the characteristic-2 supersingular inertia fibre, G is binary
-- tetrahedral.  Taking v_2 of the sector isotropy denominator gives exactly:
--
--     3, 3, 2, 1, 1
--
-- on the five loop-reversal sectors.  This identifies the already-owned p2
-- preferred weights as a stack-local ISOTROPY-DENOMINATOR depth.
--
-- FIREWALL
--
-- No theorem here identifies:
--   isotropy-denominator depth = Urano composition length,
--   groupoid mass valuation = corrected Hauptmodul valuation,
--   or inertia stack mass = Monster exponent correction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.OggSSPP2InertiaCentralizerValuationExact as Centralizer
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Classical
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Full-inertia sector isotropy denominator.
------------------------------------------------------------------------

sectorRepresentativeClass :
  Inertia.BinaryTetrahedralInversionOrbit ->
  Inertia.BinaryTetrahedralConjugacyClass
sectorRepresentativeClass =
  Centralizer.representativeClass

sectorIsotropyDenominator :
  Inertia.BinaryTetrahedralInversionOrbit ->
  Nat
sectorIsotropyDenominator sector =
  Centralizer.centralizerOrder (sectorRepresentativeClass sector)

sectorIsotropyDenominatorTwoAdicDepth :
  Inertia.BinaryTetrahedralInversionOrbit ->
  Nat
sectorIsotropyDenominatorTwoAdicDepth =
  Centralizer.unorientedCentralizerTwoAdicDepth

------------------------------------------------------------------------
-- 2. Exact denominator-depth vector.
------------------------------------------------------------------------

identitySectorDepthIsThree :
  sectorIsotropyDenominatorTwoAdicDepth
    Inertia.identityInertiaOrbit
  ≡ 3
identitySectorDepthIsThree = refl

centralMinusOneSectorDepthIsThree :
  sectorIsotropyDenominatorTwoAdicDepth
    Inertia.centralMinusOneInertiaOrbit
  ≡ 3
centralMinusOneSectorDepthIsThree = refl

orderFourSectorDepthIsTwo :
  sectorIsotropyDenominatorTwoAdicDepth
    Inertia.orderFourInertiaOrbit
  ≡ 2
orderFourSectorDepthIsTwo = refl

orderThreePairSectorDepthIsOne :
  sectorIsotropyDenominatorTwoAdicDepth
    Inertia.orderThreePairInertiaOrbit
  ≡ 1
orderThreePairSectorDepthIsOne = refl

orderSixPairSectorDepthIsOne :
  sectorIsotropyDenominatorTwoAdicDepth
    Inertia.orderSixPairInertiaOrbit
  ≡ 1
orderSixPairSectorDepthIsOne = refl

------------------------------------------------------------------------
-- 3. Preferred p2 weight is exactly the isotropy-denominator depth.
------------------------------------------------------------------------

preferredP2WeightIsIsotropyDenominatorDepth :
  (sector : Inertia.BinaryTetrahedralInversionOrbit) ->
  Preferred.weight Preferred.p2PreferredPresentation sector
  ≡
  sectorIsotropyDenominatorTwoAdicDepth sector
preferredP2WeightIsIsotropyDenominatorDepth
  Inertia.identityInertiaOrbit = refl
preferredP2WeightIsIsotropyDenominatorDepth
  Inertia.centralMinusOneInertiaOrbit = refl
preferredP2WeightIsIsotropyDenominatorDepth
  Inertia.orderFourInertiaOrbit = refl
preferredP2WeightIsIsotropyDenominatorDepth
  Inertia.orderThreePairInertiaOrbit = refl
preferredP2WeightIsIsotropyDenominatorDepth
  Inertia.orderSixPairInertiaOrbit = refl

p2IsotropyDenominatorDepthTotal : Nat
p2IsotropyDenominatorDepthTotal =
  sectorIsotropyDenominatorTwoAdicDepth Inertia.identityInertiaOrbit
  + sectorIsotropyDenominatorTwoAdicDepth Inertia.centralMinusOneInertiaOrbit
  + sectorIsotropyDenominatorTwoAdicDepth Inertia.orderFourInertiaOrbit
  + sectorIsotropyDenominatorTwoAdicDepth Inertia.orderThreePairInertiaOrbit
  + sectorIsotropyDenominatorTwoAdicDepth Inertia.orderSixPairInertiaOrbit

p2IsotropyDenominatorDepthTotalIsTen :
  p2IsotropyDenominatorDepthTotal ≡ 10
p2IsotropyDenominatorDepthTotalIsTen = refl

------------------------------------------------------------------------
-- 4. Attribution and non-promotion boundary.
------------------------------------------------------------------------

classicalSourcingBoundary :
  Classical.SmallCharacteristicClassicalSourcingBoundary
classicalSourcingBoundary =
  Classical.canonicalSmallCharacteristicClassicalSourcingBoundary

data InertiaMassDepthIsUranoCompositionLength : Set where
data InertiaMassDepthIsCorrectedHauptmodulValuation : Set where
data InertiaMassDepthProvesMonsterResidual : Set where
data LoopReversalQuotientPreservesStackMassWithoutProof : Set where

inertiaMassDepthNotIdentifiedWithUranoLength :
  InertiaMassDepthIsUranoCompositionLength -> ⊥
inertiaMassDepthNotIdentifiedWithUranoLength ()

inertiaMassDepthNotIdentifiedWithHauptmodulValuation :
  InertiaMassDepthIsCorrectedHauptmodulValuation -> ⊥
inertiaMassDepthNotIdentifiedWithHauptmodulValuation ()

inertiaMassDepthDoesNotProveMonsterResidual :
  InertiaMassDepthProvesMonsterResidual -> ⊥
inertiaMassDepthDoesNotProveMonsterResidual ()

loopReversalMassTransportNeedsProof :
  LoopReversalQuotientPreservesStackMassWithoutProof -> ⊥
loopReversalMassTransportNeedsProof ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryCrossModuleInference

record P2InertiaStackDenominatorValuationBoundary : Set where
  constructor p2-inertia-stack-denominator-valuation-boundary
  field
    inertiaComponentsByCentralizerClassicallySourced : Bool
    finiteGroupoidInverseAutomorphismWeightSourced : Bool
    binaryTetrahedralCentralizerOrdersOwned : Bool
    fiveSectorIsotropyDenominatorDepthsExact : Bool
    depthVectorThreeThreeTwoOneOne : Bool
    preferredP2WeightIdentifiedAsIsotropyDenominatorDepth : Bool
    isotropyDepthTotalTen : Bool
    isotropyDepthPromotedToUranoLength : Bool
    isotropyDepthPromotedToHauptmodulValuation : Bool
    isotropyDepthPromotedToMonsterCorrection : Bool
    attributionFirewallPreserved : Bool

canonicalP2InertiaStackDenominatorValuationBoundary :
  P2InertiaStackDenominatorValuationBoundary
canonicalP2InertiaStackDenominatorValuationBoundary =
  p2-inertia-stack-denominator-valuation-boundary
    true true true true true true true false false false true
