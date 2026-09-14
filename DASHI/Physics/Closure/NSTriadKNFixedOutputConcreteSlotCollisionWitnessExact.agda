module DASHI.Physics.Closure.NSTriadKNFixedOutputConcreteSlotCollisionWitnessExact where

------------------------------------------------------------------------
-- PR #916 / CONCRETE DISTINCT-INCIDENCE SLOT COLLISION WITNESS
--
-- PR #890 proved two separate facts:
--
--   (1) two distinct literal comparable incidences can share one output mode;
--   (2) on a fixed output, equal velocity arguments imply equal raw-curl slot
--       kernels, independently of incidence labels.
--
-- This owner inhabits both facts in ONE finite Galerkin system.  We use the
-- literal finite Audit carrier with identically-zero velocity.  Zero is
-- transverse to every Fourier mode, hence both #890 incidences produce actual
-- R205 raw-curl partner cells and R207 fixed-output partners.  Their p- and
-- q-slot velocity arguments agree definitionally, so the merged collision law
-- gives equal slot observables on distinct incidences.
--
-- This closes the concrete many-to-one observable witness.  It does NOT yet
-- prove that any particular radial/Pluecker defect functional is strictly
-- positive on this pair; therefore the stronger named coercivity no-go remains
-- fail-closed.  No residual budget, spacetime estimate, R568 payment, or Clay
-- promotion is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityTransverseRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlPartnerBonyRound186Exact as R186
import DASHI.Physics.Closure.NSTriadKNComparableRawCurlPartnerMassRound205Exact as R205
import DASHI.Physics.Closure.NSTriadKNComparableFixedOutputCarrierRound207Exact as R207
import DASHI.Physics.Closure.NSTriadKNFixedOutputSlotCollisionExact as Collision
import DASHI.Physics.Closure.NSTriadKNFixedOutputComparableCollisionGeometryExact as Geometry

F = R205.F

three : Nat
three = 3

zeroFiniteSystem :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I
zeroFiniteSystem {E = E} {I = I} = record
  { Audit.FiniteComplex3GalerkinSystem.cutoff = three
  ; Audit.FiniteComplex3GalerkinSystem.modes = []
  ; Audit.FiniteComplex3GalerkinSystem.triads =
      Physical.physicalTriadEnumeration three
  ; Audit.FiniteComplex3GalerkinSystem.velocity =
      λ _ → C3.complex3Zero F
  ; Audit.FiniteComplex3GalerkinSystem.viscosity = C3.zero F
  ; Audit.FiniteComplex3GalerkinSystem.modeListed = λ _ → ⊤
  ; Audit.FiniteComplex3GalerkinSystem.triadListed = λ _ → ⊤
  ; Audit.FiniteComplex3GalerkinSystem.modesAreLiteralCutoff = ⊤
  ; Audit.FiniteComplex3GalerkinSystem.triadsAreLiteralEnumeration = refl
  ; Audit.FiniteComplex3GalerkinSystem.zeroModeExcluded = ⊤
  ; Audit.FiniteComplex3GalerkinSystem.realityClosed = ⊤
  }

zeroVelocityTransverse :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (mode : Z3.FourierMode) →
  Helical.Transverse E mode (Audit.velocity (zeroFiniteSystem {E = E} {I = I}) mode)
zeroVelocityTransverse {E = E} mode =
  R30.bilinearDot3ZeroRight (C3.modeVector E mode)

alphaRawCurlData :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  R186.PhysicalRawCurlCellData
    (zeroFiniteSystem {E = E} {I = I}) Geometry.alphaIncidence
alphaRawCurlData =
  R186.physical-raw-curl-cell-data
    (zeroVelocityTransverse Geometry.alphaP)
    (zeroVelocityTransverse Geometry.alphaQ)

betaRawCurlData :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  R186.PhysicalRawCurlCellData
    (zeroFiniteSystem {E = E} {I = I}) Geometry.betaIncidence
betaRawCurlData =
  R186.physical-raw-curl-cell-data
    (zeroVelocityTransverse Geometry.betaP)
    (zeroVelocityTransverse Geometry.betaQ)

alphaPartner :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  R205.LocalizedComparableRawCurlPartner
    (zeroFiniteSystem {E = E} {I = I})
alphaPartner =
  R205.localized-comparable-raw-curl-partner
    Geometry.alphaLocalizedComparable
    alphaRawCurlData

betaPartner :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  R205.LocalizedComparableRawCurlPartner
    (zeroFiniteSystem {E = E} {I = I})
betaPartner =
  R205.localized-comparable-raw-curl-partner
    Geometry.betaLocalizedComparable
    betaRawCurlData

alphaFixedOutput :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  R207.FixedOutputLocalizedComparablePartner
    (zeroFiniteSystem {E = E} {I = I}) Geometry.outputMode
alphaFixedOutput =
  R207.fixed-output-localized-comparable-partner alphaPartner refl

betaFixedOutput :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  R207.FixedOutputLocalizedComparablePartner
    (zeroFiniteSystem {E = E} {I = I}) Geometry.outputMode
betaFixedOutput =
  R207.fixed-output-localized-comparable-partner betaPartner refl

alphaBetaPSlotVelocityAgreement :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.velocity (zeroFiniteSystem {E = E} {I = I}) Geometry.alphaP
  ≡ Audit.velocity (zeroFiniteSystem {E = E} {I = I}) Geometry.betaP
alphaBetaPSlotVelocityAgreement = refl

alphaBetaQSlotVelocityAgreement :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.velocity (zeroFiniteSystem {E = E} {I = I}) Geometry.alphaQ
  ≡ Audit.velocity (zeroFiniteSystem {E = E} {I = I}) Geometry.betaQ
alphaBetaQSlotVelocityAgreement = refl

concreteDistinctCCSlotCollision :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Collision.Adapter.compressedPartnerSlotKernel
    (R207.partner (alphaFixedOutput {E = E} {I = I}))
  ≡ Collision.Adapter.compressedPartnerSlotKernel
    (R207.partner (betaFixedOutput {E = E} {I = I}))
concreteDistinctCCSlotCollision {E = E} {I = I} =
  Collision.fixedOutputEqualVelocityArgumentsHaveEqualSlotKernel
    (alphaFixedOutput {E = E} {I = I})
    (betaFixedOutput {E = E} {I = I})
    alphaBetaPSlotVelocityAgreement
    alphaBetaQSlotVelocityAgreement

concreteCollisionIncidencesRemainDistinct :
  Geometry.alphaIncidence ≡ Geometry.betaIncidence → ⊥
concreteCollisionIncidencesRemainDistinct = Geometry.incidencesDistinct

roundFixedOutputConcreteDistinctCCCollisionWitnessConstructed : Bool
roundFixedOutputConcreteDistinctCCCollisionWitnessConstructed = true

roundFixedOutputIncidenceOnlyRadialPlueckerCoercivityRefuted : Bool
roundFixedOutputIncidenceOnlyRadialPlueckerCoercivityRefuted = false

roundFixedOutputConcreteCollisionClayPromotion : Bool
roundFixedOutputConcreteCollisionClayPromotion = false

roundFixedOutputConcreteDistinctCCCollisionWitnessConstructedIsTrue :
  roundFixedOutputConcreteDistinctCCCollisionWitnessConstructed ≡ true
roundFixedOutputConcreteDistinctCCCollisionWitnessConstructedIsTrue = refl

roundFixedOutputIncidenceOnlyRadialPlueckerCoercivityRefutedIsFalse :
  roundFixedOutputIncidenceOnlyRadialPlueckerCoercivityRefuted ≡ false
roundFixedOutputIncidenceOnlyRadialPlueckerCoercivityRefutedIsFalse = refl
