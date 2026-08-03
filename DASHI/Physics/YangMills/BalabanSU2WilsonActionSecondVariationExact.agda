module DASHI.Physics.YangMills.BalabanSU2WilsonActionSecondVariationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; _+_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.CompactLieGroupCore
open import DASHI.Physics.YangMills.CompactLieLatticeGauge
open import DASHI.Physics.YangMills.SUNMatrixCarrier using (matrix)
open import DASHI.Physics.YangMills.SUNWilsonClassFunction
open import DASHI.Physics.YangMills.SUNWilsonAction
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL; physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact using
  (shiftForward4; siteSum4; sumRationalCartesian)
open import DASHI.Physics.YangMills.BalabanSU2WilsonPlaquetteSecondJetExact
open import DASHI.Physics.YangMills.BalabanSU2SecondJetSUNInstanceExact
open import DASHI.Physics.YangMills.BalabanPath4SU2LiteralPlaquetteLiftExact

------------------------------------------------------------------------
-- The generic action is evaluated on the physical side-four periodic lattice.
------------------------------------------------------------------------

data PhysicalJetEdge : Set where
  positiveJetEdge negativeJetEdge :
    Axis4 → PhysicalBlockL side4 → PhysicalJetEdge

physicalJetEdgeSource : PhysicalJetEdge → PhysicalBlockL side4
physicalJetEdgeSource (positiveJetEdge axis site) = site
physicalJetEdgeSource (negativeJetEdge axis site) = shiftForward4 axis site

physicalJetEdgeTarget : PhysicalJetEdge → PhysicalBlockL side4
physicalJetEdgeTarget (positiveJetEdge axis site) = shiftForward4 axis site
physicalJetEdgeTarget (negativeJetEdge axis site) = site

physicalJetLattice : LatticeGaugeSystem
physicalJetLattice = record
  { Site = PhysicalBlockL side4
  ; Edge = PhysicalJetEdge
  ; source = physicalJetEdgeSource
  ; target = physicalJetEdgeTarget
  }

physicalJetGaugeField : PhysicalSU2Tangent4 → GaugeField physicalJetLattice JetSUN
physicalJetGaugeField tangent (positiveJetEdge axis site) =
  sunExponentialJet (physicalTangentAtSiteAxisAsLie3 tangent axis site)
physicalJetGaugeField tangent (negativeJetEdge axis site) =
  sunInverseExponentialJet (physicalTangentAtSiteAxisAsLie3 tangent axis site)

physicalPlaquettePath :
  PositivePlaquettePlane4 → PhysicalBlockL side4 → Path physicalJetLattice
physicalPlaquettePath plane site =
  step (positiveJetEdge first site)
    (step (positiveJetEdge second (shiftForward4 first site))
      (step (negativeJetEdge first (shiftForward4 second site))
        (step (negativeJetEdge second site) empty)))
  where
  first = positivePlaneFirst plane
  second = positivePlaneSecond plane

physicalPlaquetteLoop :
  PositivePlaquettePlane4 → PhysicalBlockL side4 → Loop physicalJetLattice
physicalPlaquetteLoop plane site = record
  { path = physicalPlaquettePath plane site
  ; closedProof = refl
  }

PhysicalPlaquette : Set
PhysicalPlaquette = Product PositivePlaquettePlane4 (PhysicalBlockL side4)

physicalPlaquettes : List PhysicalPlaquette
physicalPlaquettes =
  cartesian positivePlaquettePlanes4 (physicalBlockSites side4)

physicalPlaquetteLoopFromIndex : PhysicalPlaquette → Loop physicalJetLattice
physicalPlaquetteLoopFromIndex (pair plane site) = physicalPlaquetteLoop plane site

------------------------------------------------------------------------
-- The right-associated generic path product is the same exact second jet used
-- by the literal four-link calculation.
------------------------------------------------------------------------

rightAssociatedPlaquetteJet : Lie3 → Lie3 → Lie3 → Lie3 → SU2SecondJet
rightAssociatedPlaquetteJet first second third fourth =
  exponentialJet first *j
    (exponentialJet second *j
      (inverseExponentialJet third *j
        (inverseExponentialJet fourth *j identityJet)))

rightAssociatedPlaquetteJetExact : ∀ first second third fourth →
  rightAssociatedPlaquetteJet first second third fourth
  ≡ plaquetteJet first second third fourth
rightAssociatedPlaquetteJetExact
  (lie3 ax ay az) (lie3 bx by bz)
  (lie3 cx cy cz) (lie3 dx dy dz) =
  jetExt
    (ℚRing.solve-∀)
    (lie3Ext
      (ℚRing.solve-∀)
      (ℚRing.solve-∀)
      (ℚRing.solve-∀))

physicalPlaquetteHolonomyMatrixExact : ∀ tangent plane site →
  matrix
    (pathHolonomy physicalJetLattice jetSUNGroup
      (physicalPlaquettePath plane site)
      (physicalJetGaugeField tangent))
  ≡ literalPlaquetteJet tangent plane site
physicalPlaquetteHolonomyMatrixExact tangent plane site =
  rightAssociatedPlaquetteJetExact
    (firstLink links) (secondLink links) (thirdLink links) (fourthLink links)
  where
  links = literalPlaquetteFourLinks tangent plane site

------------------------------------------------------------------------
-- The generic Wilson class function has the same second derivative as the
-- exact local physical Hessian term.
------------------------------------------------------------------------

genericPlaquetteSecondDerivativeUnfold :
  ∀ (loop : Loop physicalJetLattice)
    (field : GaugeField physicalJetLattice JetSUN) →
  scalarSecondDerivative
    (wilsonPlaquetteValue scalarSecondJetOperations jetSUNTraceAuthority
      loop field)
  ≡ - (twoR * realSecond
      (matrix (loopObservable physicalJetLattice jetSUNGroup loop field)))
genericPlaquetteSecondDerivativeUnfold loop field =
  ℚRing.solve-∀

physicalPlaquetteWilsonSecondVariationExact : ∀ tangent plane site →
  scalarSecondDerivative
    (wilsonPlaquetteValue scalarSecondJetOperations jetSUNTraceAuthority
      (physicalPlaquetteLoop plane site) (physicalJetGaugeField tangent))
  ≡ literalPlaquetteWilsonSecondVariation tangent plane site
physicalPlaquetteWilsonSecondVariationExact tangent plane site =
  trans
    (genericPlaquetteSecondDerivativeUnfold
      (physicalPlaquetteLoop plane site) (physicalJetGaugeField tangent))
    (trans
      (cong (λ path → - (twoR * realSecond path))
        (physicalPlaquetteHolonomyMatrixExact tangent plane site))
      (ℚRing.solve-∀))

------------------------------------------------------------------------
-- Second differentiation commutes with the generic finite Wilson-action fold.
------------------------------------------------------------------------

scalarSecondDerivativeWilsonFold :
  ∀ (plaquettes : List PhysicalPlaquette) tangent →
  scalarSecondDerivative
    (wilsonActionFromPlaquettes scalarSecondJetOperations jetSUNTraceAuthority
      physicalPlaquetteLoopFromIndex plaquettes
      (physicalJetGaugeField tangent))
  ≡ sumRational plaquettes (λ plaquette →
      scalarSecondDerivative
        (wilsonPlaquetteValue scalarSecondJetOperations jetSUNTraceAuthority
          (physicalPlaquetteLoopFromIndex plaquette)
          (physicalJetGaugeField tangent)))
scalarSecondDerivativeWilsonFold [] tangent = scalarSecondDerivativeZero
scalarSecondDerivativeWilsonFold (plaquette ∷ plaquettes) tangent =
  trans
    (scalarSecondDerivativeAdd
      (wilsonPlaquetteValue scalarSecondJetOperations jetSUNTraceAuthority
        (physicalPlaquetteLoopFromIndex plaquette)
        (physicalJetGaugeField tangent))
      (wilsonActionFromPlaquettes scalarSecondJetOperations jetSUNTraceAuthority
        physicalPlaquetteLoopFromIndex plaquettes
        (physicalJetGaugeField tangent)))
    (cong₂ _+_ refl
      (scalarSecondDerivativeWilsonFold plaquettes tangent))

physicalJetWilsonAction : PhysicalSU2Tangent4 → ScalarSecondJet
physicalJetWilsonAction tangent =
  sunWilsonAction scalarSecondJetOperations jetSUNTraceAuthority
    physicalPlaquetteLoopFromIndex physicalPlaquettes
    (physicalJetGaugeField tangent)

genericSUNWilsonActionSecondVariationEqualsLiteralFold : ∀ tangent →
  scalarSecondDerivative (physicalJetWilsonAction tangent)
  ≡ literalWilsonHessianPositivePlaneFold tangent
genericSUNWilsonActionSecondVariationEqualsLiteralFold tangent =
  trans
    (scalarSecondDerivativeWilsonFold physicalPlaquettes tangent)
    (trans
      (sumRationalCong physicalPlaquettes _ _ (λ where
        (pair plane site) →
          physicalPlaquetteWilsonSecondVariationExact tangent plane site))
      (sumRationalCartesian positivePlaquettePlanes4
        (physicalBlockSites side4)
        (λ where
          (pair plane site) →
            literalPlaquetteWilsonSecondVariation tangent plane site)))

sunWilsonActionSecondVariationAdapterLevel : ProofLevel
sunWilsonActionSecondVariationAdapterLevel = machineChecked

sunWilsonActionPhysicalFoldIdentificationLevel : ProofLevel
sunWilsonActionPhysicalFoldIdentificationLevel = machineChecked
