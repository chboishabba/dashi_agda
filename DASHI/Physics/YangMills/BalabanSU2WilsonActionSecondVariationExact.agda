module DASHI.Physics.YangMills.BalabanSU2WilsonActionSecondVariationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_)
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

data PhysicalJetEdge (u v : PhysicalBlockL side4) : Set where
  positiveJetEdge negativeJetEdge :
    Axis4 → PhysicalBlockL side4 → PhysicalJetEdge u v

physicalJetGaugeField :
  PhysicalSU2Tangent4 → GaugeField {G = JetSUN} PhysicalJetEdge
physicalJetGaugeField tangent _ _ (positiveJetEdge axis site) =
  sunExponentialJet (physicalTangentAtSiteAxisAsLie3 tangent axis site)
physicalJetGaugeField tangent _ _ (negativeJetEdge axis site) =
  sunInverseExponentialJet (physicalTangentAtSiteAxisAsLie3 tangent axis site)

physicalPlaquettePath :
  PositivePlaquettePlane4 → (site : PhysicalBlockL side4) →
  Path PhysicalJetEdge site site
physicalPlaquettePath plane site =
  _▷_ {x = site} {y = site} (positiveJetEdge firstAxis site)
    (_▷_ {x = site} {y = site} (positiveJetEdge secondAxis (shiftForward4 firstAxis site))
      (_▷_ {x = site} {y = site} (negativeJetEdge firstAxis (shiftForward4 secondAxis site))
        (_▷_ {x = site} {y = site} (negativeJetEdge secondAxis site) empty)))
  where
  firstAxis = positivePlaneFirst plane
  secondAxis = positivePlaneSecond plane

PhysicalPlaquette : Set
PhysicalPlaquette = Product PositivePlaquettePlane4 (PhysicalBlockL side4)

physicalPlaquettes : List PhysicalPlaquette
physicalPlaquettes =
  cartesian positivePlaquettePlanes4 (physicalBlockSites side4)

physicalPlaquetteBase : PhysicalPlaquette → PhysicalBlockL side4
physicalPlaquetteBase (pair _ site) = site

physicalPlaquetteBoundary :
  (plaquette : PhysicalPlaquette) →
  Path PhysicalJetEdge (physicalPlaquetteBase plaquette) (physicalPlaquetteBase plaquette)
physicalPlaquetteBoundary (pair plane site) = physicalPlaquettePath plane site

physicalSUNWilsonActionData :
  SUNWilsonActionData {Scalar = ScalarSecondJet} jetSUNTheory PhysicalJetEdge
physicalSUNWilsonActionData = record
  { Plaquette = PhysicalPlaquette
  ; plaquettes = physicalPlaquettes
  ; plaquetteBase = physicalPlaquetteBase
  ; plaquetteBoundary = physicalPlaquetteBoundary
  ; scalarOperations = scalarSecondJetOperations
  ; traceAuthority = jetSUNTraceAuthority
  }

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

threeSumLeft : ∀ a b c → a + (b + c) ≡ a + b + c
threeSumLeft = ℚRing.solve-∀

plaquetteJetIsLeftAssociated : ∀ first second third fourth →
  ((exponentialJet first *j exponentialJet second) *j inverseExponentialJet third)
    *j inverseExponentialJet fourth
  ≡ plaquetteJet first second third fourth
plaquetteJetIsLeftAssociated
  (lie3 ax ay az) (lie3 bx by bz)
  (lie3 cx cy cz) (lie3 dx dy dz) =
  jetExt
    (cong₂ _+_
      (cong₂ _+_
        (cong₂ _+_
          (cong₂ _+_
            (cong₂ _+_
              (cong₂ _+_
                (cong (λ u → - (half * u)) (threeSumLeft (ax * ax) (ay * ay) (az * az)))
                (cong (λ u → - (half * u)) (threeSumLeft (bx * bx) (by * by) (bz * bz))))
              (cong -_ (threeSumLeft (ax * bx) (ay * by) (az * bz))))
            (cong (λ u → - (half * u)) (threeSumLeft (cx * cx) (cy * cy) (cz * cz))))
          (cong -_ (threeSumLeft ((ax + bx) * (- cx)) ((ay + by) * (- cy)) ((az + bz) * (- cz)))))
        (cong (λ u → - (half * u)) (threeSumLeft (dx * dx) (dy * dy) (dz * dz))))
      (cong -_ (threeSumLeft (((ax + bx) + (- cx)) * (- dx)) (((ay + by) + (- cy)) * (- dy)) (((az + bz) + (- cz)) * (- dz)))))
    refl

rightAssociatedFourJet : ∀ j₁ j₂ j₃ j₄ →
  j₁ *j (j₂ *j (j₃ *j (j₄ *j identityJet)))
  ≡ ((j₁ *j j₂) *j j₃) *j j₄
rightAssociatedFourJet j₁ j₂ j₃ j₄ =
  trans
    (cong (λ u → j₁ *j (j₂ *j (j₃ *j u))) (jetIdentityRight j₄))
    (trans
      (sym (jetMultiplyAssociative j₁ j₂ (j₃ *j j₄)))
      (sym (jetMultiplyAssociative (j₁ *j j₂) j₃ j₄)))

rightAssociatedPlaquetteJetExact : ∀ first second third fourth →
  rightAssociatedPlaquetteJet first second third fourth
  ≡ plaquetteJet first second third fourth
rightAssociatedPlaquetteJetExact first second third fourth =
  trans
    (rightAssociatedFourJet
      (exponentialJet first)
      (exponentialJet second)
      (inverseExponentialJet third)
      (inverseExponentialJet fourth))
    (plaquetteJetIsLeftAssociated first second third fourth)

physicalPlaquetteHolonomyMatrixExact : ∀ tangent plane site →
  matrix
    (holonomy jetSUNGroup
      (physicalJetGaugeField tangent)
      (physicalPlaquettePath plane site))
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

twoZeroSubRaw : ∀ q → twoR * (0ℚ + - q) ≡ - (twoR * q)
twoZeroSubRaw = ℚRing.solve-∀

genericPlaquetteSecondDerivativeUnfold :
  ∀ {site : PhysicalBlockL side4}
    (path : Path PhysicalJetEdge site site)
    (fld : GaugeField {G = JetSUN} PhysicalJetEdge) →
  scalarSecondDerivative
    (loopObservable jetSUNGroup
      (wilsonPlaquetteValue scalarSecondJetOperations jetSUNTraceAuthority)
      fld path)
  ≡ - (twoR * realSecond
      (matrix (holonomy jetSUNGroup fld path)))
genericPlaquetteSecondDerivativeUnfold path fld =
  twoZeroSubRaw (realSecond (matrix (holonomy jetSUNGroup fld path)))

twoRIsTwoRaw : ∀ q → - (twoR * q) ≡ - ((1ℚ + 1ℚ) * q)
twoRIsTwoRaw q = refl

physicalPlaquetteWilsonSecondVariationExact : ∀ tangent plane site →
  scalarSecondDerivative
    (loopObservable jetSUNGroup
      (wilsonPlaquetteValue scalarSecondJetOperations jetSUNTraceAuthority)
      (physicalJetGaugeField tangent)
      (physicalPlaquettePath plane site))
  ≡ literalPlaquetteWilsonSecondVariation tangent plane site
physicalPlaquetteWilsonSecondVariationExact tangent plane site =
  trans
    (genericPlaquetteSecondDerivativeUnfold
      (physicalPlaquettePath plane site) (physicalJetGaugeField tangent))
    (cong (λ path → - (twoR * realSecond path))
      (physicalPlaquetteHolonomyMatrixExact tangent plane site))

------------------------------------------------------------------------
-- Second differentiation commutes with the generic finite Wilson-action fold.
------------------------------------------------------------------------

scalarSecondDerivativeWilsonFold :
  ∀ (plaquettes : List PhysicalPlaquette) tangent →
  scalarSecondDerivative
    (sunWilsonActionFrom physicalSUNWilsonActionData
      plaquettes (physicalJetGaugeField tangent))
  ≡ sumRational plaquettes (λ plaquette →
      scalarSecondDerivative
        (loopObservable jetSUNGroup
          (wilsonPlaquetteValue scalarSecondJetOperations jetSUNTraceAuthority)
          (physicalJetGaugeField tangent)
          (physicalPlaquetteBoundary plaquette)))
scalarSecondDerivativeWilsonFold [] tangent = scalarSecondDerivativeZero
scalarSecondDerivativeWilsonFold (plaquette ∷ plaquettes) tangent =
  trans
    (scalarSecondDerivativeAdd
      (loopObservable jetSUNGroup
        (wilsonPlaquetteValue scalarSecondJetOperations jetSUNTraceAuthority)
        (physicalJetGaugeField tangent)
        (physicalPlaquetteBoundary plaquette))
      (sunWilsonActionFrom physicalSUNWilsonActionData
        plaquettes (physicalJetGaugeField tangent)))
    (cong
      (_+_ (scalarSecondDerivative
        (loopObservable jetSUNGroup
          (wilsonPlaquetteValue scalarSecondJetOperations jetSUNTraceAuthority)
          (physicalJetGaugeField tangent)
          (physicalPlaquetteBoundary plaquette))))
      (scalarSecondDerivativeWilsonFold plaquettes tangent))

physicalJetWilsonAction : PhysicalSU2Tangent4 → ScalarSecondJet
physicalJetWilsonAction tangent =
  sunWilsonAction physicalSUNWilsonActionData (physicalJetGaugeField tangent)

genericSUNWilsonActionSecondVariationEqualsLiteralFold : ∀ tangent →
  scalarSecondDerivative (physicalJetWilsonAction tangent)
  ≡ literalWilsonHessianPositivePlaneFold tangent
genericSUNWilsonActionSecondVariationEqualsLiteralFold tangent =
  trans
    (scalarSecondDerivativeWilsonFold physicalPlaquettes tangent)
    (trans
      (sumRationalCong physicalPlaquettes
        (λ plaquette →
          scalarSecondDerivative
            (loopObservable jetSUNGroup
              (wilsonPlaquetteValue scalarSecondJetOperations jetSUNTraceAuthority)
              (physicalJetGaugeField tangent)
              (physicalPlaquetteBoundary plaquette)))
        (λ where
          (pair plane site) →
            literalPlaquetteWilsonSecondVariation tangent plane site)
        (λ where
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
