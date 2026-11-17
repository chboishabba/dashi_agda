module DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL; physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (SiteField; sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumRationalAdd)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanSU2WilsonPlaquetteSecondJetExact using
  (Lie3; lie3; x; y; z; _·v_; normSqV)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
  using (siteSum4; forwardDifference4)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using
    ( ScalarBondField4
    ; literalPeriodicDivergenceScalar
    ; literalNegativeForwardGradientScalar
    ; scalarBondInner
    ; scalarSiteInner
    ; periodicDivergenceGradientAdjoint
    )
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicHodgeExact
  using
    ( curlPlaneEnergy
    ; componentCurlEnergy
    ; componentDivergenceEnergy
    ; componentPeriodicDifferenceEnergy
    ; componentDiscreteCurlDivergenceHodgeIdentity
    )
import DASHI.Physics.YangMills.BalabanPath4SU2LiteralPlaquetteLiftExact as Plaquette

------------------------------------------------------------------------
-- Component views of the physical tangent.
------------------------------------------------------------------------

componentScalarBondField : PhysicalSU2Tangent4 → SU2Component → ScalarBondField4
componentScalarBondField tangent component axis site =
  physicalTangentComponent tangent component axis site

Lie3SiteField : Set
Lie3SiteField = PhysicalBlockL side4 → Lie3

lie3Component : SU2Component → Lie3 → ℚ
lie3Component component1 value = x value
lie3Component component2 value = y value
lie3Component component3 value = z value

literalPeriodicDivergence : PhysicalSU2Tangent4 → Lie3SiteField
literalPeriodicDivergence tangent site =
  lie3
    (literalPeriodicDivergenceScalar
      (componentScalarBondField tangent component1) site)
    (literalPeriodicDivergenceScalar
      (componentScalarBondField tangent component2) site)
    (literalPeriodicDivergenceScalar
      (componentScalarBondField tangent component3) site)

literalNegativeForwardGradient : Lie3SiteField → PhysicalSU2Tangent4
literalNegativeForwardGradient gauge component (pair site axis) =
  literalNegativeForwardGradientScalar
    (λ current → lie3Component component (gauge current)) axis site

physicalTangentInner : PhysicalSU2Tangent4 → PhysicalSU2Tangent4 → ℚ
physicalTangentInner left right =
  scalarBondInner
    (componentScalarBondField left component1)
    (componentScalarBondField right component1)
  + (scalarBondInner
      (componentScalarBondField left component2)
      (componentScalarBondField right component2)
  + scalarBondInner
      (componentScalarBondField left component3)
      (componentScalarBondField right component3))

gaugeLie3Inner : Lie3SiteField → Lie3SiteField → ℚ
gaugeLie3Inner left right = siteSum4 (λ site → left site ·v right site)

sumRationalThreeTerms : ∀ {A : Set} values first second third →
  sumRational values (λ value → first value + (second value + third value))
  ≡ sumRational values first
    + (sumRational values second + sumRational values third)
sumRationalThreeTerms values first second third =
  trans
    (sumRationalAdd values first (λ value → second value + third value))
    (cong₂ _+_ refl (sumRationalAdd values second third))

siteSum4ThreeComponentTerms : ∀ first second third →
  siteSum4 (λ site → first site + (second site + third site))
  ≡ siteSum4 first + (siteSum4 second + siteSum4 third)
siteSum4ThreeComponentTerms first second third =
  sumRationalThreeTerms (physicalBlockSites side4) first second third

literalDivergencePairingComponentFold : ∀ tangent gauge →
  scalarSiteInner
    (literalPeriodicDivergenceScalar
      (componentScalarBondField tangent component1))
    (λ site → x (gauge site))
  + (scalarSiteInner
      (literalPeriodicDivergenceScalar
        (componentScalarBondField tangent component2))
      (λ site → y (gauge site))
  + scalarSiteInner
      (literalPeriodicDivergenceScalar
        (componentScalarBondField tangent component3))
      (λ site → z (gauge site)))
  ≡ gaugeLie3Inner (literalPeriodicDivergence tangent) gauge
literalDivergencePairingComponentFold tangent gauge =
  trans
    (sym
      (siteSum4ThreeComponentTerms
        (λ site →
          literalPeriodicDivergenceScalar
            (componentScalarBondField tangent component1) site * x (gauge site))
        (λ site →
          literalPeriodicDivergenceScalar
            (componentScalarBondField tangent component2) site * y (gauge site))
        (λ site →
          literalPeriodicDivergenceScalar
            (componentScalarBondField tangent component3) site * z (gauge site))))
    (sumRationalCong (physicalBlockSites side4) _ _
      (λ site → ℚRing.solve-∀))

periodicDivergenceGradientAdjointSU2 : ∀ tangent gauge →
  physicalTangentInner tangent (literalNegativeForwardGradient gauge)
  ≡ gaugeLie3Inner (literalPeriodicDivergence tangent) gauge
periodicDivergenceGradientAdjointSU2 tangent gauge =
  trans
    (cong₂ _+_
      (periodicDivergenceGradientAdjoint
        (componentScalarBondField tangent component1)
        (λ site → x (gauge site)))
      (cong₂ _+_
        (periodicDivergenceGradientAdjoint
          (componentScalarBondField tangent component2)
          (λ site → y (gauge site)))
        (periodicDivergenceGradientAdjoint
          (componentScalarBondField tangent component3)
          (λ site → z (gauge site)))))
    (literalDivergencePairingComponentFold tangent gauge)

literalCodifferential : PhysicalSU2Tangent4 → Lie3SiteField
literalCodifferential = literalPeriodicDivergence

literalCodifferentialEqualsPeriodicDivergenceSU2 : ∀ tangent site →
  literalCodifferential tangent site ≡ literalPeriodicDivergence tangent site
literalCodifferentialEqualsPeriodicDivergenceSU2 tangent site = refl

literalGaugeFixingEnergy : PhysicalSU2Tangent4 → ℚ
literalGaugeFixingEnergy tangent =
  gaugeLie3Inner
    (literalPeriodicDivergence tangent)
    (literalPeriodicDivergence tangent)

literalGaugeFixingFoldEqualsDivergenceFoldSU2 : ∀ tangent →
  literalGaugeFixingEnergy tangent
  ≡ gaugeLie3Inner
      (literalCodifferential tangent)
      (literalCodifferential tangent)
literalGaugeFixingFoldEqualsDivergenceFoldSU2 tangent = refl

literalGaugeFixingEqualsDivergenceEnergy : ∀ tangent →
  literalGaugeFixingEnergy tangent
  ≡ gaugeLie3Inner
      (literalPeriodicDivergence tangent)
      (literalPeriodicDivergence tangent)
literalGaugeFixingEqualsDivergenceEnergy tangent = refl

------------------------------------------------------------------------
-- Lift the scalar Hodge theorem through the three Lie-algebra components.
------------------------------------------------------------------------

componentCurlTerm :
  PhysicalSU2Tangent4 → SU2Component → PositivePlaquettePlane4 →
  PhysicalBlockL side4 → ℚ
componentCurlTerm tangent component plane site =
  let field = componentScalarBondField tangent component in
  let first = positivePlaneFirst plane in
  let second = positivePlaneSecond plane in
  let value =
    forwardDifference4 first (field second) site
    - forwardDifference4 second (field first) site
  in value * value

literalCurlNormSqComponentExpansion : ∀ tangent plane site →
  Plaquette.literalPlaquetteCurlNormSq tangent plane site
  ≡ componentCurlTerm tangent component1 plane site
    + (componentCurlTerm tangent component2 plane site
    + componentCurlTerm tangent component3 plane site)
literalCurlNormSqComponentExpansion tangent plane site =
  ℚRing.solve-∀

literalCurlEnergyComponentFold : ∀ tangent →
  Plaquette.literalDiscreteCurlEnergy tangent
  ≡ componentCurlEnergy (componentScalarBondField tangent component1)
    + (componentCurlEnergy (componentScalarBondField tangent component2)
    + componentCurlEnergy (componentScalarBondField tangent component3))
literalCurlEnergyComponentFold tangent =
  trans
    (sumRationalCong positivePlaquettePlanes4 _ _ (λ plane →
      trans
        (sumRationalCong (physicalBlockSites side4) _ _
          (literalCurlNormSqComponentExpansion tangent plane))
        (siteSum4ThreeComponentTerms
          (componentCurlTerm tangent component1 plane)
          (componentCurlTerm tangent component2 plane)
          (componentCurlTerm tangent component3 plane))))
    (sumRationalThreeTerms positivePlaquettePlanes4
      (λ plane → curlPlaneEnergy plane
        (componentScalarBondField tangent component1))
      (λ plane → curlPlaneEnergy plane
        (componentScalarBondField tangent component2))
      (λ plane → curlPlaneEnergy plane
        (componentScalarBondField tangent component3)))

componentDivergenceSq :
  PhysicalSU2Tangent4 → SU2Component → PhysicalBlockL side4 → ℚ
componentDivergenceSq tangent component site =
  let value = literalPeriodicDivergenceScalar
    (componentScalarBondField tangent component) site
  in value * value

literalDivergenceNormSqComponentExpansion : ∀ tangent site →
  normSqV (literalPeriodicDivergence tangent site)
  ≡ componentDivergenceSq tangent component1 site
    + (componentDivergenceSq tangent component2 site
    + componentDivergenceSq tangent component3 site)
literalDivergenceNormSqComponentExpansion tangent site =
  ℚRing.solve-∀

literalDivergenceEnergyComponentFold : ∀ tangent →
  literalGaugeFixingEnergy tangent
  ≡ componentDivergenceEnergy (componentScalarBondField tangent component1)
    + (componentDivergenceEnergy (componentScalarBondField tangent component2)
    + componentDivergenceEnergy (componentScalarBondField tangent component3))
literalDivergenceEnergyComponentFold tangent =
  trans
    (sumRationalCong (physicalBlockSites side4) _ _
      (literalDivergenceNormSqComponentExpansion tangent))
    (siteSum4ThreeComponentTerms
      (componentDivergenceSq tangent component1)
      (componentDivergenceSq tangent component2)
      (componentDivergenceSq tangent component3))

physicalPeriodicReferenceDifferenceEnergy : PhysicalSU2Tangent4 → ℚ
physicalPeriodicReferenceDifferenceEnergy tangent =
  componentPeriodicDifferenceEnergy
    (componentScalarBondField tangent component1)
  + (componentPeriodicDifferenceEnergy
      (componentScalarBondField tangent component2)
  + componentPeriodicDifferenceEnergy
      (componentScalarBondField tangent component3))

threeComponentDifferenceEnergyFoldExact : ∀ tangent →
  physicalPeriodicReferenceDifferenceEnergy tangent
  ≡ physicalPeriodicReferenceDifferenceEnergy tangent
threeComponentDifferenceEnergyFoldExact tangent = refl

discreteCurlDivergenceHodgeIdentity : ∀ tangent →
  Plaquette.literalDiscreteCurlEnergy tangent + literalGaugeFixingEnergy tangent
  ≡ physicalPeriodicReferenceDifferenceEnergy tangent
discreteCurlDivergenceHodgeIdentity tangent =
  trans
    (cong₂ _+_
      (literalCurlEnergyComponentFold tangent)
      (literalDivergenceEnergyComponentFold tangent))
    (trans
      (ℚRing.solve-∀)
      (cong₂ _+_
        (componentDiscreteCurlDivergenceHodgeIdentity
          (componentScalarBondField tangent component1))
        (cong₂ _+_
          (componentDiscreteCurlDivergenceHodgeIdentity
            (componentScalarBondField tangent component2))
          (componentDiscreteCurlDivergenceHodgeIdentity
            (componentScalarBondField tangent component3)))))

path4SU2PeriodicDivergenceLevel : ProofLevel
path4SU2PeriodicDivergenceLevel = machineChecked

path4SU2PeriodicHodgeIdentityLevel : ProofLevel
path4SU2PeriodicHodgeIdentityLevel = machineChecked
