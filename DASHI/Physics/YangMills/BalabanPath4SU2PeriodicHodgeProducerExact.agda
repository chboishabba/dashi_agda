module DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; _+_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (PhysicalBlockL; physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (SiteField; sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumRationalAdd)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanSU2WilsonPlaquetteSecondJetExact using
  (Lie3; lie3; x; y; z; _·v_; normSqV)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicHodgeExact
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
gaugeLie3Inner left right =
  siteSum4 (λ site → left site ·v right site)

sumRationalThreeTerms : ∀ {A : Set} values first second third →
  sumRational values (λ value →
    first value + (second value + third value))
  ≡ sumRational values first
    + (sumRational values second + sumRational values third)
sumRationalThreeTerms values first second third =
  trans
    (sumRationalAdd values first (λ value → second value + third value))
    (cong₂ _+_ refl (sumRationalAdd values second third))

siteSum4ThreeTerms : ∀ first second third →
  siteSum4 (λ site → first site + (second site + third site))
  ≡ siteSum4 first + (siteSum4 second + siteSum4 third)
siteSum4ThreeTerms first second third =
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
    (symSiteSplit)
    (sumRationalCong (physicalBlockSites side4) _ _
      (λ site → ℚRing.solve-∀
        (literalPeriodicDivergenceScalar
          (componentScalarBondField tangent component1) site)
        (literalPeriodicDivergenceScalar
          (componentScalarBondField tangent component2) site)
        (literalPeriodicDivergenceScalar
          (componentScalarBondField tangent component3) site)
        (x (gauge site)) (y (gauge site)) (z (gauge site))))
  where
  symSiteSplit =
    Relation.Binary.PropositionalEquality.sym
      (siteSum4ThreeTerms
        (λ site →
          literalPeriodicDivergenceScalar
            (componentScalarBondField tangent component1) site * x (gauge site))
        (λ site →
          literalPeriodicDivergenceScalar
            (componentScalarBondField tangent component2) site * y (gauge site))
        (λ site →
          literalPeriodicDivergenceScalar
            (componentScalarBondField tangent component3) site * z (gauge site)))

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

literalCodifferentialEqualsPeriodicDivergence : ∀ tangent site →
  literalCodifferential tangent site ≡ literalPeriodicDivergence tangent site
literalCodifferentialEqualsPeriodicDivergence tangent site = refl

literalGaugeFixingEnergy : PhysicalSU2Tangent4 → ℚ
literalGaugeFixingEnergy tangent =
  gaugeLie3Inner
    (literalPeriodicDivergence tangent)
    (literalPeriodicDivergence tangent)

literalGaugeFixingFoldEqualsDivergenceFold : ∀ tangent →
  literalGaugeFixingEnergy tangent
  ≡ gaugeLie3Inner
      (literalCodifferential tangent)
      (literalCodifferential tangent)
literalGaugeFixingFoldEqualsDivergenceFold tangent = refl

literalGaugeFixingEqualsDivergenceEnergy : ∀ tangent →
  literalGaugeFixingEnergy tangent
  ≡ gaugeLie3Inner
      (literalPeriodicDivergence tangent)
      (literalPeriodicDivergence tangent)
literalGaugeFixingEqualsDivergenceEnergy tangent = refl

------------------------------------------------------------------------
-- Lift the scalar Hodge theorem through the three Lie-algebra components.
------------------------------------------------------------------------

literalCurlNormSqComponentExpansion : ∀ tangent plane site →
  Plaquette.literalPlaquetteCurlNormSq tangent plane site
  ≡ curlScalar component1 + (curlScalar component2 + curlScalar component3)
  where
  curlScalar : SU2Component → ℚ
  curlScalar component =
    let field = componentScalarBondField tangent component in
    let first = positivePlaneFirst plane in
    let second = positivePlaneSecond plane in
    let value =
      forwardDifference4 first (field second) site
      Data.Rational._-_
      forwardDifference4 second (field first) site
    in value * value
literalCurlNormSqComponentExpansion tangent plane site =
  ℚRing.solve-∀
    (forwardDifference4 (positivePlaneFirst plane)
      (componentScalarBondField tangent component1
        (positivePlaneSecond plane)) site)
    (forwardDifference4 (positivePlaneSecond plane)
      (componentScalarBondField tangent component1
        (positivePlaneFirst plane)) site)
    (forwardDifference4 (positivePlaneFirst plane)
      (componentScalarBondField tangent component2
        (positivePlaneSecond plane)) site)
    (forwardDifference4 (positivePlaneSecond plane)
      (componentScalarBondField tangent component2
        (positivePlaneFirst plane)) site)
    (forwardDifference4 (positivePlaneFirst plane)
      (componentScalarBondField tangent component3
        (positivePlaneSecond plane)) site)
    (forwardDifference4 (positivePlaneSecond plane)
      (componentScalarBondField tangent component3
        (positivePlaneFirst plane)) site)

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
        (siteSum4ThreeTerms
          (λ site → curlTerm component1 plane site)
          (λ site → curlTerm component2 plane site)
          (λ site → curlTerm component3 plane site))))
    (sumRationalThreeTerms positivePlaquettePlanes4
      (λ plane → curlPlaneEnergy plane
        (componentScalarBondField tangent component1))
      (λ plane → curlPlaneEnergy plane
        (componentScalarBondField tangent component2))
      (λ plane → curlPlaneEnergy plane
        (componentScalarBondField tangent component3)))
  where
  curlTerm : SU2Component → PositivePlaquettePlane4 →
    PhysicalBlockL side4 → ℚ
  curlTerm component plane site =
    let field = componentScalarBondField tangent component in
    let first = positivePlaneFirst plane in
    let second = positivePlaneSecond plane in
    let value =
      forwardDifference4 first (field second) site
      Data.Rational._-_
      forwardDifference4 second (field first) site
    in value * value

literalDivergenceNormSqComponentExpansion : ∀ tangent site →
  normSqV (literalPeriodicDivergence tangent site)
  ≡ divSq component1 + (divSq component2 + divSq component3)
  where
  divSq : SU2Component → ℚ
  divSq component =
    let value = literalPeriodicDivergenceScalar
      (componentScalarBondField tangent component) site
    in value * value
literalDivergenceNormSqComponentExpansion tangent site =
  ℚRing.solve-∀
    (literalPeriodicDivergenceScalar
      (componentScalarBondField tangent component1) site)
    (literalPeriodicDivergenceScalar
      (componentScalarBondField tangent component2) site)
    (literalPeriodicDivergenceScalar
      (componentScalarBondField tangent component3) site)

literalDivergenceEnergyComponentFold : ∀ tangent →
  literalGaugeFixingEnergy tangent
  ≡ componentDivergenceEnergy (componentScalarBondField tangent component1)
    + (componentDivergenceEnergy (componentScalarBondField tangent component2)
    + componentDivergenceEnergy (componentScalarBondField tangent component3))
literalDivergenceEnergyComponentFold tangent =
  trans
    (sumRationalCong (physicalBlockSites side4) _ _
      (literalDivergenceNormSqComponentExpansion tangent))
    (siteSum4ThreeTerms
      (λ site → let value = literalPeriodicDivergenceScalar
        (componentScalarBondField tangent component1) site in value * value)
      (λ site → let value = literalPeriodicDivergenceScalar
        (componentScalarBondField tangent component2) site in value * value)
      (λ site → let value = literalPeriodicDivergenceScalar
        (componentScalarBondField tangent component3) site in value * value))

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
      (ℚRing.solve-∀
        (componentCurlEnergy (componentScalarBondField tangent component1))
        (componentCurlEnergy (componentScalarBondField tangent component2))
        (componentCurlEnergy (componentScalarBondField tangent component3))
        (componentDivergenceEnergy (componentScalarBondField tangent component1))
        (componentDivergenceEnergy (componentScalarBondField tangent component2))
        (componentDivergenceEnergy (componentScalarBondField tangent component3)))
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
