module DASHI.Moonshine.Monster3BFiniteSchrodingerHeisenbergActionExact where

------------------------------------------------------------------------
-- FULL FINITE HEISENBERG SCHRODINGER ACTION FORMULA ON X6 -> Q(zeta_3)
--
-- Existing owners already provide:
--   * the exact central-extension carrier Heisenberg6,
--   * its cocycle composition law,
--   * closed group laws,
--   * the exact Schrodinger function carrier,
--   * the six translation and six modulation generator actions.
--
-- This owner constructs the action for an arbitrary group coordinate
--
--   g = (a,b,c) in X6 x X6* x F3
--
-- using the cocycle convention already fixed by the repository:
--
--   (rho(a,b,c) f)(x)
--     = zeta^(c + b . (x-a)) f(x-a).
--
-- With compose(g,h) carrying the cocycle b_g . a_h, this convention restricts
-- to the existing translation/modulation generators.  The arbitrary-product
-- action law is kept as an explicit receipt below: constructing the formula
-- and checking generators does not silently manufacture a representation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Rational.Tactic.RingSolver using (solve)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BF3AlgebraExact as F3
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BFiniteHeisenbergGroupLawFrontierExact as GroupLaw
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as Schrodinger

------------------------------------------------------------------------
-- 1. Source attribution.
------------------------------------------------------------------------

terras : Attribution.AttributedSource
terras = Attribution.mkDOISource
  "Audrey Terras"
  "Fourier Analysis on Finite Groups and Applications"
  "Cambridge University Press"
  "1999"
  "10.1017/CBO9780511626265"
  "https://doi.org/10.1017/CBO9780511626265"
  Attribution.academicArticleSource
  "standard finite Fourier/Schrodinger calibration; not authority for this repository's concrete cocycle convention or proof transport"
  Attribution.publicAttribution

barracloughWilson : Attribution.AttributedSource
barracloughWilson = Attribution.mkDOISource
  "R. W. Barraclough and R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "Monster 3B-normalizer character calibration; not authority for the constructed X6 action law"
  Attribution.publicAttribution

terrasAttribution = Snowball.canonicalSourceRoleSnowballReceipt terras
barracloughWilsonAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughWilson

------------------------------------------------------------------------
-- 2. Exact vector translation by an arbitrary X6 coordinate.
------------------------------------------------------------------------

translateByVector : G.X6 → G.X6 → G.X6
translateByVector a x = H.addX6 x (H.negX6 a)

translateByZero : (x : G.X6) → translateByVector H.zeroX6 x ≡ x
translateByZero (G.x6 a0 a1 a2 a3 a4 a5)
  rewrite F3.plusRightZero a0 | F3.plusRightZero a1
        | F3.plusRightZero a2 | F3.plusRightZero a3
        | F3.plusRightZero a4 | F3.plusRightZero a5 = refl

translationBasisMatchesExistingInverse :
  (axis : G.Axis6) → (x : G.X6) →
  translateByVector (H.basis axis) x ≡ G.translateInverse axis x
translationBasisMatchesExistingInverse G.axis0 (G.x6 a0 a1 a2 a3 a4 a5)
  rewrite F3.plusComm a0 neg
        | F3.plusRightZero a1 | F3.plusRightZero a2
        | F3.plusRightZero a3 | F3.plusRightZero a4
        | F3.plusRightZero a5 = refl
translationBasisMatchesExistingInverse G.axis1 (G.x6 a0 a1 a2 a3 a4 a5)
  rewrite F3.plusRightZero a0 | F3.plusComm a1 neg
        | F3.plusRightZero a2 | F3.plusRightZero a3
        | F3.plusRightZero a4 | F3.plusRightZero a5 = refl
translationBasisMatchesExistingInverse G.axis2 (G.x6 a0 a1 a2 a3 a4 a5)
  rewrite F3.plusRightZero a0 | F3.plusRightZero a1
        | F3.plusComm a2 neg | F3.plusRightZero a3
        | F3.plusRightZero a4 | F3.plusRightZero a5 = refl
translationBasisMatchesExistingInverse G.axis3 (G.x6 a0 a1 a2 a3 a4 a5)
  rewrite F3.plusRightZero a0 | F3.plusRightZero a1
        | F3.plusRightZero a2 | F3.plusComm a3 neg
        | F3.plusRightZero a4 | F3.plusRightZero a5 = refl
translationBasisMatchesExistingInverse G.axis4 (G.x6 a0 a1 a2 a3 a4 a5)
  rewrite F3.plusRightZero a0 | F3.plusRightZero a1
        | F3.plusRightZero a2 | F3.plusRightZero a3
        | F3.plusComm a4 neg | F3.plusRightZero a5 = refl
translationBasisMatchesExistingInverse G.axis5 (G.x6 a0 a1 a2 a3 a4 a5)
  rewrite F3.plusRightZero a0 | F3.plusRightZero a1
        | F3.plusRightZero a2 | F3.plusRightZero a3
        | F3.plusRightZero a4 | F3.plusComm a5 neg = refl

------------------------------------------------------------------------
-- 3. Exact phase algebra reused by the arbitrary action.
------------------------------------------------------------------------

multiplyOne : (z : C3.Cyclotomic3) → C3.multiply C3.one z ≡ z
multiplyOne (C3.cyclotomic3 u v) =
  C3.cyclotomic3Ext (solve (u ∷ v ∷ [])) (solve (u ∷ v ∷ []))

multiplyDistributesAdd :
  (a x y : C3.Cyclotomic3) →
  C3.multiply a (Schrodinger.addC3 x y)
  ≡ Schrodinger.addC3 (C3.multiply a x) (C3.multiply a y)
multiplyDistributesAdd
  (C3.cyclotomic3 a b)
  (C3.cyclotomic3 x y)
  (C3.cyclotomic3 r s) =
  C3.cyclotomic3Ext
    (solve (a ∷ b ∷ x ∷ y ∷ r ∷ s ∷ []))
    (solve (a ∷ b ∷ x ∷ y ∷ r ∷ s ∷ []))

scalarsCommuteThroughAction :
  (phaseScalar externalScalar z : C3.Cyclotomic3) →
  C3.multiply phaseScalar (C3.multiply externalScalar z)
  ≡ C3.multiply externalScalar (C3.multiply phaseScalar z)
scalarsCommuteThroughAction
  (C3.cyclotomic3 p q)
  (C3.cyclotomic3 a b)
  (C3.cyclotomic3 x y) =
  C3.cyclotomic3Ext
    (solve (p ∷ q ∷ a ∷ b ∷ x ∷ y ∷ []))
    (solve (p ∷ q ∷ a ∷ b ∷ x ∷ y ∷ []))

phaseProduct : (left right : Trit) →
  C3.multiply (Schrodinger.phase left) (Schrodinger.phase right)
  ≡ Schrodinger.phase (G._+3_ left right)
phaseProduct neg neg = C3.cyclotomic3Ext (solve []) (solve [])
phaseProduct neg zer = C3.cyclotomic3Ext (solve []) (solve [])
phaseProduct neg pos = C3.cyclotomic3Ext (solve []) (solve [])
phaseProduct zer neg = C3.cyclotomic3Ext (solve []) (solve [])
phaseProduct zer zer = C3.cyclotomic3Ext (solve []) (solve [])
phaseProduct zer pos = C3.cyclotomic3Ext (solve []) (solve [])
phaseProduct pos neg = C3.cyclotomic3Ext (solve []) (solve [])
phaseProduct pos zer = C3.cyclotomic3Ext (solve []) (solve [])
phaseProduct pos pos = C3.cyclotomic3Ext (solve []) (solve [])

------------------------------------------------------------------------
-- 4. Full action formula on arbitrary Heisenberg6 coordinates.
------------------------------------------------------------------------

actionExponent : H.Heisenberg6 → G.X6 → Trit
actionExponent g x =
  G._+3_
    (H.centralPhase g)
    (H.dot6
      (H.modulationPart (H.quotient g))
      (translateByVector (H.translationPart (H.quotient g)) x))

heisenbergAction :
  H.Heisenberg6 → Schrodinger.SchrodingerFunction → Schrodinger.SchrodingerFunction
heisenbergAction g f x =
  C3.multiply
    (Schrodinger.phase (actionExponent g x))
    (f (translateByVector (H.translationPart (H.quotient g)) x))

------------------------------------------------------------------------
-- 5. The arbitrary formula agrees with every already-owned generator action.
------------------------------------------------------------------------

dotBasisIsCoordinate :
  (axis : G.Axis6) → (x : G.X6) →
  H.dot6 (H.basis axis) x ≡ G.coordinate axis x
dotBasisIsCoordinate G.axis0 (G.x6 a0 a1 a2 a3 a4 a5)
  rewrite F3.plusRightZero a0 = refl
dotBasisIsCoordinate G.axis1 (G.x6 a0 a1 a2 a3 a4 a5)
  rewrite F3.plusRightZero a1 = refl
dotBasisIsCoordinate G.axis2 (G.x6 a0 a1 a2 a3 a4 a5)
  rewrite F3.plusRightZero a2 = refl
dotBasisIsCoordinate G.axis3 (G.x6 a0 a1 a2 a3 a4 a5)
  rewrite F3.plusRightZero a3 = refl
dotBasisIsCoordinate G.axis4 (G.x6 a0 a1 a2 a3 a4 a5)
  rewrite F3.plusRightZero a4 = refl
dotBasisIsCoordinate G.axis5 (G.x6 a0 a1 a2 a3 a4 a5)
  rewrite F3.plusRightZero a5 = refl

identityActionPointwise :
  (f : Schrodinger.SchrodingerFunction) → (x : G.X6) →
  heisenbergAction H.identityH f x ≡ f x
identityActionPointwise f x
  rewrite translateByZero x | multiplyOne (f x) = refl

translationGeneratorAgreement :
  (axis : G.Axis6) → (f : Schrodinger.SchrodingerFunction) → (x : G.X6) →
  heisenbergAction (H.translationGenerator axis) f x
  ≡ Schrodinger.translationAction axis f x
translationGeneratorAgreement axis f x
  rewrite translationBasisMatchesExistingInverse axis x
        | multiplyOne (f (G.translateInverse axis x)) = refl

modulationGeneratorAgreement :
  (axis : G.Axis6) → (f : Schrodinger.SchrodingerFunction) → (x : G.X6) →
  heisenbergAction (H.modulationGenerator axis) f x
  ≡ Schrodinger.modulationAction axis f x
modulationGeneratorAgreement axis f x
  rewrite translateByZero x | dotBasisIsCoordinate axis x = refl

centralGeneratorAgreement :
  (centralPhase : Trit) → (f : Schrodinger.SchrodingerFunction) → (x : G.X6) →
  heisenbergAction (H.central centralPhase) f x
  ≡ C3.multiply (Schrodinger.phase centralPhase) (f x)
centralGeneratorAgreement centralPhase f x
  rewrite translateByZero x = refl

------------------------------------------------------------------------
-- 6. Exact Q(zeta_3)-linearity of every constructed operator.
------------------------------------------------------------------------

actionPreservesAddition :
  (g : H.Heisenberg6) →
  (f h : Schrodinger.SchrodingerFunction) →
  (x : G.X6) →
  heisenbergAction g (Schrodinger.addFunction f h) x
  ≡ Schrodinger.addFunction (heisenbergAction g f) (heisenbergAction g h) x
actionPreservesAddition g f h x =
  multiplyDistributesAdd
    (Schrodinger.phase (actionExponent g x))
    (f (translateByVector (H.translationPart (H.quotient g)) x))
    (h (translateByVector (H.translationPart (H.quotient g)) x))

actionPreservesCyclotomicScaling :
  (g : H.Heisenberg6) →
  (a : C3.Cyclotomic3) →
  (f : Schrodinger.SchrodingerFunction) →
  (x : G.X6) →
  heisenbergAction g (Schrodinger.cyclotomicScaleFunction a f) x
  ≡ Schrodinger.cyclotomicScaleFunction a (heisenbergAction g f) x
actionPreservesCyclotomicScaling g a f x =
  scalarsCommuteThroughAction
    (Schrodinger.phase (actionExponent g x))
    a
    (f (translateByVector (H.translationPart (H.quotient g)) x))

------------------------------------------------------------------------
-- 7. One remaining theorem payment before this formula becomes a group rep.
------------------------------------------------------------------------

record FullHeisenbergActionLawReceipt : Set where
  constructor full-heisenberg-action-law-receipt
  field
    actionCompositionPointwise :
      (g h : H.Heisenberg6) →
      (f : Schrodinger.SchrodingerFunction) →
      (x : G.X6) →
      heisenbergAction (H.compose g h) f x
      ≡ heisenbergAction g (heisenbergAction h f) x
open FullHeisenbergActionLawReceipt public

------------------------------------------------------------------------
-- 8. WrongType / non-promotion firewalls.
------------------------------------------------------------------------

data GeneratorActionsCreateFullGroupAction : Set where
data ConstructedFormulaCreatesActionLaw : Set where
data Degree729CreatesAction : Set where
data CharacterSignatureCreatesAction : Set where
data QidCreatesAction : Set where
data DeweyCreatesAction : Set where
data OeisCreatesAction : Set where

generatorActionsDoNotCreateFullGroupAction :
  GeneratorActionsCreateFullGroupAction → ⊥
generatorActionsDoNotCreateFullGroupAction ()

constructedFormulaDoesNotCreateActionLaw : ConstructedFormulaCreatesActionLaw → ⊥
constructedFormulaDoesNotCreateActionLaw ()

degree729DoesNotCreateAction : Degree729CreatesAction → ⊥
degree729DoesNotCreateAction ()

characterSignatureDoesNotCreateAction : CharacterSignatureCreatesAction → ⊥
characterSignatureDoesNotCreateAction ()

qidDoesNotCreateAction : QidCreatesAction → ⊥
qidDoesNotCreateAction ()

deweyDoesNotCreateAction : DeweyCreatesAction → ⊥
deweyDoesNotCreateAction ()

oeisDoesNotCreateAction : OeisCreatesAction → ⊥
oeisDoesNotCreateAction ()

------------------------------------------------------------------------
-- 9. Snowball coordinates remain non-promoting.
------------------------------------------------------------------------

record HeisenbergActionExternalCoordinates : Set where
  constructor heisenberg-action-external-coordinates
  field
    groupRepresentationQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasActionAuthority : Bool
open HeisenbergActionExternalCoordinates public

canonicalHeisenbergActionExternalCoordinates : HeisenbergActionExternalCoordinates
canonicalHeisenbergActionExternalCoordinates =
  heisenberg-action-external-coordinates
    "Q1055807"
    "Q1057968"
    "512.22"
    "512.23"
    "A005052 remains numerical provenance for 90 = 10*3^2 only; it has no Heisenberg action, cocycle, linearity, FDRep, trace, character, or intertwiner authority"
    false

------------------------------------------------------------------------
-- 10. Pareto frontier.
------------------------------------------------------------------------

record FiniteSchrodingerHeisenbergActionFrontier : Set where
  constructor finite-schrodinger-heisenberg-action-frontier
  field
    groupLawCarrierPaid : Bool
    actionFormulaConstructed : Bool
    identityActionPaid : Bool
    generatorCompatibilityPaid : Bool
    exactCyclotomicLinearityPaid : Bool
    fullActionLawPaid : Bool
    mathlibFDRepPackagingPaid : Bool
    classCharacterTraceAgreementPaid : Bool
    nextResidual : String
open FiniteSchrodingerHeisenbergActionFrontier public

currentFiniteSchrodingerHeisenbergActionFrontier :
  FiniteSchrodingerHeisenbergActionFrontier
currentFiniteSchrodingerHeisenbergActionFrontier =
  finite-schrodinger-heisenberg-action-frontier
    true true true true true
    false false false
    "prove FullHeisenbergActionLawReceipt for the explicit formula rho(a,b,c)f(x)=zeta^(c+b dot (x-a)) f(x-a), using the already-proved X6 additive laws, dot bilinearity, phaseProduct, and the central-extension cocycle b_g dot a_h. Only after that receipt is inhabited package the exact 729-dimensional carrier as the mathlib FDRep and prove the DASHI ExtraspecialClassKind character values agree with the mathlib trace. Terras/Barraclough-Wilson DOI, QID/Dewey/OEIS coordinates, generator compatibility, dimension 729, or matching character signatures do not create the full action law or FDRep transport."
