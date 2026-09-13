module DASHI.Moonshine.Monster3BFiniteSchrodingerArbitraryWeylExact where

------------------------------------------------------------------------
-- ARBITRARY X6 WEYL RELATION FOR THE FINITE SCHRODINGER MODEL
--
-- Generator-level translation/modulation Weyl relations were already proved.
-- The full Heisenberg action constructed in
-- Monster3BFiniteSchrodingerHeisenbergActionExact needs the corresponding law
-- for arbitrary translation and modulation vectors a,b : X6.
--
-- This owner proves:
--
--   T_a T_A = T_(a+A)
--   M_b M_B = M_(b+B)
--   M_b T_a = zeta^(b.a) T_a M_b
--
-- pointwise on the exact Q(zeta_3)-valued function carrier, and rewrites the
-- arbitrary Heisenberg action as zeta^c T_a M_b.  It deliberately leaves the
-- final rho(gh)=rho(g)rho(h) theorem to the next one-line structural compiler;
-- generator relations alone do not count as that theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Rational.Tactic.RingSolver using (solve)
open import DASHI.Algebra.Trit using (Trit)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BF3AlgebraExact as F3
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BFiniteHeisenbergDotBilinearityExact as Dot
import DASHI.Moonshine.Monster3BFiniteHeisenbergInverseExact as Inv
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as Schrodinger
import DASHI.Moonshine.Monster3BFiniteSchrodingerHeisenbergActionExact as Action

infixl 6 _⊕_
_⊕_ : Trit → Trit → Trit
_⊕_ = G._+3_

------------------------------------------------------------------------
-- 1. Attribution.
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
  "standard Weyl/finite Fourier calibration; not authority for the repository-specific arbitrary-X6 proof"
  Attribution.publicAttribution

terrasAttribution = Snowball.canonicalSourceRoleSnowballReceipt terras

------------------------------------------------------------------------
-- 2. Arbitrary vector subtraction composes exactly.
------------------------------------------------------------------------

sub3Composition : (x a b : Trit) →
  (x ⊕ G.negate3 a) ⊕ G.negate3 b
  ≡ x ⊕ G.negate3 (a ⊕ b)
sub3Composition x a b =
  trans
    (F3.plusAssoc x (G.negate3 a) (G.negate3 b))
    (cong (λ t → x ⊕ t) (sym (F3.negateAdd a b)))

translationByVectorComposition :
  (a b x : G.X6) →
  Action.translateByVector b (Action.translateByVector a x)
  ≡ Action.translateByVector (H.addX6 a b) x
translationByVectorComposition
  (G.x6 a0 a1 a2 a3 a4 a5)
  (G.x6 b0 b1 b2 b3 b4 b5)
  (G.x6 x0 x1 x2 x3 x4 x5)
  rewrite sub3Composition x0 a0 b0
        | sub3Composition x1 a1 b1
        | sub3Composition x2 a2 b2
        | sub3Composition x3 a3 b3
        | sub3Composition x4 a4 b4
        | sub3Composition x5 a5 b5 = refl

------------------------------------------------------------------------
-- 3. Dot product through arbitrary translation.
------------------------------------------------------------------------

dotTranslateByVector : (b a x : G.X6) →
  H.dot6 b (Action.translateByVector a x)
  ≡ H.dot6 b x ⊕ G.negate3 (H.dot6 b a)
dotTranslateByVector b a x =
  trans
    (Dot.dotAddRight b x (H.negX6 a))
    (cong (λ t → H.dot6 b x ⊕ t) (Inv.dotNegRight b a))

cancelAround : (a b : Trit) → a ⊕ (b ⊕ G.negate3 a) ≡ b
cancelAround a b =
  trans
    (Dot.moveMiddle a b (G.negate3 a))
    (trans
      (cong (λ t → b ⊕ t) (F3.plusInverseRight a))
      (F3.plusRightZero b))

dotTranslationCancellation : (b a x : G.X6) →
  H.dot6 b a ⊕ H.dot6 b (Action.translateByVector a x)
  ≡ H.dot6 b x
dotTranslationCancellation b a x =
  trans
    (cong (λ t → H.dot6 b a ⊕ t) (dotTranslateByVector b a x))
    (cancelAround (H.dot6 b a) (H.dot6 b x))

------------------------------------------------------------------------
-- 4. Arbitrary translation and modulation operators.
------------------------------------------------------------------------

arbitraryTranslation :
  G.X6 → Schrodinger.SchrodingerFunction → Schrodinger.SchrodingerFunction
arbitraryTranslation a f x = f (Action.translateByVector a x)

arbitraryModulation :
  G.X6 → Schrodinger.SchrodingerFunction → Schrodinger.SchrodingerFunction
arbitraryModulation b f x =
  C3.multiply (Schrodinger.phase (H.dot6 b x)) (f x)

multiplyAssociative :
  (a b z : C3.Cyclotomic3) →
  C3.multiply a (C3.multiply b z) ≡ C3.multiply (C3.multiply a b) z
multiplyAssociative
  (C3.cyclotomic3 a0 a1)
  (C3.cyclotomic3 b0 b1)
  (C3.cyclotomic3 z0 z1) =
  C3.cyclotomic3Ext
    (solve (a0 ∷ a1 ∷ b0 ∷ b1 ∷ z0 ∷ z1 ∷ []))
    (solve (a0 ∷ a1 ∷ b0 ∷ b1 ∷ z0 ∷ z1 ∷ []))

arbitraryTranslationComposition :
  (a b : G.X6) →
  (f : Schrodinger.SchrodingerFunction) → (x : G.X6) →
  arbitraryTranslation a (arbitraryTranslation b f) x
  ≡ arbitraryTranslation (H.addX6 a b) f x
arbitraryTranslationComposition a b f x =
  cong f (translationByVectorComposition a b x)

arbitraryModulationComposition :
  (a b : G.X6) →
  (f : Schrodinger.SchrodingerFunction) → (x : G.X6) →
  arbitraryModulation a (arbitraryModulation b f) x
  ≡ arbitraryModulation (H.addX6 a b) f x
arbitraryModulationComposition a b f x =
  trans
    (multiplyAssociative
      (Schrodinger.phase (H.dot6 a x))
      (Schrodinger.phase (H.dot6 b x))
      (f x))
    (trans
      (cong
        (λ p → C3.multiply p (f x))
        (Action.phaseProduct (H.dot6 a x) (H.dot6 b x)))
      (cong
        (λ e → C3.multiply (Schrodinger.phase e) (f x))
        (sym (Dot.dotAddLeft a b x))))

------------------------------------------------------------------------
-- 5. Arbitrary Weyl law.
------------------------------------------------------------------------

arbitraryWeylRelation :
  (b a : G.X6) →
  (f : Schrodinger.SchrodingerFunction) → (x : G.X6) →
  arbitraryModulation b (arbitraryTranslation a f) x
  ≡ Schrodinger.cyclotomicScaleFunction
      (Schrodinger.phase (H.dot6 b a))
      (arbitraryTranslation a (arbitraryModulation b f)) x
arbitraryWeylRelation b a f x =
  let
    translated = Action.translateByVector a x
    ba = H.dot6 b a
    bt = H.dot6 b translated
  in
  trans
    (cong
      (λ e → C3.multiply (Schrodinger.phase e) (f translated))
      (sym (dotTranslationCancellation b a x)))
    (trans
      (cong
        (λ p → C3.multiply p (f translated))
        (sym (Action.phaseProduct ba bt)))
      (sym
        (multiplyAssociative
          (Schrodinger.phase ba)
          (Schrodinger.phase bt)
          (f translated))))

------------------------------------------------------------------------
-- 6. The full Heisenberg formula is exactly central phase * T_a M_b.
------------------------------------------------------------------------

heisenbergActionFactorsThroughWeyl :
  (g : H.Heisenberg6) →
  (f : Schrodinger.SchrodingerFunction) → (x : G.X6) →
  Action.heisenbergAction g f x
  ≡ Schrodinger.cyclotomicScaleFunction
      (Schrodinger.phase (H.centralPhase g))
      (arbitraryTranslation
        (H.translationPart (H.quotient g))
        (arbitraryModulation (H.modulationPart (H.quotient g)) f)) x
heisenbergActionFactorsThroughWeyl
  (H.heisenberg6 (H.symplectic12 a b) c) f x =
  let
    translated = Action.translateByVector a x
    exponent = H.dot6 b translated
  in
  trans
    (cong
      (λ p → C3.multiply p (f translated))
      (sym (Action.phaseProduct c exponent)))
    (sym
      (multiplyAssociative
        (Schrodinger.phase c)
        (Schrodinger.phase exponent)
        (f translated)))

------------------------------------------------------------------------
-- 7. WrongType / non-promotion.
------------------------------------------------------------------------

data GeneratorWeylCreatesArbitraryWeyl : Set where
data ArbitraryWeylCreatesFullHeisenbergActionLaw : Set where
data QidCreatesWeyl : Set where
data DeweyCreatesWeyl : Set where
data OeisCreatesWeyl : Set where

generatorWeylDoesNotCreateArbitraryWeyl : GeneratorWeylCreatesArbitraryWeyl → ⊥
generatorWeylDoesNotCreateArbitraryWeyl ()

arbitraryWeylDoesNotCreateFullHeisenbergActionLaw :
  ArbitraryWeylCreatesFullHeisenbergActionLaw → ⊥
arbitraryWeylDoesNotCreateFullHeisenbergActionLaw ()

qidDoesNotCreateWeyl : QidCreatesWeyl → ⊥
qidDoesNotCreateWeyl ()

deweyDoesNotCreateWeyl : DeweyCreatesWeyl → ⊥
deweyDoesNotCreateWeyl ()

oeisDoesNotCreateWeyl : OeisCreatesWeyl → ⊥
oeisDoesNotCreateWeyl ()

------------------------------------------------------------------------
-- 8. Snowball coordinates remain non-promoting.
------------------------------------------------------------------------

record ArbitraryWeylExternalCoordinates : Set where
  constructor arbitrary-weyl-external-coordinates
  field
    groupRepresentationQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasWeylAuthority : Bool
open ArbitraryWeylExternalCoordinates public

canonicalArbitraryWeylExternalCoordinates : ArbitraryWeylExternalCoordinates
canonicalArbitraryWeylExternalCoordinates =
  arbitrary-weyl-external-coordinates
    "Q1055807"
    "Q1057968"
    "512.22"
    "512.23"
    "A005052 remains numerical provenance for 90 = 10*3^2 only; it has no arbitrary Weyl, Heisenberg action-law, FDRep, trace, character, or intertwiner authority"
    false

------------------------------------------------------------------------
-- 9. Pareto frontier.
------------------------------------------------------------------------

record ArbitraryWeylFrontier : Set where
  constructor arbitrary-weyl-frontier
  field
    arbitraryTranslationPaid : Bool
    arbitraryModulationPaid : Bool
    arbitraryTranslationCompositionPaid : Bool
    arbitraryModulationCompositionPaid : Bool
    arbitraryWeylPaid : Bool
    actionFactorizationPaid : Bool
    fullHeisenbergActionLawPaid : Bool
    nextResidual : String
open ArbitraryWeylFrontier public

currentArbitraryWeylFrontier : ArbitraryWeylFrontier
currentArbitraryWeylFrontier =
  arbitrary-weyl-frontier
    true true true true true true false
    "use arbitraryTranslationComposition, arbitraryModulationComposition, arbitraryWeylRelation, phaseProduct, and the already-proved central-extension cocycle to prove Action.FullHeisenbergActionLawReceipt. This is now group-law/operator bookkeeping; no coordinate-by-coordinate F3 expansion is needed. After that, package the exact 729-dimensional representation for mathlib FDRep and prove class-character/trace agreement. QID/Dewey/OEIS coordinates and source citations do not create the action law or representation transport."
