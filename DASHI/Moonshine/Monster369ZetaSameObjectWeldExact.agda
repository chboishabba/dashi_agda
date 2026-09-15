module DASHI.Moonshine.Monster369ZetaSameObjectWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.TriadicDepthOneCharacters as DepthOne
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BPhaseTransportExact as Phase
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.Base369Monster3BVOAActionPhaseAdapterBidiExact as VOAAdapter
import DASHI.Moonshine.Base369ZetaHeisenbergFiftyFourCarrierExact as Zeta54
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as LinearZeta
import DASHI.Wikimedia.IbrahimMonster3BLinearMultiplicityHomSpaceExact as Hom

------------------------------------------------------------------------
-- MONSTER / BASE369 ZETA SAME-OBJECT WELD
--
-- The useful common object here is the selected third-root phase zeta, not the
-- glyph by itself.  The repository already contains a literal chain:
--
--   depth-one C3 zeta
--      -> Monster 3B zeta phase
--      -> inertia phaseZeta
--      -> exact cyclotomic scalar C3.zeta
--      -> literal VOA phaseZeta eigenspace.
--
-- The first arrow is an exact finite Fourier/Monster phase chart.  The latter
-- two arrows are stronger: Base369Monster3BVOAActionPhaseAdapterBidiExact puts
-- the exact Q(zeta_3) scalar on the SAME literal VOA carrier and defines the
-- literal zeta sector as that dependent central eigenspace.
--
-- What is NOT yet paid is the representation-layer completion:
--   literal zeta eigenspace -> actual linear W_zeta,
--   finite Schrodinger H_zeta model -> that same actual W_zeta,
--   S_zeta = Hom_E(H_zeta,W_zeta),
--   evaluation/intertwiner -> 12 + 78 decomposition.
--
-- Base369's 54-site zeta-sheet carrier is retained only as a conjugate-sheet
-- chart.  Its constructor name `zetaSheet` is not promoted to literal equality
-- with the cyclotomic scalar C3.zeta or with W_zeta.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Symbolic C3 zeta is already aligned exactly with the Monster phase chart.
------------------------------------------------------------------------

fourierZetaIsDepthOnePositivePhase : Fourier.zeta ≡ DepthOne.phase1
fourierZetaIsDepthOnePositivePhase = refl

fourierZetaMapsToMonsterZeta :
  Fourier.phaseToMonster Fourier.zeta ≡ Phase.zetaPhase
fourierZetaMapsToMonsterZeta = refl

fourierInverseZetaMapsToMonsterZetaSquared :
  Fourier.phaseToMonster (Fourier.inversePhase Fourier.zeta)
  ≡ Phase.zetaSquaredPhase
fourierInverseZetaMapsToMonsterZetaSquared = refl

------------------------------------------------------------------------
-- 2. The inertia phase chart uses the exact Q(zeta_3) scalar.
------------------------------------------------------------------------

inertiaZetaMapsToExactCyclotomicZeta :
  VOAAdapter.phaseCyclotomic Inertia.phaseZeta ≡ C3.zeta
inertiaZetaMapsToExactCyclotomicZeta = VOAAdapter.phaseZetaIsZeta

inertiaZetaSquaredMapsToExactCyclotomicZetaSquared :
  VOAAdapter.phaseCyclotomic Inertia.phaseZetaSquared ≡ C3.zetaSquared
inertiaZetaSquaredMapsToExactCyclotomicZetaSquared =
  VOAAdapter.phaseZetaSquaredIsZetaSquared

cyclotomicConjugationMatchesSelectedInverseScalar :
  C3.conjugate (VOAAdapter.phaseCyclotomic Inertia.phaseZeta)
  ≡ VOAAdapter.phaseCyclotomic Inertia.phaseZetaSquared
cyclotomicConjugationMatchesSelectedInverseScalar = C3.conjugateZetaIsZetaSquared

------------------------------------------------------------------------
-- 3. On any inhabited literal VOA phase source, the chosen zeta sector is
--    definitionally the dependent phaseZeta eigenspace on that SAME carrier.
------------------------------------------------------------------------

literalVOAZetaSectorIsSelectedEigenspace :
  ∀ {G K : Set} {group} →
  (source : VOAAdapter.ActualMonster3BVOAPhaseActionSource G K group) →
  VOAAdapter.literalVOAZetaSector source
  ≡ Inertia.CentralEigenspace
      (Inertia.phaseAction (VOAAdapter.normalizerActionFromVOA source))
      Inertia.phaseZeta
literalVOAZetaSectorIsSelectedEigenspace source = refl

------------------------------------------------------------------------
-- 4. Existing downstream frontiers.  These are retained, not promoted.
------------------------------------------------------------------------

linearZetaFrontier : LinearZeta.LinearZetaSectorFrontier
linearZetaFrontier = LinearZeta.currentLinearZetaSectorFrontier

homFrontier : Hom.LinearMultiplicityHomFrontier
homFrontier = Hom.currentLinearMultiplicityHomFrontier

zeta54Boundary : Zeta54.ZetaHeisenbergFiftyFourBoundary
zeta54Boundary = Zeta54.canonicalZetaHeisenbergFiftyFourBoundary

nextZetaResidual : String
nextZetaResidual =
  "instantiate the existing literal VOA zeta eigenspace as the actual linear W_zeta on the same selected 3B action; then identify the finite Stone-von-Neumann H_zeta model with the corresponding actual Heisenberg constituent and construct S_zeta = Hom_E(H_zeta,W_zeta). The current Base369 54-site zeta-sheet chart and shared zeta notation do not discharge either same-object recognition."

------------------------------------------------------------------------
-- 5. WrongType firewalls.
------------------------------------------------------------------------

data SameZetaGlyphCreatesSameObject : Set where
data Zeta54SheetCreatesCyclotomicScalar : Set where
data CyclotomicPolynomialCreatesActualWZeta : Set where
data FiniteHeisenbergModelCreatesActualHZetaRecognition : Set where
data LiteralZetaSectorCreatesLinearHomIntertwiner : Set where

sameZetaGlyphDoesNotCreateSameObject : SameZetaGlyphCreatesSameObject → ⊥
sameZetaGlyphDoesNotCreateSameObject ()

zeta54SheetDoesNotCreateCyclotomicScalar : Zeta54SheetCreatesCyclotomicScalar → ⊥
zeta54SheetDoesNotCreateCyclotomicScalar ()

cyclotomicPolynomialDoesNotCreateActualWZeta :
  CyclotomicPolynomialCreatesActualWZeta → ⊥
cyclotomicPolynomialDoesNotCreateActualWZeta ()

finiteHeisenbergModelDoesNotCreateActualRecognition :
  FiniteHeisenbergModelCreatesActualHZetaRecognition → ⊥
finiteHeisenbergModelDoesNotCreateActualRecognition ()

literalSectorDoesNotCreateLinearHomIntertwiner :
  LiteralZetaSectorCreatesLinearHomIntertwiner → ⊥
literalSectorDoesNotCreateLinearHomIntertwiner ()

------------------------------------------------------------------------
-- 6. Frontier summary.
------------------------------------------------------------------------

record Monster369ZetaWeldBoundary : Set where
  constructor monster-369-zeta-weld-boundary
  field
    fourierZetaMapsToMonsterZeta : Bool
    inertiaZetaMapsToExactCyclotomicZeta : Bool
    literalVOAZetaSectorUsesThatPhase : Bool
    linearRestrictionReusesLiteralZetaSector : Bool
    base369ZetaSheetIsLiteralCyclotomicScalar : Bool
    actualLinearWZetaPaid : Bool
    actualHZetaWZetaSameObjectRecognitionPaid : Bool
    actualMultiplicityIntertwinerPaid : Bool
    nextResidual : String
open Monster369ZetaWeldBoundary public

canonicalMonster369ZetaWeldBoundary : Monster369ZetaWeldBoundary
canonicalMonster369ZetaWeldBoundary =
  monster-369-zeta-weld-boundary
    true true true true
    false false false false
    nextZetaResidual
