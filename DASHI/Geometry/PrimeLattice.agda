module DASHI.Geometry.PrimeLattice where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (sym)

open import MonsterOntos using (SSP)
import Ontology.GodelLattice as GL
import Ontology.Hecke.FactorVecInstances as FVI

------------------------------------------------------------------------
-- Standalone prime-lattice geometry.
--
-- This module deliberately does not depend on DASHIState or SFGC.  The
-- diagnostics showed those are process surfaces, while G2 needs geometry on
-- the prime-address lattice itself: FactorVec with prime-indexed bumps.

Prime : Set
Prime = SSP

FactorVec : Set
FactorVec = GL.FactorVec

primeBump : Prime → FactorVec → FactorVec
primeBump = FVI.primeBump

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Cells.

record PrimeLatticeEdge : Set where
  field
    source :
      FactorVec

    edgePrime :
      Prime

    target :
      FactorVec

    targetDef :
      target ≡ primeBump edgePrime source

record PrimeLattice2Cell : Set where
  field
    base :
      FactorVec

    prime1 :
      Prime

    prime2 :
      Prime

    p1≠p2 :
      prime1 ≠ prime2

edgeAt :
  FactorVec →
  Prime →
  PrimeLatticeEdge
edgeAt source edgePrime =
  record
    { source =
        source
    ; edgePrime =
        edgePrime
    ; target =
        primeBump edgePrime source
    ; targetDef =
        refl
    }

southWest :
  PrimeLattice2Cell →
  FactorVec
southWest cell =
  PrimeLattice2Cell.base cell

southEast :
  PrimeLattice2Cell →
  FactorVec
southEast cell =
  primeBump
    (PrimeLattice2Cell.prime1 cell)
    (PrimeLattice2Cell.base cell)

northWest :
  PrimeLattice2Cell →
  FactorVec
northWest cell =
  primeBump
    (PrimeLattice2Cell.prime2 cell)
    (PrimeLattice2Cell.base cell)

northEast :
  PrimeLattice2Cell →
  FactorVec
northEast cell =
  primeBump
    (PrimeLattice2Cell.prime2 cell)
    (southEast cell)

northEast-from-commuted-path :
  (cell : PrimeLattice2Cell) →
  northEast cell
    ≡
  primeBump
    (PrimeLattice2Cell.prime1 cell)
    (northWest cell)
northEast-from-commuted-path cell =
  sym
    (FVI.primeBumpCommutes
      (PrimeLattice2Cell.prime1 cell)
      (PrimeLattice2Cell.prime2 cell)
      (PrimeLattice2Cell.base cell))

bottomEdge :
  PrimeLattice2Cell →
  PrimeLatticeEdge
bottomEdge cell =
  edgeAt
    (southWest cell)
    (PrimeLattice2Cell.prime1 cell)

rightEdge :
  PrimeLattice2Cell →
  PrimeLatticeEdge
rightEdge cell =
  edgeAt
    (southEast cell)
    (PrimeLattice2Cell.prime2 cell)

topEdge :
  PrimeLattice2Cell →
  PrimeLatticeEdge
topEdge cell =
  record
    { source =
        northWest cell
    ; edgePrime =
        PrimeLattice2Cell.prime1 cell
    ; target =
        northEast cell
    ; targetDef =
        northEast-from-commuted-path cell
    }

leftEdge :
  PrimeLattice2Cell →
  PrimeLatticeEdge
leftEdge cell =
  edgeAt
    (southWest cell)
    (PrimeLattice2Cell.prime2 cell)

northEast-square-commutes :
  (cell : PrimeLattice2Cell) →
  PrimeLatticeEdge.target (rightEdge cell)
    ≡
  PrimeLatticeEdge.target (topEdge cell)
northEast-square-commutes cell =
  refl

------------------------------------------------------------------------
-- Cochains.  The coefficient algebra is intentionally explicit: this file
-- supplies geometry and boundary shape, not a hidden numeric ring solver.

record PrimeLatticeCoefficientLaw (Coeff : Set) : Set₁ where
  field
    zero :
      Coeff

    _+_ :
      Coeff →
      Coeff →
      Coeff

    _-_ :
      Coeff →
      Coeff →
      Coeff

    d2SquareCancellation :
      (sw se nw ne : Coeff) →
      _-_
        (_+_ (_-_ se sw) (_-_ ne se))
        (_+_ (_-_ ne nw) (_-_ nw sw))
        ≡
      zero

0Form :
  Set →
  Set
0Form Coeff =
  FactorVec → Coeff

1Form :
  Set →
  Set
1Form Coeff =
  PrimeLatticeEdge → Coeff

δ₀ :
  {Coeff : Set} →
  PrimeLatticeCoefficientLaw Coeff →
  0Form Coeff →
  1Form Coeff
δ₀ law f edge =
  PrimeLatticeCoefficientLaw._-_ law
    (f (PrimeLatticeEdge.target edge))
    (f (PrimeLatticeEdge.source edge))

δ₁ :
  {Coeff : Set} →
  PrimeLatticeCoefficientLaw Coeff →
  1Form Coeff →
  PrimeLattice2Cell →
  Coeff
δ₁ law a cell =
  PrimeLatticeCoefficientLaw._-_ law
    (PrimeLatticeCoefficientLaw._+_ law
      (a (bottomEdge cell))
      (a (rightEdge cell)))
    (PrimeLatticeCoefficientLaw._+_ law
      (a (topEdge cell))
      (a (leftEdge cell)))

δ₁∘δ₀-zero :
  {Coeff : Set} →
  (law : PrimeLatticeCoefficientLaw Coeff) →
  (f : 0Form Coeff) →
  (cell : PrimeLattice2Cell) →
  δ₁ law (δ₀ law f) cell
    ≡
  PrimeLatticeCoefficientLaw.zero law
δ₁∘δ₀-zero law f cell =
  PrimeLatticeCoefficientLaw.d2SquareCancellation law
    (f (southWest cell))
    (f (southEast cell))
    (f (northWest cell))
    (f (northEast cell))

------------------------------------------------------------------------
-- Non-promoting G2 prerequisite receipt.

data PrimeLatticeGeometryStatus : Set where
  standalonePrimeLatticeGeometryOnly :
    PrimeLatticeGeometryStatus

data PrimeLatticeG2Boundary : Set where
  noDiscreteCurvatureCarrierInhabitedHere :
    PrimeLatticeG2Boundary

record PrimeLatticeD2Surface : Set₁ where
  field
    status :
      PrimeLatticeGeometryStatus

    edgeSurface :
      Set

    twoCellSurface :
      Set

    primeBumpSquareCommutes :
      (cell : PrimeLattice2Cell) →
      PrimeLatticeEdge.target (rightEdge cell)
        ≡
      PrimeLatticeEdge.target (topEdge cell)

    coefficientLawNeededForNumericD2 :
      String

    d2ForAnySuppliedCoefficientLaw :
      {Coeff : Set} →
      (law : PrimeLatticeCoefficientLaw Coeff) →
      (f : 0Form Coeff) →
      (cell : PrimeLattice2Cell) →
      δ₁ law (δ₀ law f) cell
        ≡
      PrimeLatticeCoefficientLaw.zero law

    nonPromotionBoundary :
      PrimeLatticeG2Boundary

    notes :
      List String

canonicalPrimeLatticeD2Surface :
  PrimeLatticeD2Surface
canonicalPrimeLatticeD2Surface =
  record
    { status =
        standalonePrimeLatticeGeometryOnly
    ; edgeSurface =
        PrimeLatticeEdge
    ; twoCellSurface =
        PrimeLattice2Cell
    ; primeBumpSquareCommutes =
        northEast-square-commutes
    ; coefficientLawNeededForNumericD2 =
        "d2SquareCancellation : ((se - sw) + (ne - se)) - ((ne - nw) + (nw - sw)) == zero"
    ; d2ForAnySuppliedCoefficientLaw =
        δ₁∘δ₀-zero
    ; nonPromotionBoundary =
        noDiscreteCurvatureCarrierInhabitedHere
    ; notes =
        "This is the standalone prime-lattice geometry over Ontology.GodelLattice.FactorVec"
        ∷ "It is independent of DASHIState and SFGC ShiftPressurePoint"
        ∷ "The northeast vertex is shared by the two prime-bump paths using FVI.primeBumpCommutes"
        ∷ "Numeric d2 is coefficient-parametric; callers must supply the square-boundary cancellation law for their scalar"
        ∷ "No G2 Maxwell promotion or DiscreteCurvatureCarrier inhabitant is claimed here"
        ∷ []
    }
