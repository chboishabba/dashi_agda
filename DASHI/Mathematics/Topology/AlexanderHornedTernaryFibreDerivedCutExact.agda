module DASHI.Mathematics.Topology.AlexanderHornedTernaryFibreDerivedCutExact where

------------------------------------------------------------------------
-- GROUP-THEORETIC MAX-CUT FOR LOCAL FIBRE SYMMETRIES
--
-- Local group: H_n = Map(C3 x Trit^n,C3) ⋊ C3_sector.
-- Group law and faithful action live in the prior source owner.
-- The normal translation subgroup Map(X_n,C3) is ABELIAN. Its
-- sector quotient C3 is also ABELIAN; H_n is thus METABELIAN.
-- For 3^n independent sector orbits, the classical augmentation
-- calculation gives:
--
-- |H_n| = 3^(3*3^n +1)
-- |[H_n,H_n]| = 3^(2*3^n)
-- |H_n^ab| = 3^(3^n +1).
--
-- Derivation: each triple (g0,g1,g2) has invariant sum. The
-- differences (rotate(g)-g) span its 2D sum-zero kernel. The
-- derived subgroup is abelian, so second derived is trivial.
--
-- This is STRUCTURALLY INCOMPATIBLE with a nontrivial PERFECT
-- Alexander-Hatcher or A5/2I source group. A homomorphism from
-- a perfect source group to H_n has trivial image (because image
-- must be perfect and solvable). The source is NOT the orbifold
-- group G_A*G_A*G_A ⋊ C3, even if both have external sector C3.
--
-- Exact source proofs below: concrete noncommutation, abelian
-- field kernel, commutative sector quotient. Full abstract
-- group-derived-subgroup cardinality uses the independent exact
-- finite Python regression, NOT a kernel-verified Agda quotient.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Data.Vec.Base using ([])
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryLocalFibreActionExact as F

-- Depth zero has exactly three sector addresses and 3^3 local gauges.
deltaAtFirstSector : F.Gauge 0
deltaAtFirstSector (C3.c0 , []) = C3.c1
deltaAtFirstSector (C3.c1 , []) = C3.c0
deltaAtFirstSector (C3.c2 , []) = C3.c0

deltaDistinguishesFirstSector :
  deltaAtFirstSector (C3.c0 , []) ≡ C3.c1
deltaDistinguishesFirstSector = refl

deltaVanishesAtSecondSector :
  deltaAtFirstSector (C3.c1 , []) ≡ C3.c0
deltaVanishesAtSecondSector = refl

rotateMovesDeltaToSecondSector :
  F.rotateField 0 C3.c1 deltaAtFirstSector (C3.c1 , [])
    ≡ C3.c1
rotateMovesDeltaToSecondSector = refl

sectorRotationIsNotTrivialOnGauges :
  F.rotateField 0 C3.c1 deltaAtFirstSector (C3.c1 , [])
    ≡ deltaAtFirstSector (C3.c1 , []) → ⊥
sectorRotationIsNotTrivialOnGauges ()

-- The local gauge subgroup is abelian (already proved pointwise).
localGaugeSubgroupIsAbelian :
  ∀ {n} (g h : F.Gauge n) (x : F.Level n) →
  F.addGauge g h x ≡ F.addGauge h g x
localGaugeSubgroupIsAbelian = F.pointwiseAddCommutative

-- The quotient by this normal gauge subgroup is the sector C3,
-- so its elements commute; the projection is a homomorphism.
sectorProjectionPreservesProduct :
  ∀ {n} (a b : F.FiniteFieldSymmetry n) →
  F.sectorRotation (F.combineSymmetry a b)
  ≡ C3._∙_ (F.sectorRotation a) (F.sectorRotation b)
sectorProjectionPreservesProduct a b = refl

sectorProjectionIsAbelian :
  ∀ {n} (a b : F.FiniteFieldSymmetry n) →
  C3._∙_ (F.sectorRotation a) (F.sectorRotation b)
  ≡ C3._∙_ (F.sectorRotation b) (F.sectorRotation a)
sectorProjectionIsAbelian a b =
  F.commutativeC3 (F.sectorRotation a) (F.sectorRotation b)

-- Concrete proof of NONcommutativity at stage zero:
-- local delta followed by sector rotation differs from the reverse.
localFirst : F.FiniteFieldSymmetry 0
localFirst = F.fieldSymmetry deltaAtFirstSector C3.c0

externalSecond : F.FiniteFieldSymmetry 0
externalSecond = F.fieldSymmetry (F.zeroGauge 0) C3.c1

firstThenSecond :
  F.localRotation (F.combineSymmetry localFirst externalSecond)
    (C3.c0 , []) ≡ C3.c1
firstThenSecond = refl

secondThenFirst :
  F.localRotation (F.combineSymmetry externalSecond localFirst)
    (C3.c0 , []) ≡ C3.c0
secondThenFirst = refl

noncommutingAtFirstSector :
  F.localRotation (F.combineSymmetry localFirst externalSecond)
    (C3.c0 , [])
  ≡ F.localRotation (F.combineSymmetry externalSecond localFirst)
    (C3.c0 , []) → ⊥
noncommutingAtFirstSector ()

-- The expected augmentation subgroup for a single 3-sector orbit:
-- (a,b,c) is in the derived subgroup exactly when a+b+c=0.
-- No source-level colimit or π1 identification follows from this
-- finite group computation. Hatcher requires a nontrivial perfect
-- GROUP at the actual wild exterior, not this metabelian field actor.
