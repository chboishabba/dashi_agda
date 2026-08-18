module DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005. DOI: 10.1007/978-0-387-27226-9.
-- Oldforms / degeneracy maps and prime-to-level Hecke action.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
-- The three-point permutation module decomposes as 1 + std.
--
-- DASHI CONTRIBUTION
--
-- Upgrade P11MarkedLevel44PermutationOldspaceExact from a basis-level match to
-- an exact Z-linear module map.
--
-- The formal old-copy module has coordinates (x1,x2,x4) on the three classical
-- degeneracy labels d=1,2,4.  Its S3 deck action is the literal permutation
-- action on those coordinates.  Realize it in the source-native marked five
-- state carrier by
--
--   Phi(x1,x2,x4)
--     = (-3 s,-3 s,6 x1,6 x2,6 x4),  s=x1+x2+x4.
--
-- This sends the coordinate basis exactly to the three integral permutation
-- vectors constructed in P11MarkedLevel44PermutationOldspaceExact.
--
-- We prove for ARBITRARY integer coefficients:
--
--   Phi(r v) = deckR Phi(v),
--   Phi(s v) = deckS Phi(v),
--
-- and, for the source-native Hecke operators already constructed,
--
--   T3 Phi(v) = Phi((-1) v),
--   T5 Phi(v) = Phi((+1) v),
--   T7 Phi(v) = Phi((-2) v).
--
-- Hence this is an honest finite deck/Hecke intertwiner, not three independent
-- eigenvector receipts.
--
-- IMPORTANT BOUNDARY
-- The domain is the formal Z-module on degeneracy COPY LABELS.  This module is
-- not yet identified with the analytic oldforms f(z),f(2z),f(4z).  The global
-- same-object theorem is now exactly the map from those analytic degeneracy
-- forms to this formal copy module (or directly to the marked image), together
-- with the classical away-from-44 Hecke commuting square.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Tactic.RingSolver as ℤRing
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)

import DASHI.Moonshine.P11MarkedLevel44OldspaceWeldExact as Old
import DASHI.Moonshine.P11MarkedLevel44PermutationOldspaceExact as Perm
import DASHI.Moonshine.P11MarkedX2S3HeckeDecompositionExact as S3
import DASHI.Moonshine.P11MarkedX2T7HeckeCollisionExact as T7

------------------------------------------------------------------------
-- Free integer module on old-copy labels d=1,2,4.
------------------------------------------------------------------------

record Old3 : Set where
  constructor old3
  field
    x1 x2 x4 : ℤ
open Old3 public

addOld3 : Old3 → Old3 → Old3
addOld3 u v = old3
  (x1 u +ℤ x1 v)
  (x2 u +ℤ x2 v)
  (x4 u +ℤ x4 v)

scaleOld3 : ℤ → Old3 → Old3
scaleOld3 a v = old3
  (a *ℤ x1 v)
  (a *ℤ x2 v)
  (a *ℤ x4 v)

oldBasis1 oldBasis2 oldBasis4 : Old3
oldBasis1 = old3 (+ 1) (+ 0) (+ 0)
oldBasis2 = old3 (+ 0) (+ 1) (+ 0)
oldBasis4 = old3 (+ 0) (+ 0) (+ 1)

------------------------------------------------------------------------
-- S3 permutation action on the copy module.
------------------------------------------------------------------------

oldR : Old3 → Old3
oldR v = old3 (x4 v) (x1 v) (x2 v)

oldS : Old3 → Old3
oldS v = old3 (x1 v) (x4 v) (x2 v)

oldR3 : (v : Old3) → oldR (oldR (oldR v)) ≡ v
oldR3 (old3 a b c) = refl

oldS2 : (v : Old3) → oldS (oldS v) ≡ v
oldS2 (old3 a b c) = refl

oldSRS : (v : Old3) → oldS (oldR (oldS v)) ≡ oldR (oldR v)
oldSRS (old3 a b c) = refl

------------------------------------------------------------------------
-- Exact Z-linear realization in the marked five-state carrier.
------------------------------------------------------------------------

realizeOld3 : Old3 → S3.Int5
realizeOld3 v = S3.int5
  ((-[1+ 2 ]) *ℤ (x1 v +ℤ x2 v +ℤ x4 v))
  ((-[1+ 2 ]) *ℤ (x1 v +ℤ x2 v +ℤ x4 v))
  ((+ 6) *ℤ x1 v)
  ((+ 6) *ℤ x2 v)
  ((+ 6) *ℤ x4 v)

-- Extensionality for the existing five-coordinate record.  RingSolver proves
-- scalar coordinate identities; this lemma then reconstructs record equality.
int5Ext :
  (u v : S3.Int5) →
  S3.a0c u ≡ S3.a0c v →
  S3.a1c u ≡ S3.a1c v →
  S3.b0c u ≡ S3.b0c v →
  S3.b1c u ≡ S3.b1c v →
  S3.b2c u ≡ S3.b2c v →
  u ≡ v
int5Ext
  (S3.int5 a0 a1 b0 b1 b2)
  (S3.int5 a0' a1' b0' b1' b2')
  refl refl refl refl refl = refl

realizeBasis1 : realizeOld3 oldBasis1 ≡ Perm.oldCopyVector Old.copy1
realizeBasis1 = refl

realizeBasis2 : realizeOld3 oldBasis2 ≡ Perm.oldCopyVector Old.copy2
realizeBasis2 = refl

realizeBasis4 : realizeOld3 oldBasis4 ≡ Perm.oldCopyVector Old.copy4
realizeBasis4 = refl

realizeAdditive :
  (u v : Old3) →
  realizeOld3 (addOld3 u v) ≡ S3.add5 (realizeOld3 u) (realizeOld3 v)
realizeAdditive (old3 a b c) (old3 d e f) =
  int5Ext _ _
    (ℤRing.solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []))
    (ℤRing.solve (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ []))
    (ℤRing.solve (a ∷ d ∷ []))
    (ℤRing.solve (b ∷ e ∷ []))
    (ℤRing.solve (c ∷ f ∷ []))

realizeScalar :
  (k : ℤ) → (v : Old3) →
  realizeOld3 (scaleOld3 k v) ≡ S3.scale5 k (realizeOld3 v)
realizeScalar k (old3 a b c) =
  int5Ext _ _
    (ℤRing.solve (k ∷ a ∷ b ∷ c ∷ []))
    (ℤRing.solve (k ∷ a ∷ b ∷ c ∷ []))
    (ℤRing.solve (k ∷ a ∷ []))
    (ℤRing.solve (k ∷ b ∷ []))
    (ℤRing.solve (k ∷ c ∷ []))

------------------------------------------------------------------------
-- Deck intertwining on arbitrary vectors.
------------------------------------------------------------------------

realizeDeckR :
  (v : Old3) →
  realizeOld3 (oldR v) ≡ Perm.deckR5 (realizeOld3 v)
realizeDeckR (old3 a b c) =
  int5Ext _ _
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (c ∷ []))
    (ℤRing.solve (a ∷ []))
    (ℤRing.solve (b ∷ []))

realizeDeckS :
  (v : Old3) →
  realizeOld3 (oldS v) ≡ Perm.deckS5 (realizeOld3 v)
realizeDeckS (old3 a b c) =
  int5Ext _ _
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (a ∷ []))
    (ℤRing.solve (c ∷ []))
    (ℤRing.solve (b ∷ []))

------------------------------------------------------------------------
-- Source-native T3/T5/T7 Hecke intertwiners on the WHOLE old-copy module.
------------------------------------------------------------------------

realizeT3 :
  (v : Old3) →
  S3.markedT3Action (realizeOld3 v)
  ≡ realizeOld3 (scaleOld3 (-[1+ 0 ]) v)
realizeT3 (old3 a b c) =
  int5Ext _ _
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (a ∷ b ∷ c ∷ []))

realizeT5 :
  (v : Old3) →
  S3.markedT5Action (realizeOld3 v)
  ≡ realizeOld3 (scaleOld3 (+ 1) v)
realizeT5 (old3 a b c) =
  int5Ext _ _
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (a ∷ b ∷ c ∷ []))

realizeT7 :
  (v : Old3) →
  T7.markedT7Action (realizeOld3 v)
  ≡ realizeOld3 (scaleOld3 (-[1+ 1 ]) v)
realizeT7 (old3 a b c) =
  int5Ext _ _
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (a ∷ b ∷ c ∷ []))
    (ℤRing.solve (a ∷ b ∷ c ∷ []))

------------------------------------------------------------------------
-- The finite same-object seam is now an actual pair of commuting squares:
-- deck S3 and Hecke T3/T5/T7 are transported by one common realization map.
------------------------------------------------------------------------

record P11MarkedLevel44PermutationIntertwinerBoundary : Set where
  field
    freeThreeCopyModuleConstructed : Bool
    singleMarkedRealizationMapConstructed : Bool
    realizationAdditive : Bool
    realizationScalarCompatible : Bool
    deckRIntertwinerConstructed : Bool
    deckSIntertwinerConstructed : Bool
    t3IntertwinerConstructed : Bool
    t5IntertwinerConstructed : Bool
    t7IntertwinerConstructed : Bool
    analyticDegeneracyModuleIdentified : Bool

canonicalP11MarkedLevel44PermutationIntertwinerBoundary :
  P11MarkedLevel44PermutationIntertwinerBoundary
canonicalP11MarkedLevel44PermutationIntertwinerBoundary = record
  { freeThreeCopyModuleConstructed = true
  ; singleMarkedRealizationMapConstructed = true
  ; realizationAdditive = true
  ; realizationScalarCompatible = true
  ; deckRIntertwinerConstructed = true
  ; deckSIntertwinerConstructed = true
  ; t3IntertwinerConstructed = true
  ; t5IntertwinerConstructed = true
  ; t7IntertwinerConstructed = true
  ; analyticDegeneracyModuleIdentified = false
  }
