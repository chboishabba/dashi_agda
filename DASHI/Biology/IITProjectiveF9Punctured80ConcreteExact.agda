module DASHI.Biology.IITProjectiveF9Punctured80ConcreteExact where

open import DASHI.Core.Prelude

import DASHI.Algebra.Trit as Trit
import DASHI.Codec.TriadicPAdicCodec as Codec
import DASHI.Analysis.RiemannQuarticTriadicCodecKernelBridgeExact as K4
import DASHI.Moonshine.OggSSPP2PuncturedKernel2BidiExact as P2
import DASHI.Moonshine.OggSSPP3F9FrobeniusCandidateNoGoExact as Ogg
import DASHI.Biology.IITProjectiveF9Pointed80Exact as Projective
import DASHI.Biology.IITF81F9ConcreteQuarticTowerExact as Tower
open Codec using ([]ᵥ; _∷ᵥ_)

------------------------------------------------------------------------
-- COMPLETE LITERAL 80-ELEMENT SOURCE PROJECTIVE TRIVIALISATION.
--
-- This fills the previously open record
-- Projective.Projective80Trivialisation with real source carriers:
--   K4.PuncturedKernel4
--   Projective.ProjectiveF9Chart
--   P2.PuncturedKernel2
--
-- The table is generated from the exact F81 / F9 tower basis already
-- registered on K4.Kernel4:
--   (c0,c1,c2,c3) ->
--   a=(c0,c1+c2-c3), b=(c1+c3,c3-c2).
-- If b=0, use infinity and scalar a != 0;
-- if b!=0, use affine slope a/b in F9 and nonzero scalar b.
-- The inverse maps infinity,scalar to (scalar,0), and
-- affine slope,scalar to (slope*scalar,scalar).
-- All 80 two-sided equalities are source-written CLOSED proof cases.
-- This is a CHOSEN projective chart, not modular j or Monster action.
-- No dependence on hypothetical cardinal identifications.
------------------------------------------------------------------------

toProjectiveSource :
  K4.PuncturedKernel4 →
  Projective.ProjectiveF9Chart × P2.PuncturedKernel2
toProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.infinity , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.infinity , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)
toProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.infinity , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.infinity , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.infinity , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)
toProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.infinity , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.infinity , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.infinity , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)
toProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) =
  Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)

fromProjectiveSource :
  Projective.ProjectiveF9Chart × P2.PuncturedKernel2 →
  K4.PuncturedKernel4
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) =
  ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) =
  ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) =
  ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) =
  ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) =
  ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) =
  ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) =
  ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) =
  ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) =
  ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) =
  ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) =
  ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) =
  ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) =
  ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) =
  ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) =
  ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) =
  ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.infinity , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) =
  ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) =
  ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) =
  ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) =
  ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) =
  ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.infinity , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) =
  ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) =
  ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) =
  ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) =
  ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) =
  ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.infinity , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) =
  ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) =
  ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) =
  ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) =
  ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) =
  ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) =
  ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) =
  ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) =
  ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) =
  ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) =
  ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) =
  ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) =
  ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) =
  ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) =
  ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) =
  ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) =
  ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) =
  ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.infinity , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) =
  ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) =
  ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) =
  ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) =
  ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) =
  ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.infinity , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) =
  ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) =
  ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) =
  ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) =
  ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) =
  ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.infinity , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) =
  ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) =
  ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) =
  ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) =
  ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) =
  ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) =
  ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) =
  ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) =
  ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) =
  ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) =
  ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) =
  ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) =
  ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) =
  ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) =
  ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) =
  ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) =
  ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) =
  ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.infinity , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) =
  ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) =
  ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) =
  ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) =
  ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) =
  ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.infinity , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) =
  ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) =
  ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) =
  ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) =
  ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl)
fromProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) =
  ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl)

decodeEncodeProjectiveSource :
  (p : Projective.ProjectiveF9Chart × P2.PuncturedKernel2) →
  toProjectiveSource (fromProjectiveSource p) ≡ p
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) = refl
decodeEncodeProjectiveSource (Projective.infinity , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) = refl
decodeEncodeProjectiveSource (Projective.infinity , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.z3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) = refl
decodeEncodeProjectiveSource (Projective.infinity , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) = refl
decodeEncodeProjectiveSource (Projective.infinity , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) = refl
decodeEncodeProjectiveSource (Projective.infinity , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) = refl
decodeEncodeProjectiveSource (Projective.infinity , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.z3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) = refl
decodeEncodeProjectiveSource (Projective.infinity , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.negZero)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.zeroPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.posNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.o3) , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) = refl
decodeEncodeProjectiveSource (Projective.infinity , ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.negNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.o3) , ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.posPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.o3 Ogg.z3) , ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , P2.negPos)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.z3 Ogg.t3) , ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , P2.zeroNeg)) = refl
decodeEncodeProjectiveSource (Projective.affine (Ogg.f9 Ogg.t3 Ogg.t3) , ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , P2.posZero)) = refl

encodeDecodeProjectiveSource :
  (p : K4.PuncturedKernel4) →
  fromProjectiveSource (toProjectiveSource p) ≡ p
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.zer ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.pos ∷ᵥ []ᵥ) , refl) = refl
encodeDecodeProjectiveSource ((Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ Trit.neg ∷ᵥ []ᵥ) , refl) = refl

-- The previously uninhabited actual source-field record is now
-- CONSTRUCTIVELY inhabited, provided the finite Agda checker accepts
-- the source-written 80×2 closed roundtrips.

concreteProjective80Trivialisation :
  Projective.Projective80Trivialisation
concreteProjective80Trivialisation =
  record
    { Projective.toProjectiveFibre = toProjectiveSource
    ; Projective.fromProjectiveFibre = fromProjectiveSource
    ; Projective.decodeEncode = decodeEncodeProjectiveSource
    ; Projective.encodeDecode = encodeDecodeProjectiveSource
    }

-- Projective infinity is only a CHOSEN chart. The literal source C5
-- and D4 actions are not automatically intertwined; constructing the
-- corresponding action transport is a distinct theorem obligation.

record ConcreteProjective80Boundary : Set where
  constructor concrete-projective80-boundary
  field
    literalSourceEightyAndEightReferenced : Bool
    full80ForwardAndBackwardMapsSourceWritten : Bool
    twoSidedSourceWeldInhabited : Bool
    selectedInfinityIsClassicalModularCusp : Bool
    AgdaExactHeadKernelReceiptPresent : Bool
    externalMonsterActionOrConsciousnessEstablished : Bool

canonicalConcreteProjective80Boundary : ConcreteProjective80Boundary
canonicalConcreteProjective80Boundary =
  concrete-projective80-boundary true true true false false false
