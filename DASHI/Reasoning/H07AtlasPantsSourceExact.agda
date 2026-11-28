module DASHI.Reasoning.H07AtlasPantsSourceExact where

-- Reuse the original heterogeneous seam constructor recovered from master.
-- This is a finite affine channel interpretation, not a physical wave.
open import DASHI.Core.Prelude
open import Agda.Builtin.String using (primStringAppend)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Codec.TriadicMaskSignFactorization as M
import DASHI.Reasoning.H07FullAtlasSectionExact as H
import DASHI.Reasoning.H07AtlasProjectionLawsExact as P
import DASHI.Reasoning.H07AffinePairedSeamExact as S
import DASHI.Reasoning.TypedHyperfabricCore as F
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Reasoning.TypedHyperfabricPantsNonvacuousSeamQuotientExact as G
import DASHI.Reasoning.TypedHyperfabricPantsSourceHeterogeneousTransportExact as Original

pivotLabel : H.Pivot → String
pivotLabel H.p01 = "01"
pivotLabel H.p02 = "02"
pivotLabel H.p03 = "03"
pivotLabel H.p04 = "04"
pivotLabel H.p12 = "12"
pivotLabel H.p13 = "13"
pivotLabel H.p14 = "14"
pivotLabel H.p23 = "23"
pivotLabel H.p24 = "24"
pivotLabel H.p34 = "34"

complement : H.Pivot → H.Vec5 → M.Triple Trit
complement H.p01 (H.vec5 a0 a1 a2 a3 a4) = M.triple a2 a3 a4
complement H.p02 (H.vec5 a0 a1 a2 a3 a4) = M.triple a1 a3 a4
complement H.p03 (H.vec5 a0 a1 a2 a3 a4) = M.triple a1 a2 a4
complement H.p04 (H.vec5 a0 a1 a2 a3 a4) = M.triple a1 a2 a3
complement H.p12 (H.vec5 a0 a1 a2 a3 a4) = M.triple a0 a3 a4
complement H.p13 (H.vec5 a0 a1 a2 a3 a4) = M.triple a0 a2 a4
complement H.p14 (H.vec5 a0 a1 a2 a3 a4) = M.triple a0 a2 a3
complement H.p23 (H.vec5 a0 a1 a2 a3 a4) = M.triple a0 a1 a4
complement H.p24 (H.vec5 a0 a1 a2 a3 a4) = M.triple a0 a1 a3
complement H.p34 (H.vec5 a0 a1 a2 a3 a4) = M.triple a0 a1 a2

digitLabel : Trit → String
digitLabel neg = "-"
digitLabel zer = "0"
digitLabel pos = "+"

vecLabel : H.Vec5 → String
vecLabel (H.vec5 a b c d e) =
  primStringAppend (digitLabel a)
    (primStringAppend (digitLabel b)
      (primStringAppend (digitLabel c)
        (primStringAppend (digitLabel d) (digitLabel e))))

directionLabel : H.Direction → String
directionLabel (H.direction u v) =
  primStringAppend "H07 chosen direction basis "
    (primStringAppend (vecLabel u) (primStringAppend ":" (vecLabel v)))

-- Proposition identity is direction-dependent and uses one common target
-- chart. The chosen basis label is not claimed basis-independent.
channel : {L : H.Direction} {p q : H.Mark L} →
  String → H.Shared p q → Pants.BranchChannel
channel {L} {p} {q} label (H.shared x n k) =
  Pants.branchChannel
    (Pants.boundaryInterface label
      (directionLabel L) (pivotLabel (H.Mark.pivot q)) 9
      (S.Context.phase4 k) true (label ∷ S.Context.history k))
    (S.offsetWave (complement (H.Mark.pivot q) x))
    "common normalized affine quotient"
    "finite signed radix observer; source correction remains in local stalk"

module At {L : H.Direction} (p v w q : H.Mark L)
  (x : H.Vec5) (n : Trit) (k : S.Context) where

  sourceSection : F.GlobalSection (H.fabric p)
  sourceSection = P.atlasSection p x n k

  left : H.Local p v
  left = F.vertexValue sourceSection v

  right : H.Local p w
  right = F.vertexValue sourceSection w

  leftInterpret : H.Local p v → Pants.BranchChannel
  leftInterpret a = channel (pivotLabel (H.Mark.pivot v))
    (H.restrict {q = q} H.sameDirection a)

  rightInterpret : H.Local p w → Pants.BranchChannel
  rightInterpret a = channel (pivotLabel (H.Mark.pivot w))
    (H.restrict {q = q} H.sameDirection a)

  leftAgrees : H.restrict {q = q} H.sameDirection left ≡ F.edgeValue sourceSection q
  leftAgrees = F.compatible sourceSection {vertex = v} {edge = q} H.sameDirection

  rightAgrees : H.restrict {q = q} H.sameDirection right ≡ F.edgeValue sourceSection q
  rightAgrees = F.compatible sourceSection {vertex = w} {edge = q} H.sameDirection

  signature : H.Shared p q → G.SeamSignature
  signature z = G.boundarySignature (channel "common" z)

  signatureAgreement : G.boundarySignature (leftInterpret left)
    ≡ G.boundarySignature (rightInterpret right)
  signatureAgreement = trans (cong signature leftAgrees)
    (sym (cong signature rightAgrees))

  module Merged = Original.HeterogeneousMatchedSource
    (H.Local p v) (H.Local p w) left right leftInterpret rightInterpret
    signatureAgreement
    (pivotLabel (H.Mark.pivot v) ∷ S.Context.history k)
    (pivotLabel (H.Mark.pivot w) ∷ S.Context.history k)

-- Merged.admittedOriginalPantsSeam, beforeSection, afterSection,
-- restrictionPreserved and entireSourceProvenanceRetained are the original
-- constructors. Both local offsets and corrections remain in vertex
-- stalks. No new topology or full BranchChannel equality is asserted.
