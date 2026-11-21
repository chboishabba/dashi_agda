module DASHI.Codec.IndexedCubePivot02RechartedExact where

-- H07: actual pivot02-COORDINATE arrow compiler for the same restricted
-- cube, not a post-hoc endpoint equality. The one source-specific
-- arithmetic obligation (involutive reparametrization) is explicit.
-- SymPy exhaustive acceptance is separate from Agda kernel acceptance.

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit; neg; pos; inv)
import DASHI.Codec.TriadicMaskSignFactorization as M
import DASHI.Codec.IndexedCubeMarkedAffine9Exact as A
import DASHI.Codec.IndexedCubeAffineStableOverlapExact as S
import DASHI.Codec.IndexedCubeGeometryChartExact as G
import DASHI.Core.GovernedIndexedResidualCubeExact as Q

-- Two nonzero signs multiply to another nonzero sign, without
-- embedding a spurious zero coefficient.
multiplySign : M.Sign → M.Sign → M.Sign
multiplySign M.negative M.negative = M.positive
multiplySign M.negative M.positive = M.negative
multiplySign M.positive M.negative = M.negative
multiplySign M.positive M.positive = M.positive

-- Pivot02 data as all nine genuine coefficients of the graph in the
-- AMBIENT coordinate order (0,2), restricted to the same 5832 states.
-- Reciprocals in F3 are the original nonzero signs themselves.
pivotRaw : S.StableBlocks Trit → S.StableBlocks Trit
pivotRaw (S.stableBlocks
    (M.triple a0 a1 a2)
    (M.triple s0 s1 s2)
    (M.triple b0 b1 b2)) =
  S.stableBlocks
    (M.triple aa
      (A.add3 a1 (A.mul3 (S.rawSlope s1) aa))
      (A.add3 a2 (A.mul3 (S.rawSlope s2) aa)))
    (M.triple s0 (multiplySign s1 s0) (multiplySign s2 s0))
    (M.triple bb
      (A.add3 b1 (A.mul3 (S.rawSlope s1) bb))
      (A.add3 b2 (A.mul3 (S.rawSlope s2) bb)))
  where
    aa : Trit
    aa = A.mul3 (inv a0) (S.rawSlope s0)

    bb : Trit
    bb = A.mul3 (inv b0) (S.rawSlope s0)

-- Original source's staged mask/sign codec is preserved; the pivot is
-- done on the raw coefficients and re-encoded at factorized vertices.
pivotFact : S.StableBlocks M.FactorizedTrit →
            S.StableBlocks M.FactorizedTrit
pivotFact x = S.encodeBlocks (pivotRaw (S.decodeBlocks x))

pivotSplit : ∀ {A : Set} →
  (S.StableBlocks A → S.StableBlocks A) →
  S.StableSplit A → S.StableSplit A
pivotSplit p x = S.toSplit (p (S.toBlocks x))

decodeEncodeStable : (x : S.StableBlocks Trit) →
  S.decodeBlocks (S.encodeBlocks x) ≡ x
decodeEncodeStable (S.stableBlocks a s b)
  rewrite M.decodeTriple-encodeTriple a
        | M.decodeTriple-encodeTriple b = refl

encodeDecodeStable : (x : S.StableBlocks M.FactorizedTrit) →
  S.encodeBlocks (S.decodeBlocks x) ≡ x
encodeDecodeStable (S.stableBlocks a s b)
  rewrite M.encodeTriple-decodeTriple a
        | M.encodeTriple-decodeTriple b = refl

-- The remaining Agda proof obligation is exactly the universal F3
-- pivot involution. It cannot be filled by a finite test result.
record SourcePivotInvolution : Set where
  field
    onRaw : (x : S.StableBlocks Trit) →
      pivotRaw (pivotRaw x) ≡ x
open SourcePivotInvolution public

pivotFactInvolution : (laws : SourcePivotInvolution) →
  (x : S.StableBlocks M.FactorizedTrit) →
  pivotFact (pivotFact x) ≡ x
pivotFactInvolution laws x
  rewrite decodeEncodeStable (pivotRaw (S.decodeBlocks x))
        | onRaw laws (S.decodeBlocks x)
        | encodeDecodeStable x = refl

rawChart : (laws : SourcePivotInvolution) →
  G.Chart (S.StableBlocks Trit)
rawChart laws = record
  { Coordinates = S.StableBlocks Trit
  ; encode = pivotRaw
  ; decode = pivotRaw
  ; decodeEncode = onRaw laws
  ; encodeDecode = onRaw laws
  }

factChart : (laws : SourcePivotInvolution) →
  G.Chart (S.StableBlocks M.FactorizedTrit)
factChart laws = record
  { Coordinates = S.StableBlocks M.FactorizedTrit
  ; encode = pivotFact
  ; decode = pivotFact
  ; decodeEncode = pivotFactInvolution laws
  ; encodeDecode = pivotFactInvolution laws
  }

splitRawChart : (laws : SourcePivotInvolution) →
  G.Chart (S.StableSplit Trit)
splitRawChart laws = record
  { Coordinates = S.StableSplit Trit
  ; encode = pivotSplit pivotRaw
  ; decode = pivotSplit pivotRaw
  ; decodeEncode = λ { (S.stableSplit a s b) →
      Q.cong S.toSplit (onRaw laws (S.stableBlocks a s b)) }
  ; encodeDecode = λ { (S.stableSplit a s b) →
      Q.cong S.toSplit (onRaw laws (S.stableBlocks a s b)) }
  }

splitFactChart : (laws : SourcePivotInvolution) →
  G.Chart (S.StableSplit M.FactorizedTrit)
splitFactChart laws = record
  { Coordinates = S.StableSplit M.FactorizedTrit
  ; encode = pivotSplit pivotFact
  ; decode = pivotSplit pivotFact
  ; decodeEncode = λ { (S.stableSplit a s b) →
      Q.cong S.toSplit
        (pivotFactInvolution laws (S.stableBlocks a s b)) }
  ; encodeDecode = λ { (S.stableSplit a s b) →
      Q.cong S.toSplit
        (pivotFactInvolution laws (S.stableBlocks a s b)) }
  }

pivot02Charts : (laws : SourcePivotInvolution) → G.Charts S.stableCube
pivot02Charts laws = record
  { a = rawChart laws ; b = splitRawChart laws
  ; c = rawChart laws ; d = splitRawChart laws
  ; e = factChart laws ; f = splitFactChart laws
  ; h = factChart laws ; i = splitFactChart laws
  }

-- All twelve arrows are G.lift of the ORIGINAL restricted cube arrows;
-- in particular the rotation edge is pivot02 ∘ rotate ∘ pivot02^-1.
pivot02Cube : (laws : SourcePivotInvolution) → Q.Cube
pivot02Cube laws = G.recharted S.stableCube (pivot02Charts laws)

pivot02Faces : (laws : SourcePivotInvolution) →
  Q.Faces (pivot02Cube laws)
pivot02Faces laws =
  G.rechartedFaces S.stableCube S.stableFaces (pivot02Charts laws)

pivot02Exact : (laws : SourcePivotInvolution) →
  Q.ExactFaces (pivot02Cube laws) (pivot02Faces laws)
pivot02Exact laws =
  G.rechartedExact S.stableCube S.stableFaces
    (pivot02Charts laws) S.stableExact

pivot02Terminal : (laws : SourcePivotInvolution) →
  (x : Q.A (pivot02Cube laws)) →
  Q.xyz (pivot02Cube laws) x ≡ Q.zyx (pivot02Cube laws) x
pivot02Terminal laws = Q.xyz-zyx (pivot02Exact laws)

-- The selected nonzero/pivot-source-involution is not imported
-- from unmerged branches or equated with analytic j/Monster objects.
