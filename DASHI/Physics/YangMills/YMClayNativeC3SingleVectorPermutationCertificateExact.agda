module DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact where

------------------------------------------------------------------------
-- R443 finite permutation HIGH-ALPHA certificate reduction.
--
-- The OLD physical C3 Haar codec required an arbitrary matrix-Link vector
-- equality at all 1024 coordinates for EVERY possible Link vector.
-- This module proves that it is enough to establish the equality ONCE,
-- on the canonical vector of all 1024 original positive-bond LABELS.
--
-- The proof is parametric in the link carrier (so it applies to real SU(N)
-- matrices without inspecting their values): both permuteLinks and the
-- native C3 reindex commute with arbitrary Vec.map, and every value vector
-- reconstructs by mapping its original decoder over all original labels.
--
-- A witness consists of a LinkPermutation program and precisely ONE
-- finite label-Vec equality. The term/program itself is still OPEN;
-- there is no hidden assertion that any bijection is already encoded.
--
-- Uses the prior original-bond codec and native C3 owner, not a new field.
-- The Product.LinkPermutation module imports legacy RealAnalysisAxioms,
-- hence this file does not claim a transitive postulate-free --safe chain.
-- No genuine continuous SU(N) Haar measure or physical spectral gap follows.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Agda.Builtin.List as List
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClayNativePositiveBondEnumerationVectorExact as Codec
import DASHI.Physics.YangMills.YMClayNativeSideFourC3VectorWeldExact as C3
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product

Bond : Set
Bond = Torus.PositiveBond Torus.four

Count : Nat
Count = Codec.originalPositiveBondCount Torus.four

labels : List.List Bond
labels = Torus.elements (Codec.originalPositiveBondFinite Torus.four)

canonicalLabelVector : Vec.Vec Bond Count
canonicalLabelVector =
  Codec.encodeOriginalBonds Torus.four (λ bond → bond)

mapListValues :
  ∀ {A B C : Set}
    (xs : List.List A) (f : B → C) (g : A → B) →
  Vec.map f (Codec.listValues xs g)
  ≡ Codec.listValues xs (λ value → f (g value))
mapListValues List.[] f g = refl
mapListValues (List._∷_ head tail) f g =
  cong (Vec._∷_ (f (g head))) (mapListValues tail f g)

canonicalLabelVectorDecode :
  ∀ bond →
  Codec.decodeOriginalBonds Torus.four canonicalLabelVector bond ≡ bond
canonicalLabelVectorDecode bond =
  Codec.originalBondsDecodeEncodeAt Torus.four (λ b → b) bond

-- Every vector can be reconstructed from the ORIGINAL distinct labels.
reconstructFromCanonicalLabels :
  ∀ {Value : Set} (values : Vec.Vec Value Count) →
  Vec.map (Codec.decodeOriginalBonds Torus.four values)
    canonicalLabelVector
  ≡ values
reconstructFromCanonicalLabels values =
  trans
    (mapListValues labels
      (Codec.decodeOriginalBonds Torus.four values) (λ bond → bond))
    (Codec.originalBondsEncodeDecodeExactly Torus.four values)

-- Adjacent-swap permutation programs are natural under an arbitrary map.
-- This uses exactly the pre-existing Product constructors and Vec.map.
permuteLinksMap :
  ∀ {A B : Set} {n : Nat}
    (f : A → B) (program : Product.LinkPermutation n)
    (values : Vec.Vec A n) →
  Vec.map f (Product.permuteLinks program values)
  ≡ Product.permuteLinks program (Vec.map f values)
permuteLinksMap f Product.identity values = refl
permuteLinksMap f (Product.compose first second) values =
  trans
    (permuteLinksMap f first
      (Product.permuteLinks second values))
    (cong (Product.permuteLinks first)
      (permuteLinksMap f second values))
permuteLinksMap f (Product.fixHead program)
    (head Vec.∷ tail) =
  cong (Vec._∷_ (f head)) (permuteLinksMap f program tail)
permuteLinksMap f Product.swapHead
    (first Vec.∷ second Vec.∷ rest) = refl

-- On the canonical label vector, source C3 is just a finite vector of
-- the true selected native spatial rotation of the original bond labels.
canonicalC3IsEncodedBondMap :
  C3.forwardVector canonicalLabelVector
  ≡ Codec.encodeOriginalBonds Torus.four C3.forwardBond
canonicalC3IsEncodedBondMap =
  Codec.originalBondsEncodePointwise Torus.four
    (λ bond →
      Codec.decodeOriginalBonds Torus.four
        canonicalLabelVector (C3.forwardBond bond))
    C3.forwardBond
    (λ bond → canonicalLabelVectorDecode (C3.forwardBond bond))

nativeC3VectorMap :
  ∀ {Value : Set} (values : Vec.Vec Value Count) →
  Vec.map (Codec.decodeOriginalBonds Torus.four values)
    (C3.forwardVector canonicalLabelVector)
  ≡ C3.forwardVector values
nativeC3VectorMap values =
  trans
    (cong (Vec.map (Codec.decodeOriginalBonds Torus.four values))
      canonicalC3IsEncodedBondMap)
    (mapListValues labels
      (Codec.decodeOriginalBonds Torus.four values) C3.forwardBond)

record SingleVectorC3PermutationCertificate : Set where
  field
    program : Product.LinkPermutation Count

    -- Precisely one closed finite-label test, not an all-Link assumption.
    onCanonicalLabels :
      Product.permuteLinks program canonicalLabelVector
      ≡ C3.forwardVector canonicalLabelVector

open SingleVectorC3PermutationCertificate public

-- The former universal witness is DERIVED from the single label test.
-- Nothing about SU(N), complex matrices, Haar or a chosen physical measure
-- is required to construct this implication.
singleVectorC3ImpliesAllVectors :
  (certificate : SingleVectorC3PermutationCertificate) →
  ∀ {Value : Set} (values : Vec.Vec Value Count) →
  Product.permuteLinks (program certificate) values
  ≡ C3.forwardVector values
singleVectorC3ImpliesAllVectors certificate {Value = Value} values =
  let
    read : Bond → Value
    read = Codec.decodeOriginalBonds Torus.four values
  in
  trans
    (cong (Product.permuteLinks (program certificate))
      (sym (reconstructFromCanonicalLabels values)))
    (trans
      (sym (permuteLinksMap read
        (program certificate) canonicalLabelVector))
      (trans
        (cong (Vec.map read)
          (onCanonicalLabels certificate))
        (nativeC3VectorMap values)))
