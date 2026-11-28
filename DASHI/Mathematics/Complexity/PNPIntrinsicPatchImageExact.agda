module DASHI.Mathematics.Complexity.PNPIntrinsicPatchImageExact where

-- Existing finite-linear image carrier and the actual systematic
-- ternary Golay encoder. No new ternary field or quotient carrier.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Foundations.FiniteLinear.F3Subspace as L
import DASHI.Foundations.TernaryGolay.CodeBoundary as C
import DASHI.Foundations.TernaryGolay.ExplicitCode729 as Golay

module Systematic {K Y : Set} (embed : K → Y) (key : Y → K)
  (leftInverse : ∀ k → key (embed k) ≡ k) where

  Member : Y → Set
  Member y = Σ K (λ k → embed k ≡ y)

  inImage : ∀ {y} → Member y → embed (key y) ≡ y
  inImage (k , refl) = cong embed (leftInverse k)

  fromCheck : ∀ {y} → embed (key y) ≡ y → Member y
  fromCheck {y} eq = key y , eq

  keyExact : ∀ {y z} → Member y → Member z → key y ≡ key z → y ≡ z
  keyExact hy hz eq = trans (sym (inImage hy))
    (trans (cong embed eq) (inImage hz))

  -- A compressed lookup is sound only if the REQUIRED ambient target
  -- passes the image membership check. Equal pivot coordinates alone
  -- do not permit arbitrary targets outside the image.
  targetMatch : ∀ k y → key y ≡ k → embed (key y) ≡ y → embed k ≡ y
  targetMatch k y eq check = trans (cong embed (sym eq)) check

  module Fibre {A : Set} (observe : A → Y) (membership : ∀ x → Member (observe x))
    (k : K) where

    Ambient : Set
    Ambient = Σ A (λ x → observe x ≡ embed k)

    Intrinsic : Set
    Intrinsic = Σ A (λ x → key (observe x) ≡ k)

    compress : Ambient → Intrinsic
    compress (x , eq) = x , trans (cong key eq) (leftInverse k)

    reopen : Intrinsic → Ambient
    reopen (x , eq) = x , trans (sym (inImage (membership x))) (cong embed eq)

    original : Ambient → A
    original (x , _) = x

    originalKey : Intrinsic → A
    originalKey (x , _) = x

    originalRoundtrip : ∀ a → original (reopen (compress a)) ≡ original a
    originalRoundtrip (x , _) = refl

    intrinsicRoundtrip : ∀ a → originalKey (compress (reopen a)) ≡ originalKey a
    intrinsicRoundtrip (x , _) = refl

module LinearImage {domain codomain : L.F3Space}
  (embedding : L.F3LinearMap domain codomain)
  (key : L.Carrier codomain → L.Carrier domain)
  (leftInverse : ∀ k → key (L.apply embedding k) ≡ k) where

  module B = Systematic (L.apply embedding) key leftInverse

  memberTransport : ∀ {y} → L.Member (L.imageSubspace embedding) y → B.Member y
  memberTransport (L.imageMember k eq) = k , eq

  memberBack : ∀ {y} → B.Member y → L.Member (L.imageSubspace embedding) y
  memberBack (k , eq) = L.imageMember k eq

-- Actual repository [12,6,6]_3 donor has six systematic coordinates
-- and 729 exact messages. Reuse, rather than asserting generic rank-six
-- compression for every affine source.
module GolayImage = Systematic Golay.encode Golay.decodeSystematic Golay.decodeEncode

golayKeyCount : Golay.listCount Golay.allMessages ≡ 729
golayKeyCount = Golay.allMessagesCountIs729
