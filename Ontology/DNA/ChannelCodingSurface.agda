module Ontology.DNA.ChannelCodingSurface where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Vec using (Vec; []; _∷_; map)

open import Ontology.DNA.Supervoxel4Adic using
  (Base; A; C; G; T; complement; complement-involutive)
open import Ontology.DNA.ChemistryConcrete using
  (_&&_; not; baseEq; isStrong; allStrong4; allWeak4; rcPalindrome4; hairpin6; isGC; countGCWindow;
   noImmediateRepeat; noImmediateComplement; noComplementSpan2;
   noExtremeGC4; noRCPal4; noHairpin6; gcStress3)
open import Ontology.DNA.StreamingEncoderSurface using
  (StreamingEncoderSurface; streamingEncoderSurface)

------------------------------------------------------------------------
-- Channel shaping and error-correction integration surface.
-- This keeps the ideal admissible generator separate from the physical
-- synthesis/sequencing channel while making the integration boundary typed.

record InnerChannelCode : Set₁ where
  field
    wrap : ∀ {n} → Vec Base n → Σ Nat (λ m → Vec Base m)
    admissibilityFlag : ∀ {n} → Vec Base n → Bool

record OuterRecoveryCode : Set₁ where
  field
    packetize : ∀ {n} → Vec Base n → Σ Nat (λ k → Vec Nat k)
    recover : ∀ {k} → Vec Nat k → Σ Nat (λ n → Vec Base n)

record PhysicalChannelModel : Set₁ where
  field
    substitutionRisk : Nat
    indelRisk : Nat
    dropoutRisk : Nat

record IntegratedChannelSurface : Set₁ where
  field
    encoderSurface : StreamingEncoderSurface
    innerCode : InnerChannelCode
    outerCode : OuterRecoveryCode
    channel : PhysicalChannelModel
    emit : ∀ {n} → Vec Base n → Σ Nat (λ m → Vec Base m)
    recoveryBoundary : Nat

genericAdmissibilityFlag : ∀ {n} → Vec Base n → Bool
genericAdmissibilityFlag xs =
  ((noImmediateRepeat xs && noImmediateComplement xs) && noComplementSpan2 xs)
    && ((noExtremeGC4 xs && noRCPal4 xs) && (noHairpin6 xs && gcStress3 xs))

baseEq-complement-both :
  (x y : Base) →
  baseEq (complement x) (complement y) ≡ baseEq x y
baseEq-complement-both A A = refl
baseEq-complement-both A C = refl
baseEq-complement-both A G = refl
baseEq-complement-both A T = refl
baseEq-complement-both C A = refl
baseEq-complement-both C C = refl
baseEq-complement-both C G = refl
baseEq-complement-both C T = refl
baseEq-complement-both G A = refl
baseEq-complement-both G C = refl
baseEq-complement-both G G = refl
baseEq-complement-both G T = refl
baseEq-complement-both T A = refl
baseEq-complement-both T C = refl
baseEq-complement-both T G = refl
baseEq-complement-both T T = refl

baseEq-complement-right :
  (x y : Base) →
  baseEq x (complement y) ≡ baseEq (complement x) y
baseEq-complement-right A A = refl
baseEq-complement-right A C = refl
baseEq-complement-right A G = refl
baseEq-complement-right A T = refl
baseEq-complement-right C A = refl
baseEq-complement-right C C = refl
baseEq-complement-right C G = refl
baseEq-complement-right C T = refl
baseEq-complement-right G A = refl
baseEq-complement-right G C = refl
baseEq-complement-right G G = refl
baseEq-complement-right G T = refl
baseEq-complement-right T A = refl
baseEq-complement-right T C = refl
baseEq-complement-right T G = refl
baseEq-complement-right T T = refl

isStrong-complement :
  (b : Base) →
  isStrong (complement b) ≡ isStrong b
isStrong-complement A = refl
isStrong-complement C = refl
isStrong-complement G = refl
isStrong-complement T = refl

allStrong4-complement :
  (a b c d : Base) →
  allStrong4 (complement a) (complement b) (complement c) (complement d)
    ≡ allStrong4 a b c d
allStrong4-complement a b c d
  rewrite isStrong-complement a
        | isStrong-complement b
        | isStrong-complement c
        | isStrong-complement d = refl

allWeak4-complement :
  (a b c d : Base) →
  allWeak4 (complement a) (complement b) (complement c) (complement d)
    ≡ allWeak4 a b c d
allWeak4-complement a b c d
  rewrite isStrong-complement a
        | isStrong-complement b
        | isStrong-complement c
        | isStrong-complement d = refl

rcPalindrome4-complement :
  (a b c d : Base) →
  rcPalindrome4 (complement a) (complement b) (complement c) (complement d)
    ≡
  rcPalindrome4 a b c d
rcPalindrome4-complement a b c d
  rewrite complement-involutive a
        | complement-involutive b
        | baseEq-complement-right a d
        | baseEq-complement-right b c = refl

hairpin6-complement :
  (a b c d e f : Base) →
  hairpin6
    (complement a) (complement b) (complement c)
    (complement d) (complement e) (complement f)
    ≡
  hairpin6 a b c d e f
hairpin6-complement a b c d e f
  rewrite complement-involutive a
        | complement-involutive b
        | complement-involutive c
        | baseEq-complement-right a f
        | baseEq-complement-right b e
        | baseEq-complement-right c d = refl

isGC-complement :
  (b : Base) →
  isGC (complement b) ≡ isGC b
isGC-complement A = refl
isGC-complement C = refl
isGC-complement G = refl
isGC-complement T = refl

countGCWindow-complement :
  (a b c : Base) →
  countGCWindow (complement a) (complement b) (complement c)
    ≡ countGCWindow a b c
countGCWindow-complement a b c
  rewrite isGC-complement a
        | isGC-complement b
        | isGC-complement c = refl

noImmediateRepeat-map-complement :
  ∀ {n} (xs : Vec Base n) →
  noImmediateRepeat (map complement xs) ≡ noImmediateRepeat xs

noImmediateRepeatFrom-map-complement :
  ∀ {n} (x y : Base) (xs : Vec Base n) →
  noImmediateRepeat (map complement (x ∷ y ∷ xs))
    ≡
  noImmediateRepeat (x ∷ y ∷ xs)
noImmediateRepeatFrom-map-complement x y []
  rewrite baseEq-complement-both x y = refl
noImmediateRepeatFrom-map-complement x y (z ∷ xs)
  rewrite baseEq-complement-both x y
        | noImmediateRepeatFrom-map-complement y z xs = refl

noImmediateRepeat-map-complement [] = refl
noImmediateRepeat-map-complement (x ∷ []) = refl
noImmediateRepeat-map-complement (x ∷ y ∷ xs) =
  noImmediateRepeatFrom-map-complement x y xs

noImmediateComplement-map-complement :
  ∀ {n} (xs : Vec Base n) →
  noImmediateComplement (map complement xs) ≡ noImmediateComplement xs

noImmediateComplementFrom-map-complement :
  ∀ {n} (x y : Base) (xs : Vec Base n) →
  noImmediateComplement (map complement (x ∷ y ∷ xs))
    ≡
  noImmediateComplement (x ∷ y ∷ xs)
noImmediateComplementFrom-map-complement x y []
  rewrite complement-involutive x
        | baseEq-complement-right x y = refl
noImmediateComplementFrom-map-complement x y (z ∷ xs)
  rewrite complement-involutive x
        | baseEq-complement-right x y
        | noImmediateComplementFrom-map-complement y z xs = refl

noImmediateComplement-map-complement [] = refl
noImmediateComplement-map-complement (x ∷ []) = refl
noImmediateComplement-map-complement (x ∷ y ∷ xs) =
  noImmediateComplementFrom-map-complement x y xs

defaultInnerCode : InnerChannelCode
defaultInnerCode = record
  { wrap = λ {n} xs → n , xs
  ; admissibilityFlag = genericAdmissibilityFlag
  }

complementInnerCode : InnerChannelCode
complementInnerCode = record
  { wrap = λ {n} xs → n , map complement xs
  ; admissibilityFlag = noImmediateRepeat
  }

defaultOuterCode : OuterRecoveryCode
defaultOuterCode = record
  { packetize = λ _ → zero , []
  ; recover = λ _ → zero , []
  }

defaultChannel : PhysicalChannelModel
defaultChannel = record
  { substitutionRisk = 1
  ; indelRisk = 1
  ; dropoutRisk = 1
  }

integratedChannelSurface : IntegratedChannelSurface
integratedChannelSurface = record
  { encoderSurface = streamingEncoderSurface
  ; innerCode = defaultInnerCode
  ; outerCode = defaultOuterCode
  ; channel = defaultChannel
  ; emit = InnerChannelCode.wrap defaultInnerCode
  ; recoveryBoundary = 3
  }

defaultWrap-identity : ∀ {n} (xs : Vec Base n) → InnerChannelCode.wrap defaultInnerCode xs ≡ (n , xs)
defaultWrap-identity xs = refl

defaultWrap-admissibility-consistent :
  ∀ {n} (xs : Vec Base n) →
  InnerChannelCode.admissibilityFlag defaultInnerCode xs ≡ genericAdmissibilityFlag xs
defaultWrap-admissibility-consistent xs = refl

integratedEmit-wrap-coherent :
  ∀ {n} (xs : Vec Base n) →
  IntegratedChannelSurface.emit integratedChannelSurface xs
    ≡ InnerChannelCode.wrap (IntegratedChannelSurface.innerCode integratedChannelSurface) xs
integratedEmit-wrap-coherent xs = refl

integratedEmit-preserves-length-and-sequence :
  ∀ {n} (xs : Vec Base n) →
  IntegratedChannelSurface.emit integratedChannelSurface xs ≡ (n , xs)
integratedEmit-preserves-length-and-sequence xs = refl

integratedEmit-output-admissibility-preserved :
  ∀ {n} (xs : Vec Base n) →
  Σ Nat
    (λ m → Σ (Vec Base m)
      (λ ys → Σ
        (IntegratedChannelSurface.emit integratedChannelSurface xs ≡ (m , ys))
        (λ _ →
          InnerChannelCode.admissibilityFlag
            (IntegratedChannelSurface.innerCode integratedChannelSurface)
            ys
            ≡
          InnerChannelCode.admissibilityFlag
            (IntegratedChannelSurface.innerCode integratedChannelSurface)
            xs)))
integratedEmit-output-admissibility-preserved xs = _ , xs , refl , refl

integratedEmit-output-genericAdmissibility-coherent :
  ∀ {n} (xs : Vec Base n) →
  Σ Nat
    (λ m → Σ (Vec Base m)
      (λ ys → Σ
        (IntegratedChannelSurface.emit integratedChannelSurface xs ≡ (m , ys))
        (λ _ →
          InnerChannelCode.admissibilityFlag
            (IntegratedChannelSurface.innerCode integratedChannelSurface)
            ys
            ≡ genericAdmissibilityFlag xs)))
integratedEmit-output-genericAdmissibility-coherent xs = _ , xs , refl , refl

complementWrap-nonIdentity-surface :
  ∀ {n} (xs : Vec Base n) →
  InnerChannelCode.wrap complementInnerCode xs ≡ (n , map complement xs)
complementWrap-nonIdentity-surface xs = refl

complementWrap-output-admissibility-preserved :
  ∀ {n} (xs : Vec Base n) →
  InnerChannelCode.admissibilityFlag complementInnerCode
    (map complement xs)
    ≡
  InnerChannelCode.admissibilityFlag complementInnerCode xs
complementWrap-output-admissibility-preserved xs =
  noImmediateRepeat-map-complement xs

complementWrap-output-repeat-coherent :
  ∀ {n} (xs : Vec Base n) →
  InnerChannelCode.admissibilityFlag complementInnerCode
    (map complement xs)
    ≡
  noImmediateRepeat xs
complementWrap-output-repeat-coherent xs =
  noImmediateRepeat-map-complement xs
