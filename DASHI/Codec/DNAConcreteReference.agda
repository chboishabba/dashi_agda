module DASHI.Codec.DNAConcreteReference where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Core.Prelude using (_×_; _,_)
open import DASHI.Codec.DNAFirstFormalism using
  ( Base; A; C; G; T
  ; ConstraintMachine
  ; Trace; emptyTrace; emitTrace
  ; Generable
  )
open import DASHI.Codec.DNACarrierFibre using
  ( ChemicalPair; atPair; cgPair; chemicalPair )

data PairPhase : Set where
  atTurn : PairPhase
  cgTurn : PairPhase

nextPair : PairPhase → PairPhase
nextPair atTurn = cgTurn
nextPair cgTurn = atTurn

nextPair-involutive : ∀ s → nextPair (nextPair s) ≡ s
nextPair-involutive atTurn = refl
nextPair-involutive cgTurn = refl

data Legal : PairPhase → Base → Set where
  legalA : Legal atTurn A
  legalT : Legal atTurn T
  legalC : Legal cgTurn C
  legalG : Legal cgTurn G

legal? : PairPhase → Base → Bool
legal? atTurn A = true
legal? atTurn T = true
legal? atTurn C = false
legal? atTurn G = false
legal? cgTurn A = false
legal? cgTurn T = false
legal? cgTurn C = true
legal? cgTurn G = true

legal-sound : ∀ {s b} → Legal s b → legal? s b ≡ true
legal-sound legalA = refl
legal-sound legalT = refl
legal-sound legalC = refl
legal-sound legalG = refl

referenceMachine : ConstraintMachine
referenceMachine = record
  { State = PairPhase
  ; initial = atTurn
  ; admissible = Legal
  ; step = λ s b → nextPair s
  }

legalBases : PairPhase → Base × Base
legalBases atTurn = A , T
legalBases cgTurn = C , G

branchCount : PairPhase → Nat
branchCount _ = suc (suc zero)

unrank : PairPhase → Bool → Base
unrank atTurn false = A
unrank atTurn true = T
unrank cgTurn false = C
unrank cgTurn true = G

unrankLegal : ∀ s bit → Legal s (unrank s bit)
unrankLegal atTurn false = legalA
unrankLegal atTurn true = legalT
unrankLegal cgTurn false = legalC
unrankLegal cgTurn true = legalG

rank : ∀ {s b} → Legal s b → Bool
rank legalA = false
rank legalT = true
rank legalC = false
rank legalG = true

rank-unrank : ∀ s bit → rank (unrankLegal s bit) ≡ bit
rank-unrank atTurn false = refl
rank-unrank atTurn true = refl
rank-unrank cgTurn false = refl
rank-unrank cgTurn true = refl

unrank-rank : ∀ {s b} (p : Legal s b) → unrank s (rank p) ≡ b
unrank-rank legalA = refl
unrank-rank legalT = refl
unrank-rank legalC = refl
unrank-rank legalG = refl

pairFor : PairPhase → ChemicalPair
pairFor atTurn = atPair
pairFor cgTurn = cgPair

chemicalPair-unrank :
  ∀ s bit → chemicalPair (unrank s bit) ≡ pairFor s
chemicalPair-unrank atTurn false = refl
chemicalPair-unrank atTurn true = refl
chemicalPair-unrank cgTurn false = refl
chemicalPair-unrank cgTurn true = refl

bitOf : Base → Bool
bitOf A = false
bitOf T = true
bitOf C = false
bitOf G = true

encodeFrom : PairPhase → List Bool → List Base
encodeFrom s [] = []
encodeFrom s (bit ∷ bits) =
  unrank s bit ∷ encodeFrom (nextPair s) bits

decodeFrom : PairPhase → List Base → List Bool
decodeFrom s [] = []
decodeFrom s (b ∷ bs) = bitOf b ∷ decodeFrom (nextPair s) bs

encode : List Bool → List Base
encode = encodeFrom atTurn

decode : List Base → List Bool
decode = decodeFrom atTurn

decode-encode-from : ∀ s bits → decodeFrom s (encodeFrom s bits) ≡ bits
decode-encode-from s [] = refl
decode-encode-from atTurn (false ∷ bits)
  rewrite decode-encode-from cgTurn bits = refl
decode-encode-from atTurn (true ∷ bits)
  rewrite decode-encode-from cgTurn bits = refl
decode-encode-from cgTurn (false ∷ bits)
  rewrite decode-encode-from atTurn bits = refl
decode-encode-from cgTurn (true ∷ bits)
  rewrite decode-encode-from atTurn bits = refl

decode-encode : ∀ bits → decode (encode bits) ≡ bits
decode-encode = decode-encode-from atTurn

encode-prefix-step :
  ∀ s bit bits →
  encodeFrom s (bit ∷ bits) ≡
  unrank s bit ∷ encodeFrom (nextPair s) bits
encode-prefix-step s bit bits = refl

encodeTrace : ∀ s bits → Trace referenceMachine s (encodeFrom s bits)
encodeTrace s [] = emptyTrace
encodeTrace s (bit ∷ bits) =
  emitTrace (unrankLegal s bit) (encodeTrace (nextPair s) bits)

encoded-is-generable : ∀ bits → Generable referenceMachine (encode bits)
encoded-is-generable bits = encodeTrace atTurn bits

ViableNext : PairPhase → Set
ViableNext s = Σ Base (λ b → Legal s b)

cacheViable : PairPhase → Bool
cacheViable _ = true

cache-sound : ∀ s → cacheViable s ≡ true → ViableNext s
cache-sound s refl = unrank s false , unrankLegal s false

record ReferenceCodecReceipt : Set where
  field
    exactBranchArity : ∀ s → branchCount s ≡ suc (suc zero)
    legalSelection : ∀ s bit → Legal s (unrank s bit)
    payloadRoundtrip : ∀ bits → decode (encode bits) ≡ bits
    generatedLanguage : ∀ bits → Generable referenceMachine (encode bits)
    completionCacheSound : ∀ s → cacheViable s ≡ true → ViableNext s

referenceCodecReceipt : ReferenceCodecReceipt
referenceCodecReceipt = record
  { exactBranchArity = λ s → refl
  ; legalSelection = unrankLegal
  ; payloadRoundtrip = decode-encode
  ; generatedLanguage = encoded-is-generable
  ; completionCacheSound = cache-sound
  }
