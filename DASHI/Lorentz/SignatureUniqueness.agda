module DASHI.Lorentz.SignatureUniqueness where

open import DASHI.Unifier using (Poset; ChainAntichain; LorentzInterval)

record SignatureBundle {E : Set} (P : Poset E) (CA : ChainAntichain P) : Set₁ where
  field
    interval : LorentzInterval P CA
    signature-proof : LorentzInterval.signature-3+1 interval
    p3-uniqueness : LorentzInterval.p3-unique interval
    scaling-stability : Set

record SignatureConsequences {E : Set} {P : Poset E} {CA : ChainAntichain P}
  (bundle : SignatureBundle P CA) : Set₁ where
  field
    signature-proof : LorentzInterval.signature-3+1 (SignatureBundle.interval bundle)
    p3-uniqueness : LorentzInterval.p3-unique (SignatureBundle.interval bundle)
    scaling-stability : Set

Signature-uniqueness
  : ∀ {E : Set} {P : Poset E} {CA : ChainAntichain P}
  → (bundle : SignatureBundle P CA)
  → SignatureConsequences bundle
Signature-uniqueness bundle =
  record
    { signature-proof = SignatureBundle.signature-proof bundle
    ; p3-uniqueness = SignatureBundle.p3-uniqueness bundle
    ; scaling-stability = SignatureBundle.scaling-stability bundle
    }
