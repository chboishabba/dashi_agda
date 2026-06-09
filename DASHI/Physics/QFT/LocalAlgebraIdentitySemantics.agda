module DASHI.Physics.QFT.LocalAlgebraIdentitySemantics where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.AQFTTypedNetSurface as AQFT

------------------------------------------------------------------------
-- Local algebra identity semantics.
--
-- The AQFT/QFT surfaces in this repository expose the local algebra carrier
-- abstractly as `AQFT.LocalAlgebra region`.  That is enough to define the
-- identity endomorphism on each local algebra and prove the identity law by
-- definitional equality, without fabricating any new algebraic structure.

record DASHILocalAlgebraIdentitySemantics (region : AQFT.Region) : Setω where
  field
    localAlgebraCarrier :
      Set

    localAlgebraCarrierIsAQFT :
      localAlgebraCarrier ≡ AQFT.LocalAlgebra region

    identityAction :
      localAlgebraCarrier →
      localAlgebraCarrier

    identityActionLaw :
      ∀ (a : localAlgebraCarrier) →
      identityAction a ≡ a

    identityActionIsCanonical :
      ∀ (a : localAlgebraCarrier) →
      identityAction a ≡ a

open DASHILocalAlgebraIdentitySemantics public

canonicalDASHILocalAlgebraIdentitySemantics :
  ∀ (region : AQFT.Region) →
  DASHILocalAlgebraIdentitySemantics region
canonicalDASHILocalAlgebraIdentitySemantics region = record
  { localAlgebraCarrier = AQFT.LocalAlgebra region
  ; localAlgebraCarrierIsAQFT = refl
  ; identityAction = λ a → a
  ; identityActionLaw = λ a → refl
  ; identityActionIsCanonical = λ a → refl
  }

identityActionOnLocalAlgebra :
  ∀ {region : AQFT.Region} →
  AQFT.LocalAlgebra region →
  AQFT.LocalAlgebra region
identityActionOnLocalAlgebra a = a

identityActionOnLocalAlgebraLaw :
  ∀ {region : AQFT.Region} (a : AQFT.LocalAlgebra region) →
  identityActionOnLocalAlgebra a ≡ a
identityActionOnLocalAlgebraLaw a = refl

localAlgebraIdentitySemanticsWitness :
  ∀ (region : AQFT.Region) →
  DASHILocalAlgebraIdentitySemantics region
localAlgebraIdentitySemanticsWitness = canonicalDASHILocalAlgebraIdentitySemantics

localAlgebraIdentitySemanticsBoundary : List String
localAlgebraIdentitySemanticsBoundary =
  "The AQFT typed net surface is packaged explicitly through the canonical net receipt"
  ∷ "The local algebra carrier is the repository's abstract AQFT.LocalAlgebra region"
  ∷ "The identity action is definitional identity on the carrier"
  ∷ []
