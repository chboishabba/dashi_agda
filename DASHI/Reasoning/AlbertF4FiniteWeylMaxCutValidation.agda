module DASHI.Reasoning.AlbertF4FiniteWeylMaxCutValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Reasoning.AlbertF4FiniteWeylMaxCutExact

foldedWeyl1152-source-written :
  leanFoldedWeylOrder1152SourceWritten canonicalFiniteAlbertF4Boundary ≡ true
foldedWeyl1152-source-written = refl

f4-root48-source-written :
  leanF4RootSet48SourceWritten canonicalFiniteAlbertF4Boundary ≡ true
f4-root48-source-written = refl

finite-one-plus-26-source-written :
  leanFiniteOnePlus26SourceWritten canonicalFiniteAlbertF4Boundary ≡ true
finite-one-plus-26-source-written = refl

linear-transport-source-written :
  leanLinearAlbertTransportSourceWritten canonicalFiniteAlbertF4Boundary ≡ true
linear-transport-source-written = refl

ternary-basis-source-written :
  leanTernaryOriginPlus26BasisTransportSourceWritten canonicalFiniteAlbertF4Boundary ≡ true
ternary-basis-source-written = refl

natural-relative-240-no-go-source-written :
  leanNaturalRelative240E6NoGoSourceWritten canonicalFiniteAlbertF4Boundary ≡ true
natural-relative-240-no-go-source-written = refl

agda-finite-f4-not-manufactured :
  agdaFoldedWeylKernelPaidHere canonicalFiniteAlbertF4Boundary ≡ false
agda-finite-f4-not-manufactured = refl

albert-product-compatibility-open :
  actualAlbertProductCompatibilityPaid canonicalFiniteAlbertF4Boundary ≡ false
albert-product-compatibility-open = refl

f4-aut-group-open :
  actualF4AutomorphismGroupRecognitionPaid canonicalFiniteAlbertF4Boundary ≡ false
f4-aut-group-open = refl

alternative-240-open :
  alternativeTernary240RecognitionPaid canonicalFiniteAlbertF4Boundary ≡ false
alternative-240-open = refl
