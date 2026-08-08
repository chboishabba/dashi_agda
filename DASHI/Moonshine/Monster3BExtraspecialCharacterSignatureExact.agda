module DASHI.Moonshine.Monster3BExtraspecialCharacterSignatureExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- I. M. Isaacs,
-- "Character Theory of Finite Groups",
-- Dover Publications, 1994 reprint of the 1976 edition.
-- ISBN: 978-0-486-68014-9; no DOI assigned.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- R. W. Barraclough and R. A. Wilson,
-- "The Character Table of a Maximal Subgroup of the Monster",
-- LMS Journal of Computation and Mathematics 10 (2007), 161--175.
-- DOI: 10.1112/S1461157000001352.
--
-- DASHI CONTRIBUTION
--
-- Record the complete class-shape of the two nonlinear characters of an
-- extraspecial group of order 3^(1+12), and prove the exact degree-square and
-- norm numerators.  The values are represented in the free C3 phase basis
-- {1,zeta,zeta^2}; no floating complex arithmetic enters the proof.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

------------------------------------------------------------------------
-- Formal C3 phase traces.
------------------------------------------------------------------------

record C3Trace : Set where
  constructor c3trace
  field
    oneCoefficient : Nat
    zetaCoefficient : Nat
    zetaSquaredCoefficient : Nat

open C3Trace public

zeroTrace : C3Trace
zeroTrace = c3trace 0 0 0

scaleTrace : Nat → C3Trace → C3Trace
scaleTrace scale value =
  c3trace
    (scale * oneCoefficient value)
    (scale * zetaCoefficient value)
    (scale * zetaSquaredCoefficient value)

------------------------------------------------------------------------
-- Extraspecial class types relevant to nonlinear characters.
------------------------------------------------------------------------

data ExtraspecialClassKind : Set where
  identityClass : ExtraspecialClassKind
  centralZetaClass : ExtraspecialClassKind
  centralZetaSquaredClass : ExtraspecialClassKind
  noncentralClass : ExtraspecialClassKind

heisenbergDegree : Nat
heisenbergDegree = 729

heisenbergZetaCharacter : ExtraspecialClassKind → C3Trace
heisenbergZetaCharacter identityClass = c3trace heisenbergDegree 0 0
heisenbergZetaCharacter centralZetaClass = c3trace 0 heisenbergDegree 0
heisenbergZetaCharacter centralZetaSquaredClass = c3trace 0 0 heisenbergDegree
heisenbergZetaCharacter noncentralClass = zeroTrace

heisenbergZetaSquaredCharacter : ExtraspecialClassKind → C3Trace
heisenbergZetaSquaredCharacter identityClass = c3trace heisenbergDegree 0 0
heisenbergZetaSquaredCharacter centralZetaClass = c3trace 0 0 heisenbergDegree
heisenbergZetaSquaredCharacter centralZetaSquaredClass = c3trace 0 heisenbergDegree 0
heisenbergZetaSquaredCharacter noncentralClass = zeroTrace

heisenbergIdentityDegree :
  oneCoefficient (heisenbergZetaCharacter identityClass) ≡ 729
heisenbergIdentityDegree = refl

heisenbergNoncentralTraceVanishes :
  heisenbergZetaCharacter noncentralClass ≡ zeroTrace
heisenbergNoncentralTraceVanishes = refl

conjugateHeisenbergNoncentralTraceVanishes :
  heisenbergZetaSquaredCharacter noncentralClass ≡ zeroTrace
conjugateHeisenbergNoncentralTraceVanishes = refl

------------------------------------------------------------------------
-- Character completeness arithmetic.
------------------------------------------------------------------------

linearCharacterCount : Nat
linearCharacterCount = 531441

nonlinearCharacterCount : Nat
nonlinearCharacterCount = 2

extraspecialOrder : Nat
extraspecialOrder = 1594323

nonlinearDegreeSquare : Nat
nonlinearDegreeSquare = heisenbergDegree * heisenbergDegree

extraspecialCharacterDegreeSquareSum : Nat
extraspecialCharacterDegreeSquareSum =
  linearCharacterCount
  + nonlinearCharacterCount * nonlinearDegreeSquare

extraspecialCharacterDegreeSquareSumIsOrder :
  extraspecialCharacterDegreeSquareSum ≡ extraspecialOrder
extraspecialCharacterDegreeSquareSumIsOrder = refl

-- The nonlinear character is supported on the three central elements.  Its
-- Hermitian norm numerator is therefore 3 * 729^2, exactly |E|.
heisenbergNormNumerator : Nat
heisenbergNormNumerator = 3 * nonlinearDegreeSquare

heisenbergNormNumeratorIsExtraspecialOrder :
  heisenbergNormNumerator ≡ extraspecialOrder
heisenbergNormNumeratorIsExtraspecialOrder = refl

------------------------------------------------------------------------
-- The actual 3B phase-sector target.
------------------------------------------------------------------------

phaseMultiplicity : Nat
phaseMultiplicity = 90

zetaSectorDegree : Nat
zetaSectorDegree = phaseMultiplicity * heisenbergDegree

zetaSectorDegreeIs65610 : zetaSectorDegree ≡ 65610
zetaSectorDegreeIs65610 = refl

ninetyHeisenbergCharacter : ExtraspecialClassKind → C3Trace
ninetyHeisenbergCharacter class =
  scaleTrace phaseMultiplicity (heisenbergZetaCharacter class)

ninetyConjugateHeisenbergCharacter : ExtraspecialClassKind → C3Trace
ninetyConjugateHeisenbergCharacter class =
  scaleTrace phaseMultiplicity (heisenbergZetaSquaredCharacter class)

ninetyHeisenbergIdentityValue :
  oneCoefficient (ninetyHeisenbergCharacter identityClass) ≡ 65610
ninetyHeisenbergIdentityValue = refl

ninetyHeisenbergCentralZetaValue :
  zetaCoefficient (ninetyHeisenbergCharacter centralZetaClass) ≡ 65610
ninetyHeisenbergCentralZetaValue = refl

ninetyHeisenbergCentralZetaSquaredValue :
  zetaSquaredCoefficient
    (ninetyHeisenbergCharacter centralZetaSquaredClass)
  ≡ 65610
ninetyHeisenbergCentralZetaSquaredValue = refl

ninetyHeisenbergNoncentralValue :
  ninetyHeisenbergCharacter noncentralClass ≡ zeroTrace
ninetyHeisenbergNoncentralValue = refl

ninetyConjugateHeisenbergNoncentralValue :
  ninetyConjugateHeisenbergCharacter noncentralClass ≡ zeroTrace
ninetyConjugateHeisenbergNoncentralValue = refl

------------------------------------------------------------------------
-- Exact promotion statement at the character-signature level.
--
-- Once an actual restricted character is identified with this four-class
-- signature, its irreducible decomposition is forced: the degree-square budget
-- leaves only the two nonlinear Heisenberg characters above the two nontrivial
-- central characters, and dimension 65610 forces multiplicity 90.
------------------------------------------------------------------------

record ActualZetaCharacterRecognition
  (actualCharacter : ExtraspecialClassKind → C3Trace) : Set where
  constructor actual-zeta-character-recognition
  field
    identityValue :
      actualCharacter identityClass
      ≡ ninetyHeisenbergCharacter identityClass
    centralZetaValue :
      actualCharacter centralZetaClass
      ≡ ninetyHeisenbergCharacter centralZetaClass
    centralZetaSquaredValue :
      actualCharacter centralZetaSquaredClass
      ≡ ninetyHeisenbergCharacter centralZetaSquaredClass
    noncentralValue :
      actualCharacter noncentralClass
      ≡ ninetyHeisenbergCharacter noncentralClass

open ActualZetaCharacterRecognition public

actualKernelCharacterIdentity :
  ∀ {actualCharacter} →
  ActualZetaCharacterRecognition actualCharacter →
  (class : ExtraspecialClassKind) →
  actualCharacter class ≡ ninetyHeisenbergCharacter class
actualKernelCharacterIdentity recognition identityClass =
  identityValue recognition
actualKernelCharacterIdentity recognition centralZetaClass =
  centralZetaValue recognition
actualKernelCharacterIdentity recognition centralZetaSquaredClass =
  centralZetaSquaredValue recognition
actualKernelCharacterIdentity recognition noncentralClass =
  noncentralValue recognition
