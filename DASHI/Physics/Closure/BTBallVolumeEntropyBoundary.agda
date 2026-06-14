module DASHI.Physics.Closure.BTBallVolumeEntropyBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level)

data ⊥ : Set where

infixr 5 _∷_

data List {ℓ : Level} (A : Set ℓ) : Set ℓ where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

------------------------------------------------------------------------
-- Bruhat-Tits regular-tree ball, sphere, and product-volume entropy
-- boundary.
--
-- This is a finite/named constructible receipt.  It records the exact
-- regular-tree formulas for q = 2, 3, 7, the product carrier
--
--   T3 x T2 x T7,
--
-- and the product asymptotic constants:
--
--   |B_T3(r)| |B_T2(r)| |B_T7(r)| ~ 8 * 42^r,
--   h = log42,
--   kappaBT prefactor = 8,
--   rhoEff = 42^-1.
--
-- It deliberately does not promote these non-Archimedean finite/product
-- formulas to smooth kappa-noncollapsing, Clay Yang-Mills, Navier-Stokes,
-- or geometrization claims.

data BTBallVolumeEntropyStatus : Set where
  btBallSphereVolumeEntropyRecordedNoSmoothPromotion :
    BTBallVolumeEntropyStatus

data TreeRadiusName : Set where
  radius0 :
    TreeRadiusName
  radius1 :
    TreeRadiusName
  radius2 :
    TreeRadiusName
  radius3 :
    TreeRadiusName

canonicalFiniteRadii : List TreeRadiusName
canonicalFiniteRadii =
  radius0
  ∷ radius1
  ∷ radius2
  ∷ radius3
  ∷ []

data BruhatTitsQParameter : Set where
  q2 :
    BruhatTitsQParameter
  q3 :
    BruhatTitsQParameter
  q7 :
    BruhatTitsQParameter

canonicalQParameters : List BruhatTitsQParameter
canonicalQParameters =
  q2
  ∷ q3
  ∷ q7
  ∷ []

data ProductTreeFactor : Set where
  T3Factor :
    ProductTreeFactor
  T2Factor :
    ProductTreeFactor
  T7Factor :
    ProductTreeFactor

canonicalProductTreeFactors : List ProductTreeFactor
canonicalProductTreeFactors =
  T3Factor
  ∷ T2Factor
  ∷ T7Factor
  ∷ []

data EntropyBoundaryFact : Set where
  regularTreeBallFormulaRecorded :
    EntropyBoundaryFact
  regularTreeSphereFormulaRecorded :
    EntropyBoundaryFact
  q2FiniteTableRecorded :
    EntropyBoundaryFact
  q3FiniteTableRecorded :
    EntropyBoundaryFact
  q7FiniteTableRecorded :
    EntropyBoundaryFact
  productT3xT2xT7VolumeFormulaRecorded :
    EntropyBoundaryFact
  productAsymptoticPrefactorEightRecorded :
    EntropyBoundaryFact
  productBaseFortyTwoRecorded :
    EntropyBoundaryFact
  entropyLabelLog42Recorded :
    EntropyBoundaryFact
  kappaBTPrefactorEightRecorded :
    EntropyBoundaryFact
  rhoEffFortyTwoInverseRecorded :
    EntropyBoundaryFact
  smoothPromotionExplicitlyBlocked :
    EntropyBoundaryFact

canonicalEntropyBoundaryFacts : List EntropyBoundaryFact
canonicalEntropyBoundaryFacts =
  regularTreeBallFormulaRecorded
  ∷ regularTreeSphereFormulaRecorded
  ∷ q2FiniteTableRecorded
  ∷ q3FiniteTableRecorded
  ∷ q7FiniteTableRecorded
  ∷ productT3xT2xT7VolumeFormulaRecorded
  ∷ productAsymptoticPrefactorEightRecorded
  ∷ productBaseFortyTwoRecorded
  ∷ entropyLabelLog42Recorded
  ∷ kappaBTPrefactorEightRecorded
  ∷ rhoEffFortyTwoInverseRecorded
  ∷ smoothPromotionExplicitlyBlocked
  ∷ []

data BTVolumeEntropyBlocker : Set where
  smoothKappaNoncollapsingNotConstructedFromBTBalls :
    BTVolumeEntropyBlocker
  noArchimedeanManifoldLimitFromProductTreeReceipt :
    BTVolumeEntropyBlocker
  clayYangMillsPromotionBlocked :
    BTVolumeEntropyBlocker
  navierStokesPromotionBlocked :
    BTVolumeEntropyBlocker
  geometrizationPromotionBlocked :
    BTVolumeEntropyBlocker
  terminalMillenniumPromotionBlocked :
    BTVolumeEntropyBlocker

canonicalBTVolumeEntropyBlockers : List BTVolumeEntropyBlocker
canonicalBTVolumeEntropyBlockers =
  smoothKappaNoncollapsingNotConstructedFromBTBalls
  ∷ noArchimedeanManifoldLimitFromProductTreeReceipt
  ∷ clayYangMillsPromotionBlocked
  ∷ navierStokesPromotionBlocked
  ∷ geometrizationPromotionBlocked
  ∷ terminalMillenniumPromotionBlocked
  ∷ []

data SmoothOrMillenniumPromotion : Set where

smoothOrMillenniumPromotionImpossibleHere :
  SmoothOrMillenniumPromotion →
  ⊥
smoothOrMillenniumPromotionImpossibleHere ()

regularTreeBallFormulaText : String
regularTreeBallFormulaText =
  "|B(r)| = 1 + (q+1)(q^r-1)/(q-1)"

regularTreeSphereFormulaText : String
regularTreeSphereFormulaText =
  "|S(r)| = (q+1)q^(r-1)"

regularTreeSphereFormulaDomainText : String
regularTreeSphereFormulaDomainText =
  "sphere formula is for r >= 1; |S(0)| = 1 is recorded separately"

productBallFormulaText : String
productBallFormulaText =
  "|B_T3xT2xT7(r)| = |B_T3(r)| |B_T2(r)| |B_T7(r)|"

productAsymptoticFormulaText : String
productAsymptoticFormulaText =
  "|B_T3xT2xT7(r)| ~ 8 * 42^r"

entropyLabelText : String
entropyLabelText =
  "log42"

rhoEffText : String
rhoEffText =
  "rhoEff = 42^-1"

kappaBTText : String
kappaBTText =
  "kappaBT prefactor = 8"

record RegularTreeFiniteFormulaTable : Set where
  field
    qParameter :
      BruhatTitsQParameter

    qValue :
      Nat

    regularity :
      Nat

    regularityIsQPlusOne :
      String

    ballFormula :
      String

    ballFormulaIsCanonical :
      ballFormula ≡ regularTreeBallFormulaText

    sphereFormula :
      String

    sphereFormulaIsCanonical :
      sphereFormula ≡ regularTreeSphereFormulaText

    sphereFormulaDomain :
      String

    sphereFormulaDomainIsCanonical :
      sphereFormulaDomain ≡ regularTreeSphereFormulaDomainText

    ballRadius0 :
      Nat

    sphereRadius0 :
      Nat

    sphereRadius1 :
      Nat

    ballRadius1 :
      Nat

    sphereRadius2 :
      Nat

    ballRadius2 :
      Nat

    sphereRadius3 :
      Nat

    ballRadius3 :
      Nat

open RegularTreeFiniteFormulaTable public

canonicalQ2FiniteFormulaTable : RegularTreeFiniteFormulaTable
canonicalQ2FiniteFormulaTable =
  record
    { qParameter =
        q2
    ; qValue =
        2
    ; regularity =
        3
    ; regularityIsQPlusOne =
        "q=2 gives a 3-regular Bruhat-Tits tree"
    ; ballFormula =
        regularTreeBallFormulaText
    ; ballFormulaIsCanonical =
        refl
    ; sphereFormula =
        regularTreeSphereFormulaText
    ; sphereFormulaIsCanonical =
        refl
    ; sphereFormulaDomain =
        regularTreeSphereFormulaDomainText
    ; sphereFormulaDomainIsCanonical =
        refl
    ; ballRadius0 =
        1
    ; sphereRadius0 =
        1
    ; sphereRadius1 =
        3
    ; ballRadius1 =
        4
    ; sphereRadius2 =
        6
    ; ballRadius2 =
        10
    ; sphereRadius3 =
        12
    ; ballRadius3 =
        22
    }

canonicalQ3FiniteFormulaTable : RegularTreeFiniteFormulaTable
canonicalQ3FiniteFormulaTable =
  record
    { qParameter =
        q3
    ; qValue =
        3
    ; regularity =
        4
    ; regularityIsQPlusOne =
        "q=3 gives a 4-regular Bruhat-Tits tree"
    ; ballFormula =
        regularTreeBallFormulaText
    ; ballFormulaIsCanonical =
        refl
    ; sphereFormula =
        regularTreeSphereFormulaText
    ; sphereFormulaIsCanonical =
        refl
    ; sphereFormulaDomain =
        regularTreeSphereFormulaDomainText
    ; sphereFormulaDomainIsCanonical =
        refl
    ; ballRadius0 =
        1
    ; sphereRadius0 =
        1
    ; sphereRadius1 =
        4
    ; ballRadius1 =
        5
    ; sphereRadius2 =
        12
    ; ballRadius2 =
        17
    ; sphereRadius3 =
        36
    ; ballRadius3 =
        53
    }

canonicalQ7FiniteFormulaTable : RegularTreeFiniteFormulaTable
canonicalQ7FiniteFormulaTable =
  record
    { qParameter =
        q7
    ; qValue =
        7
    ; regularity =
        8
    ; regularityIsQPlusOne =
        "q=7 gives an 8-regular Bruhat-Tits tree"
    ; ballFormula =
        regularTreeBallFormulaText
    ; ballFormulaIsCanonical =
        refl
    ; sphereFormula =
        regularTreeSphereFormulaText
    ; sphereFormulaIsCanonical =
        refl
    ; sphereFormulaDomain =
        regularTreeSphereFormulaDomainText
    ; sphereFormulaDomainIsCanonical =
        refl
    ; ballRadius0 =
        1
    ; sphereRadius0 =
        1
    ; sphereRadius1 =
        8
    ; ballRadius1 =
        9
    ; sphereRadius2 =
        56
    ; ballRadius2 =
        65
    ; sphereRadius3 =
        392
    ; ballRadius3 =
        457
    }

canonicalFiniteFormulaTables : List RegularTreeFiniteFormulaTable
canonicalFiniteFormulaTables =
  canonicalQ2FiniteFormulaTable
  ∷ canonicalQ3FiniteFormulaTable
  ∷ canonicalQ7FiniteFormulaTable
  ∷ []

record ProductT3xT2xT7FiniteVolumeTable : Set where
  field
    productFactors :
      List ProductTreeFactor

    productFactorsAreCanonical :
      productFactors ≡ canonicalProductTreeFactors

    productFormula :
      String

    productFormulaIsCanonical :
      productFormula ≡ productBallFormulaText

    productAsymptoticFormula :
      String

    productAsymptoticFormulaIsCanonical :
      productAsymptoticFormula ≡ productAsymptoticFormulaText

    qProductBase :
      Nat

    qProductBaseIsFortyTwo :
      qProductBase ≡ 42

    productAsymptoticPrefactor :
      Nat

    productAsymptoticPrefactorIsEight :
      productAsymptoticPrefactor ≡ 8

    productBallRadius0 :
      Nat

    productBallRadius0IsOne :
      productBallRadius0 ≡ 1

    productBallRadius1 :
      Nat

    productBallRadius1IsOneEighty :
      productBallRadius1 ≡ 180

    productBallRadius2 :
      Nat

    productBallRadius2IsElevenThousandFifty :
      productBallRadius2 ≡ 11050

    productBallRadius3 :
      Nat

    productBallRadius3IsFiveHundredThirtyTwoThousandEightHundredSixtyTwo :
      productBallRadius3 ≡ 532862

    diagonalSphereRadius1 :
      Nat

    diagonalSphereRadius1IsNinetySix :
      diagonalSphereRadius1 ≡ 96

    diagonalSphereRadius2 :
      Nat

    diagonalSphereRadius2IsFourThousandThirtyTwo :
      diagonalSphereRadius2 ≡ 4032

    diagonalSphereRadius3 :
      Nat

    diagonalSphereRadius3IsOneHundredSixtyNineThousandThreeHundredFortyFour :
      diagonalSphereRadius3 ≡ 169344

open ProductT3xT2xT7FiniteVolumeTable public

canonicalProductT3xT2xT7FiniteVolumeTable :
  ProductT3xT2xT7FiniteVolumeTable
canonicalProductT3xT2xT7FiniteVolumeTable =
  record
    { productFactors =
        canonicalProductTreeFactors
    ; productFactorsAreCanonical =
        refl
    ; productFormula =
        productBallFormulaText
    ; productFormulaIsCanonical =
        refl
    ; productAsymptoticFormula =
        productAsymptoticFormulaText
    ; productAsymptoticFormulaIsCanonical =
        refl
    ; qProductBase =
        42
    ; qProductBaseIsFortyTwo =
        refl
    ; productAsymptoticPrefactor =
        8
    ; productAsymptoticPrefactorIsEight =
        refl
    ; productBallRadius0 =
        1
    ; productBallRadius0IsOne =
        refl
    ; productBallRadius1 =
        180
    ; productBallRadius1IsOneEighty =
        refl
    ; productBallRadius2 =
        11050
    ; productBallRadius2IsElevenThousandFifty =
        refl
    ; productBallRadius3 =
        532862
    ; productBallRadius3IsFiveHundredThirtyTwoThousandEightHundredSixtyTwo =
        refl
    ; diagonalSphereRadius1 =
        96
    ; diagonalSphereRadius1IsNinetySix =
        refl
    ; diagonalSphereRadius2 =
        4032
    ; diagonalSphereRadius2IsFourThousandThirtyTwo =
        refl
    ; diagonalSphereRadius3 =
        169344
    ; diagonalSphereRadius3IsOneHundredSixtyNineThousandThreeHundredFortyFour =
        refl
    }

record BTBallVolumeEntropyBoundary : Set where
  field
    status :
      BTBallVolumeEntropyStatus

    finiteRadii :
      List TreeRadiusName

    finiteRadiiAreCanonical :
      finiteRadii ≡ canonicalFiniteRadii

    qParameters :
      List BruhatTitsQParameter

    qParametersAreCanonical :
      qParameters ≡ canonicalQParameters

    q2FormulaTable :
      RegularTreeFiniteFormulaTable

    q2TableIsCanonical :
      q2FormulaTable ≡ canonicalQ2FiniteFormulaTable

    q3FormulaTable :
      RegularTreeFiniteFormulaTable

    q3TableIsCanonical :
      q3FormulaTable ≡ canonicalQ3FiniteFormulaTable

    q7FormulaTable :
      RegularTreeFiniteFormulaTable

    q7TableIsCanonical :
      q7FormulaTable ≡ canonicalQ7FiniteFormulaTable

    finiteFormulaTables :
      List RegularTreeFiniteFormulaTable

    finiteFormulaTablesAreCanonical :
      finiteFormulaTables ≡ canonicalFiniteFormulaTables

    productVolumeTable :
      ProductT3xT2xT7FiniteVolumeTable

    productVolumeTableIsCanonical :
      productVolumeTable ≡ canonicalProductT3xT2xT7FiniteVolumeTable

    productBase :
      Nat

    productBaseIsFortyTwo :
      productBase ≡ 42

    productAsymptoticPrefactor :
      Nat

    productAsymptoticPrefactorIsEight :
      productAsymptoticPrefactor ≡ 8

    entropyLabel :
      String

    entropyLabelIsLog42 :
      entropyLabel ≡ entropyLabelText

    kappaBTPrefactor :
      Nat

    kappaBTPrefactorIsEight :
      kappaBTPrefactor ≡ 8

    kappaBTLabel :
      String

    kappaBTLabelIsCanonical :
      kappaBTLabel ≡ kappaBTText

    rhoEffNumerator :
      Nat

    rhoEffNumeratorIsOne :
      rhoEffNumerator ≡ 1

    rhoEffDenominator :
      Nat

    rhoEffDenominatorIsFortyTwo :
      rhoEffDenominator ≡ 42

    rhoEffLabel :
      String

    rhoEffLabelIsCanonical :
      rhoEffLabel ≡ rhoEffText

    smoothKappaNoncollapsingPromoted :
      Bool

    smoothKappaNoncollapsingPromotedIsFalse :
      smoothKappaNoncollapsingPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    navierStokesPromoted :
      Bool

    navierStokesPromotedIsFalse :
      navierStokesPromoted ≡ false

    geometrizationPromoted :
      Bool

    geometrizationPromotedIsFalse :
      geometrizationPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    promotionFlags :
      List SmoothOrMillenniumPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    facts :
      List EntropyBoundaryFact

    factsAreCanonical :
      facts ≡ canonicalEntropyBoundaryFacts

    blockers :
      List BTVolumeEntropyBlocker

    blockersAreCanonical :
      blockers ≡ canonicalBTVolumeEntropyBlockers

    receiptBoundary :
      List String

open BTBallVolumeEntropyBoundary public

canonicalBTBallVolumeEntropyBoundary :
  BTBallVolumeEntropyBoundary
canonicalBTBallVolumeEntropyBoundary =
  record
    { status =
        btBallSphereVolumeEntropyRecordedNoSmoothPromotion
    ; finiteRadii =
        canonicalFiniteRadii
    ; finiteRadiiAreCanonical =
        refl
    ; qParameters =
        canonicalQParameters
    ; qParametersAreCanonical =
        refl
    ; q2FormulaTable =
        canonicalQ2FiniteFormulaTable
    ; q2TableIsCanonical =
        refl
    ; q3FormulaTable =
        canonicalQ3FiniteFormulaTable
    ; q3TableIsCanonical =
        refl
    ; q7FormulaTable =
        canonicalQ7FiniteFormulaTable
    ; q7TableIsCanonical =
        refl
    ; finiteFormulaTables =
        canonicalFiniteFormulaTables
    ; finiteFormulaTablesAreCanonical =
        refl
    ; productVolumeTable =
        canonicalProductT3xT2xT7FiniteVolumeTable
    ; productVolumeTableIsCanonical =
        refl
    ; productBase =
        42
    ; productBaseIsFortyTwo =
        refl
    ; productAsymptoticPrefactor =
        8
    ; productAsymptoticPrefactorIsEight =
        refl
    ; entropyLabel =
        entropyLabelText
    ; entropyLabelIsLog42 =
        refl
    ; kappaBTPrefactor =
        8
    ; kappaBTPrefactorIsEight =
        refl
    ; kappaBTLabel =
        kappaBTText
    ; kappaBTLabelIsCanonical =
        refl
    ; rhoEffNumerator =
        1
    ; rhoEffNumeratorIsOne =
        refl
    ; rhoEffDenominator =
        42
    ; rhoEffDenominatorIsFortyTwo =
        refl
    ; rhoEffLabel =
        rhoEffText
    ; rhoEffLabelIsCanonical =
        refl
    ; smoothKappaNoncollapsingPromoted =
        false
    ; smoothKappaNoncollapsingPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; navierStokesPromoted =
        false
    ; navierStokesPromotedIsFalse =
        refl
    ; geometrizationPromoted =
        false
    ; geometrizationPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; facts =
        canonicalEntropyBoundaryFacts
    ; factsAreCanonical =
        refl
    ; blockers =
        canonicalBTVolumeEntropyBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        regularTreeBallFormulaText
        ∷ regularTreeSphereFormulaText
        ∷ "q=2 table: spheres 1,3,6,12 and balls 1,4,10,22"
        ∷ "q=3 table: spheres 1,4,12,36 and balls 1,5,17,53"
        ∷ "q=7 table: spheres 1,8,56,392 and balls 1,9,65,457"
        ∷ productBallFormulaText
        ∷ productAsymptoticFormulaText
        ∷ "product base 42, entropy label log42, kappaBT prefactor 8, rhoEff 42^-1"
        ∷ "Smooth kappa-noncollapsing, Clay/YM, Navier-Stokes, geometrization, and terminal promotion remain false"
        ∷ []
    }

canonicalBallFormulaTextRecorded :
  ballFormula canonicalQ2FiniteFormulaTable
  ≡
  regularTreeBallFormulaText
canonicalBallFormulaTextRecorded =
  refl

canonicalSphereFormulaTextRecorded :
  sphereFormula canonicalQ7FiniteFormulaTable
  ≡
  regularTreeSphereFormulaText
canonicalSphereFormulaTextRecorded =
  refl

canonicalProductBase42Recorded :
  productBase canonicalBTBallVolumeEntropyBoundary
  ≡
  42
canonicalProductBase42Recorded =
  refl

canonicalProductPrefactor8Recorded :
  productAsymptoticPrefactor canonicalBTBallVolumeEntropyBoundary
  ≡
  8
canonicalProductPrefactor8Recorded =
  refl

canonicalEntropyLog42Recorded :
  entropyLabel canonicalBTBallVolumeEntropyBoundary
  ≡
  entropyLabelText
canonicalEntropyLog42Recorded =
  refl

canonicalKappaBTPrefactor8Recorded :
  kappaBTPrefactor canonicalBTBallVolumeEntropyBoundary
  ≡
  8
canonicalKappaBTPrefactor8Recorded =
  refl

canonicalRhoEff42InverseRecorded :
  rhoEffDenominator canonicalBTBallVolumeEntropyBoundary
  ≡
  42
canonicalRhoEff42InverseRecorded =
  refl

canonicalSmoothKappaNoncollapsingBlocked :
  smoothKappaNoncollapsingPromoted canonicalBTBallVolumeEntropyBoundary
  ≡
  false
canonicalSmoothKappaNoncollapsingBlocked =
  refl

canonicalClayYangMillsBlocked :
  clayYangMillsPromoted canonicalBTBallVolumeEntropyBoundary
  ≡
  false
canonicalClayYangMillsBlocked =
  refl

canonicalNavierStokesBlocked :
  navierStokesPromoted canonicalBTBallVolumeEntropyBoundary
  ≡
  false
canonicalNavierStokesBlocked =
  refl

canonicalGeometrizationBlocked :
  geometrizationPromoted canonicalBTBallVolumeEntropyBoundary
  ≡
  false
canonicalGeometrizationBlocked =
  refl

canonicalTerminalPromotionBlocked :
  terminalPromotion canonicalBTBallVolumeEntropyBoundary
  ≡
  false
canonicalTerminalPromotionBlocked =
  refl
