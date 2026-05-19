module DASHI.Physics.Closure.G3ContractionCarrier where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Physics.Closure.G3ConcreteOperators as G3Concrete
import DASHI.Physics.Closure.G3PoincareGalileiCarrierChain as G3Chain
import DASHI.Physics.Closure.SchrodingerEvolutionScope as SES

------------------------------------------------------------------------
-- G3 contraction carrier probe.
--
-- The selected concrete operators now give a real FactorVec-backed p2
-- support package: P/H/K endomorphisms, p2 filtration, and prime-bump
-- commutation laws.  This module checks whether that support is enough to
-- inhabit the Schrodinger-scope Poincare-to-Galilei contraction carrier.
--
-- Result: fail-closed.  The current package is still state-endomorphism
-- support only.  It does not supply the dependent Schrodinger obligation
-- fields needed to build a PoincareSectorCarrier, GalileiSectorCarrier, or
-- PoincareToGalileiContractionCarrier.

data G3ContractionCarrierStatus : Set where
  selectedOperatorsOnlyNoContractionCarrier :
    G3ContractionCarrierStatus

data G3ContractionCarrierMissingLaw : Set where
  missingSchrodingerPoincareSectorCarrier :
    G3ContractionCarrierMissingLaw

  missingSchrodingerNonRelativisticLimitCarrier :
    G3ContractionCarrierMissingLaw

  missingSchrodingerGalileiSectorCarrier :
    G3ContractionCarrierMissingLaw

  missingSchrodingerPoincareToGalileiContractionCarrier :
    G3ContractionCarrierMissingLaw

  missingWaveFunctionScalarRing :
    G3ContractionCarrierMissingLaw

  missingLieBracketOrCommutatorSemantics :
    G3ContractionCarrierMissingLaw

  missingFilteredBracketCompatibility :
    G3ContractionCarrierMissingLaw

  missingAssociatedGradedGalileiIdentification :
    G3ContractionCarrierMissingLaw

  missingContractionParameterLaw :
    G3ContractionCarrierMissingLaw

Obligations :
  SES.G3HamiltonianEvolutionObligations
    SES.canonicalG3SchrodingerInputs
Obligations =
  SES.obligationSchrodingerHamiltonianEvolutionFields

SchrodingerPoincareSectorCarrier :
  Set
SchrodingerPoincareSectorCarrier =
  SES.G3HamiltonianEvolutionObligations.PoincareSectorCarrier
    Obligations

SchrodingerNonRelativisticLimitCarrier :
  Set
SchrodingerNonRelativisticLimitCarrier =
  SES.G3HamiltonianEvolutionObligations.NonRelativisticLimitCarrier
    Obligations

SchrodingerGalileiSectorCarrier :
  Set
SchrodingerGalileiSectorCarrier =
  SES.G3HamiltonianEvolutionObligations.GalileiSectorCarrier
    Obligations

SchrodingerPoincareToGalileiContractionCarrier :
  Set
SchrodingerPoincareToGalileiContractionCarrier =
  SES.G3HamiltonianEvolutionObligations.PoincareToGalileiContractionCarrier
    Obligations

SchrodingerPoincareToGalileiContractionDerived :
  Set
SchrodingerPoincareToGalileiContractionDerived =
  SES.PoincareToGalileiContractionDerivedType Obligations

record G3ContractionCarrierFailClosedReceipt : Setω where
  field
    status :
      G3ContractionCarrierStatus

    selectedOperatorPackageName :
      String

    conditionalOperatorSurfaceName :
      String

    carrierChainSurfaceName :
      String

    carrierLevelObstructionName :
      String

    poincareSectorCarrier :
      Set

    poincareSectorCarrierIsExact :
      poincareSectorCarrier ≡ SchrodingerPoincareSectorCarrier

    nonRelativisticLimitCarrier :
      Set

    nonRelativisticLimitCarrierIsExact :
      nonRelativisticLimitCarrier
      ≡
      SchrodingerNonRelativisticLimitCarrier

    galileiSectorCarrier :
      Set

    galileiSectorCarrierIsExact :
      galileiSectorCarrier ≡ SchrodingerGalileiSectorCarrier

    poincareToGalileiContractionCarrier :
      Set

    poincareToGalileiContractionCarrierIsExact :
      poincareToGalileiContractionCarrier
      ≡
      SchrodingerPoincareToGalileiContractionCarrier

    requiredContractionFunctionType :
      Set

    requiredContractionFunctionTypeIsExact :
      requiredContractionFunctionType
      ≡
      (SchrodingerPoincareSectorCarrier →
       SchrodingerGalileiSectorCarrier →
       SchrodingerPoincareToGalileiContractionCarrier)

    requiredDerivedTheorem :
      Set

    requiredDerivedTheoremIsExact :
      requiredDerivedTheorem
      ≡
      SchrodingerPoincareToGalileiContractionDerived

    selectedOperatorsAvailable :
      List String

    missingLaws :
      List G3ContractionCarrierMissingLaw

    nextImplementableSurface :
      String

    nonPromotionBoundary :
      List String

canonicalG3ContractionCarrierFailClosedReceipt :
  G3ContractionCarrierFailClosedReceipt
canonicalG3ContractionCarrierFailClosedReceipt =
  record
    { status =
        selectedOperatorsOnlyNoContractionCarrier
    ; selectedOperatorPackageName =
        "G3Concrete.canonicalG3SelectedConcreteOperatorPackage"
    ; conditionalOperatorSurfaceName =
        "G3P2.G3P2OperatorSurface"
    ; carrierChainSurfaceName =
        "G3Chain.canonicalG3PoincareGalileiCarrierChain"
    ; carrierLevelObstructionName =
        "SES.canonicalG3PoincareToGalileiCarrierLevelObstruction"
    ; poincareSectorCarrier =
        SchrodingerPoincareSectorCarrier
    ; poincareSectorCarrierIsExact =
        refl
    ; nonRelativisticLimitCarrier =
        SchrodingerNonRelativisticLimitCarrier
    ; nonRelativisticLimitCarrierIsExact =
        refl
    ; galileiSectorCarrier =
        SchrodingerGalileiSectorCarrier
    ; galileiSectorCarrierIsExact =
        refl
    ; poincareToGalileiContractionCarrier =
        SchrodingerPoincareToGalileiContractionCarrier
    ; poincareToGalileiContractionCarrierIsExact =
        refl
    ; requiredContractionFunctionType =
        SchrodingerPoincareSectorCarrier →
        SchrodingerGalileiSectorCarrier →
        SchrodingerPoincareToGalileiContractionCarrier
    ; requiredContractionFunctionTypeIsExact =
        refl
    ; requiredDerivedTheorem =
        SchrodingerPoincareToGalileiContractionDerived
    ; requiredDerivedTheoremIsExact =
        refl
    ; selectedOperatorsAvailable =
        "SelectedG3State = GL.FactorVec"
        ∷ "selectedP, selectedH, and selectedK are concrete prime-bump endomorphisms"
        ∷ "selectedPPCommutes and selectedHPCommutes follow from primeBumpCommutes"
        ∷ "selectedP2Filtration and selectedHFiltrationStep are inhabited"
        ∷ []
    ; missingLaws =
        missingSchrodingerPoincareSectorCarrier
        ∷ missingSchrodingerNonRelativisticLimitCarrier
        ∷ missingSchrodingerGalileiSectorCarrier
        ∷ missingSchrodingerPoincareToGalileiContractionCarrier
        ∷ missingWaveFunctionScalarRing
        ∷ missingLieBracketOrCommutatorSemantics
        ∷ missingFilteredBracketCompatibility
        ∷ missingAssociatedGradedGalileiIdentification
        ∷ missingContractionParameterLaw
        ∷ []
    ; nextImplementableSurface =
        "Define a wave-function/operator algebra over SelectedG3State, then prove filtered bracket compatibility and an associated-graded Galilei identification before attempting SES.PoincareToGalileiContractionDerivedType."
    ; nonPromotionBoundary =
        "Fail-closed receipt only: this module does not inhabit SchrodingerPoincareToGalileiContractionCarrier"
        ∷ "The selected concrete operators are state endomorphisms over GL.FactorVec, not yet a wave-function scalar ring or Lie bracket algebra"
        ∷ "The exact carrier target remains SES.G3HamiltonianEvolutionObligations.PoincareToGalileiContractionCarrier obligationSchrodingerHamiltonianEvolutionFields"
        ∷ "The exact theorem target remains SES.PoincareToGalileiContractionDerivedType obligationSchrodingerHamiltonianEvolutionFields"
        ∷ "No G3 promotion is claimed"
        ∷ []
    }
