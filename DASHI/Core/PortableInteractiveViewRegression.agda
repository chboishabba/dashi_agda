module DASHI.Core.PortableInteractiveViewRegression where

import DASHI.Core.PortableInteractiveViewExact as UI

activationContractExists : Set
activationContractExists = UI.ActivationContract

canonicalActivationPaid : UI.ActivationContract
canonicalActivationPaid = UI.canonicalActivationContract

frontendEquivalencePaid : UI.CanonicalFrontendEquivalence
frontendEquivalencePaid = UI.canonicalFrontendEquivalence
