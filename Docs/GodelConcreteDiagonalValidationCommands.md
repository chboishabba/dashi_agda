# Focused validation commands

The existing classical CS validation root owns this tranche. No parallel CI planner is introduced.

```sh
agda -i . -i /usr/share/agda-stdlib DASHI/ComputerScience/GodelArithmeticRawSyntaxExact.agda
agda -i . -i /usr/share/agda-stdlib DASHI/ComputerScience/GodelArithmeticDeBruijnInstantiationExact.agda
agda -i . -i /usr/share/agda-stdlib DASHI/ComputerScience/GodelArithmeticPrefixStreamCodecExact.agda
agda -i . -i /usr/share/agda-stdlib DASHI/ComputerScience/GodelArithmeticBase12StreamStepExact.agda
agda -i . -i /usr/share/agda-stdlib DASHI/ComputerScience/GodelArithmeticBase12NatRetractionExact.agda
agda -i . -i /usr/share/agda-stdlib DASHI/ComputerScience/GodelPrimitiveRecursiveRepresentabilityBridgeExact.agda
agda -i . -i /usr/share/agda-stdlib DASHI/ComputerScience/GodelBase12SelfSubstitutionPRFrontierExact.agda
agda -i . -i /usr/share/agda-stdlib DASHI/ComputerScience/GodelSourceNativeDiagonalFrontierExact.agda
agda -i . -i /usr/share/agda-stdlib DASHI/ComputerScience/ComputerScienceFibreFoundationValidationExact.agda
```

These are validation demands, not receipts. A command listed here does not imply it has run successfully.
