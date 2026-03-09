#!/usr/bin/env python3

import argparse
import pathlib
import re

ROOT = pathlib.Path(".").resolve()

# ------------------------------------------------------------
# Mapping from old module prefixes to new directory layout
# ------------------------------------------------------------

RULES = [
    # Geometry
    ("DASHI.Geometry.RealIsotropyInstanceShiftTailPerm",
     "DASHI/Geometry/Isotropy/Instance/ShiftTailPerm"),

    ("DASHI.Geometry.SignatureUniqueness31Proof",
     "DASHI/Geometry/Signature/Uniqueness31Proof"),

    ("DASHI.Geometry.SignatureElimination",
     "DASHI/Geometry/Signature/Elimination"),

    ("DASHI.Geometry.QuadraticPolarizationFromForm",
     "DASHI/Geometry/Quadratic/PolarizationFromForm"),

    ("DASHI.Geometry.ClosestPoint",
     "DASHI/Geometry/ClosestPoint"),

    ("DASHI.Geometry.Parallelogram",
     "DASHI/Geometry/Parallelogram"),

    # Ultrametric / metric
    ("DASHI.Ultrametric.ConeMonotonicity",
     "DASHI/Metric/Cone/Monotonicity"),

    ("MonsterUltrametric",
     "Monster/Ultrametric"),

    # Monster subsystem
    ("MonsterMask", "Monster/Mask"),
    ("MonsterStep", "Monster/Step"),
    ("MonsterTrace", "Monster/Trace"),
    ("MonsterTraceSound", "Monster/TraceSound"),
    ("MonsterProjection", "Monster/Projection"),

    # Kernel
    ("KernelAlgebra", "Kernel/Algebra"),
    ("OperatorMonoid", "Kernel/Monoid"),
    ("Stabilisation", "Kernel/Stabilisation"),

    # MDL
    ("MDL", "MDL/Core"),
    ("MDLOptimalSkeleton", "MDL/OptimalSkeleton"),
    ("PrimeSubsetModel", "MDL/PrimeSubsetModel"),

    # Ontology
    ("CICADA71", "Ontology/CICADA71"),
    ("MonsterOntologyContracts", "Ontology/Contracts"),
    ("GodelLattice", "Ontology/GodelLattice"),
    ("HeckeScan", "Ontology/Hecke/Scan"),
]

# ------------------------------------------------------------
# Utilities
# ------------------------------------------------------------


def find_agda_files():
    return [path for path in ROOT.rglob("*.agda") if path.is_file()]


def module_name_from_path(path):
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def replace_module_header(text, old, new):
    pattern = rf"module\s+{re.escape(old)}\s+where"
    repl = f"module {new} where"
    return re.sub(pattern, repl, text)


def replace_imports(text, old, new):
    text = re.sub(rf"open import {re.escape(old)}", f"open import {new}", text)
    text = re.sub(rf"import {re.escape(old)}", f"import {new}", text)
    return text

# ------------------------------------------------------------
# Build move plan
# ------------------------------------------------------------


def build_plan():
    plan = []

    for old, new in RULES:
        old_file = ROOT / (old.replace(".", "/") + ".agda")

        if old_file.exists():
            new_file = ROOT / (new + ".agda")
            plan.append((old, new, old_file, new_file))

    return plan

# ------------------------------------------------------------
# Apply reorganisation
# ------------------------------------------------------------


def apply_changes(plan):

    for old_mod, new_mod, old_file, new_file in plan:

        print(f"\nProcessing {old_mod}")
        print(f" -> {new_file}")

        text = old_file.read_text()

        text = replace_module_header(text, old_mod, new_mod)

        new_file.parent.mkdir(parents=True, exist_ok=True)
        new_file.write_text(text)

        old_file.unlink()


def update_imports(pairs):

    for path in find_agda_files():

        text = path.read_text()
        new_text = text

        for old_mod, new_mod in pairs:
            new_text = replace_imports(new_text, old_mod, new_mod)

        if new_text != text:
            print("Updating imports:", path)
            path.write_text(new_text)

# ------------------------------------------------------------
# Dry run
# ------------------------------------------------------------


def show_plan(plan):

    print("\nReorganisation plan\n")

    for old_mod, new_mod, old_file, new_file in plan:

        print(f"{old_mod}")
        print(f"  {old_file}")
        print(f"  ->")
        print(f"  {new_file}")
        print()

# ------------------------------------------------------------
# Main
# ------------------------------------------------------------


def main():

    parser = argparse.ArgumentParser()
    parser.add_argument("--apply", action="store_true",
                        help="apply changes (otherwise dry-run)")
    args = parser.parse_args()

    plan = build_plan()

    if plan:
        show_plan(plan)
    else:
        print("No files matched rules.")

    if args.apply:
        if plan:
            print("\nApplying changes...\n")
            apply_changes(plan)
            print("\nDone moving files.")
        else:
            print("\nNo file moves needed.")

        print("\nUpdating imports...")
        update_imports(RULES)
    else:
        print("\nDry run only. Use --apply to execute.")


if __name__ == "__main__":
    main()
