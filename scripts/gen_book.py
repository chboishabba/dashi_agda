from __future__ import annotations

import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EVERYTHING = ROOT / "DASHI" / "Everything.agda"
OUT_DIR = ROOT / "build" / "latex"
MODULES_TXT = OUT_DIR / "modules.txt"
BOOK_TEX = OUT_DIR / "Book.tex"


def parse_modules(path: Path) -> list[str]:
    modules: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line.startswith("import "):
            continue
        mod = line.split("import ", 1)[1].strip()
        if not mod:
            continue
        modules.append(mod)
    # Deduplicate while preserving order
    seen = set()
    ordered = []
    for m in modules:
        if m in seen:
            continue
        seen.add(m)
        ordered.append(m)
    return ordered


def module_to_path(mod: str) -> Path:
    return Path(mod.replace(".", "/") + ".agda")


def main() -> None:
    modules = parse_modules(EVERYTHING)
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    # Write modules.txt for CI xargs
    module_paths = [module_to_path(m) for m in modules]
    MODULES_TXT.write_text("\n".join(str(p) for p in module_paths) + "\n", encoding="utf-8")

    # Write Book.tex that inputs each module source inside a code block.
    # This avoids Agda's LaTeX backend per-module and keeps the PDF build fast.
    lines = []
    lines.append(r"\documentclass{article}")
    lines.append(r"\usepackage{fontspec}")
    
    # JuliaMono has industry-leading coverage for Agda/Math symbols
    lines.append(r"\setmonofont{JuliaMono}[Scale=MatchLowercase]")
    
    lines.append(r"\usepackage{fancyvrb}")
    lines.append(r"\begin{document}")
    lines.append(r"\section*{DASHI Book}")
    lines.append(r"\tableofcontents")
    lines.append("")
    for mod, path in zip(modules, module_paths):
        rel_path = Path(os.path.relpath(path, OUT_DIR))
        lines.append(r"\clearpage")
        safe_title = mod.replace("_", r"\_")
        lines.append(rf"\section*{{\texttt{{{safe_title}}}}}")
        lines.append(rf"\addcontentsline{{toc}}{{section}}{{\texttt{{{safe_title}}}}}")
        lines.append(rf"\VerbatimInput{{{rel_path.as_posix()}}}")
        lines.append("")
    lines.append(r"\end{document}")

    BOOK_TEX.write_text("\n".join(lines) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
