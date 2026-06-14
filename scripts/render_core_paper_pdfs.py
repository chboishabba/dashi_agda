#!/usr/bin/env python3
"""Render the three live core paper drafts to TeX and PDF.

This is a deliberately small Markdown-to-LaTeX renderer for the current DASHI
paper drafts. It handles the patterns used by the live manuscripts: headings,
paragraphs, abstracts, block quotes, fenced code, ordered/unordered lists, and
pipe tables.
"""

from __future__ import annotations

import argparse
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LIVE_DIR = ROOT / "Docs" / "papers" / "live"
DEFAULT_OUT = ROOT / "build" / "papers"


PAPERS = (
    ("paper1_navier_stokes", LIVE_DIR / "Paper1NavierStokesClayDraft.md"),
    ("paper3_yang_mills", LIVE_DIR / "Paper3YangMillsClayDraft.md"),
    ("paper8_closure_architecture", LIVE_DIR / "Paper8UnificationDraft.md"),
)


LEDGER = ROOT / "Docs" / "support" / "live" / "PaperCommonCitationLedger.md"


BIB_ENTRIES = {
    "OS1973": """@article{OS1973,
  author = {Osterwalder, Konrad and Schrader, Robert},
  title = {Axioms for Euclidean Green's Functions},
  journal = {Communications in Mathematical Physics},
  volume = {31},
  pages = {83--112},
  year = {1973}
}
""",
    "OS1975": """@article{OS1975,
  author = {Osterwalder, Konrad and Schrader, Robert},
  title = {Axioms for Euclidean Green's Functions II},
  journal = {Communications in Mathematical Physics},
  volume = {42},
  pages = {281--305},
  year = {1975}
}
""",
    "GrossWilczek1973": """@article{GrossWilczek1973,
  author = {Gross, David J. and Wilczek, Frank},
  title = {Ultraviolet Behavior of Non-Abelian Gauge Theories},
  journal = {Physical Review Letters},
  volume = {30},
  number = {26},
  pages = {1343--1346},
  year = {1973},
  doi = {10.1103/PhysRevLett.30.1343}
}
""",
    "Politzer1973": """@article{Politzer1973,
  author = {Politzer, H. David},
  title = {Reliable Perturbative Results for Strong Interactions?},
  journal = {Physical Review Letters},
  volume = {30},
  number = {26},
  pages = {1346--1349},
  year = {1973},
  doi = {10.1103/PhysRevLett.30.1346}
}
""",
    "Seiler1982": """@book{Seiler1982,
  author = {Seiler, Erhard},
  title = {Gauge Theories as a Problem of Constructive Quantum Field Theory and Statistical Mechanics},
  series = {Lecture Notes in Physics},
  volume = {159},
  publisher = {Springer},
  year = {1982},
  doi = {10.1007/3-540-11597-5}
}
""",
    "JordanVonNeumann1935": """@article{JordanVonNeumann1935,
  author = {Jordan, Pascual and von Neumann, John},
  title = {On Inner Products in Linear, Metric Spaces},
  journal = {Annals of Mathematics},
  volume = {36},
  number = {3},
  pages = {719--723},
  year = {1935},
  doi = {10.2307/1968653}
}
""",
    "CoifmanMeyer": """@book{CoifmanMeyer,
  author = {Coifman, Ronald R. and Meyer, Yves},
  title = {Au delà des opérateurs pseudo-différentiels},
  publisher = {Astérisque},
  volume = {57},
  year = {1978}
}
""",
    "LerayHopf": """@article{LerayHopf,
  author = {Leray, Jean},
  title = {Sur le mouvement d'un liquide visqueux emplissant l'espace},
  journal = {Acta Mathematica},
  volume = {63},
  pages = {193--248},
  year = {1934},
  doi = {10.1007/BF02547354}
}
""",
    "BKM": """@article{BKM,
  author = {Beale, J. Thomas and Kato, Tosio and Majda, Andrew},
  title = {Remarks on the Breakdown of Smooth Solutions for the 3-D Euler Equations},
  journal = {Communications in Mathematical Physics},
  volume = {94},
  pages = {61--66},
  year = {1984}
}
""",
    "CKN": """@article{CKN,
  author = {Caffarelli, Luis and Kohn, Robert and Nirenberg, Louis},
  title = {Partial Regularity of Suitable Weak Solutions of the Navier-Stokes Equations},
  journal = {Communications on Pure and Applied Mathematics},
  volume = {35},
  number = {6},
  pages = {771--831},
  year = {1982},
  doi = {10.1002/cpa.3160350604}
}
""",
    "LeiRenTian2025": """@article{LeiRenTian2025,
  author = {Lei, Zhen and Ren, Xiao and Tian, Gang},
  title = {A Geometric Characterization of Potential Navier-Stokes Singularities},
  journal = {arXiv preprint},
  year = {2025},
  eprint = {2501.08976},
  archivePrefix = {arXiv},
  primaryClass = {math.AP}
}
""",
    "Seregin2012": """@article{Seregin2012,
  author = {Seregin, Gregory},
  title = {A Certain Necessary Condition of Potential Blow Up for Navier-Stokes Equations},
  journal = {Communications in Mathematical Physics},
  volume = {312},
  number = {3},
  pages = {833--845},
  year = {2012},
  doi = {10.1007/s00220-012-1440-0}
}
""",
    "ESS2003": """@article{ESS2003,
  author = {Escauriaza, Luis and Seregin, Gregory and Sverak, Vladimir},
  title = {Backward Uniqueness for Parabolic Equations and Regularity of Navier-Stokes Equations},
  journal = {Russian Mathematical Surveys},
  volume = {58},
  number = {2},
  pages = {211--250},
  year = {2003},
  doi = {10.1070/RM2003v058n02ABEH000609}
}
""",
    "Balaban1987": """@article{Balaban1987,
  author = {Balaban, Tadeusz},
  title = {Renormalization Group Approach to Lattice Gauge Field Theories. I. Generation of Effective Actions in a Small Field Approximation and a Coupling Constant Renormalization in Four Dimensions},
  journal = {Communications in Mathematical Physics},
  volume = {109},
  pages = {249--301},
  year = {1987}
}
""",
    "Balaban1988": """@article{Balaban1988,
  author = {Balaban, Tadeusz},
  title = {Renormalization Group Approach to Lattice Gauge Field Theories. II. Cluster Expansions},
  journal = {Communications in Mathematical Physics},
  volume = {116},
  pages = {1--22},
  year = {1988},
  note = {Cited as the Balaban 1988 Lemma 3 activity bound / constructive lattice-gauge multiscale input surface; polymer summability, trace norm transfer, and Option B deferred status are stated in the manuscript packet.}
}
""",
}


SPECIALS = {
    "\\": r"\textbackslash{}",
    "&": r"\&",
    "%": r"\%",
    "$": r"\$",
    "#": r"\#",
    "_": r"\_",
    "{": r"\{",
    "}": r"\}",
    "~": r"\textasciitilde{}",
    "^": r"\textasciicircum{}",
}


@dataclass(frozen=True)
class PaperMeta:
    title: str
    author: str
    date: str
    version: str
    status: str


def escape_tex(text: str) -> str:
    return "".join(SPECIALS.get(char, char) for char in text)


def inline_tex(text: str) -> str:
    parts = re.split(r"(`[^`]*`)", text)
    rendered: list[str] = []
    for part in parts:
        if not part:
            continue
        if part.startswith("`") and part.endswith("`"):
            rendered.append(r"\texttt{" + escape_tex(part[1:-1]) + "}")
            continue
        escaped = escape_tex(part)
        escaped = re.sub(r"\*\*([^*]+)\*\*", r"\\textbf{\1}", escaped)
        escaped = re.sub(r"\*([^*]+)\*", r"\\emph{\1}", escaped)
        rendered.append(escaped)
    return "".join(rendered)


def sanitize_title(title: str) -> str:
    title = re.sub(r"^Paper\s+\d+\s+Draft:\s*", "", title)
    return title.strip()


def clean_heading(text: str) -> tuple[str, bool]:
    appendix = text.startswith("Appendix ")
    if appendix:
        text = re.sub(r"^Appendix\s+[A-Z]\.\s*", "", text)
    else:
        text = re.sub(r"^\d+\.\d+\s*", "", text)
        text = re.sub(r"^\d+\.\s*", "", text)
    return text.strip(), appendix


def parse_meta(lines: list[str]) -> PaperMeta:
    title = "DASHI Core Paper"
    author = "DASHI project"
    date = ""
    version = ""
    status = ""
    for line in lines[:12]:
        if line.startswith("# "):
            title = sanitize_title(line[2:].strip())
        elif line.startswith("Author:"):
            author = line.split(":", 1)[1].strip().strip("`")
        elif line.startswith("Date:"):
            date = line.split(":", 1)[1].strip().strip("`")
        elif line.startswith("Version:"):
            version = line.split(":", 1)[1].strip().strip("`")
        elif line.startswith("Status:"):
            status = line.split(":", 1)[1].strip()
    return PaperMeta(title=title, author=author, date=date, version=version, status=status)


def is_table_at(lines: list[str], index: int) -> bool:
    return (
        index + 1 < len(lines)
        and lines[index].lstrip().startswith("|")
        and lines[index + 1].lstrip().startswith("|")
        and "---" in lines[index + 1]
    )


def split_table_row(line: str) -> list[str]:
    line = line.strip()
    if line.startswith("|"):
        line = line[1:]
    if line.endswith("|"):
        line = line[:-1]
    return [cell.strip() for cell in line.split("|")]


def render_table(rows: list[str]) -> list[str]:
    header = split_table_row(rows[0])
    body = [split_table_row(row) for row in rows[2:] if row.strip()]
    cols = max(len(header), *(len(row) for row in body)) if body else len(header)
    width = 0.94 / max(cols, 1)
    spec = " ".join([f"p{{{width:.2f}\\textwidth}}" for _ in range(cols)])
    out = [r"\begin{longtable}{" + spec + "}", r"\toprule"]
    out.append(" & ".join(inline_tex(cell) for cell in header) + r" \\")
    out.append(r"\midrule")
    for row in body:
        padded = row + [""] * (cols - len(row))
        out.append(" & ".join(inline_tex(cell) for cell in padded[:cols]) + r" \\")
    out.extend([r"\bottomrule", r"\end{longtable}"])
    return out


def close_list(out: list[str], list_kind: str | None) -> str | None:
    if list_kind == "itemize":
        out.append(r"\end{itemize}")
    elif list_kind == "enumerate":
        out.append(r"\end{enumerate}")
    return None


def paragraph_to_tex(paragraph: list[str]) -> str:
    return inline_tex(" ".join(part.strip() for part in paragraph).strip())


def convert_body(lines: list[str]) -> list[str]:
    out: list[str] = []
    paragraph: list[str] = []
    list_kind: str | None = None
    in_code = False
    in_abstract = False
    in_appendix = False

    def flush_paragraph() -> None:
        nonlocal paragraph
        if paragraph:
            out.append(paragraph_to_tex(paragraph))
            out.append("")
            paragraph = []

    i = 0
    while i < len(lines):
        line = lines[i].rstrip("\n")

        if line.startswith("# "):
            i += 1
            continue

        if line.startswith("Author:") or line.startswith("Date:") or line.startswith("Version:") or line.startswith("Status:"):
            i += 1
            continue

        if line.startswith("```"):
            flush_paragraph()
            list_kind = close_list(out, list_kind)
            if in_code:
                out.append(r"\end{Verbatim}")
                out.append("")
                in_code = False
            else:
                out.append(r"\begin{Verbatim}[breaklines=true,breakanywhere=true,fontsize=\small]")
                in_code = True
            i += 1
            continue

        if in_code:
            out.append(line)
            i += 1
            continue

        if is_table_at(lines, i):
            flush_paragraph()
            list_kind = close_list(out, list_kind)
            table_lines = []
            while i < len(lines) and lines[i].lstrip().startswith("|"):
                table_lines.append(lines[i].rstrip("\n"))
                i += 1
            out.extend(render_table(table_lines))
            out.append("")
            continue

        heading = re.match(r"^(#{2,4})\s+(.*)$", line)
        if heading:
            flush_paragraph()
            list_kind = close_list(out, list_kind)
            text, appendix = clean_heading(heading.group(2))
            if in_abstract:
                out.append(r"\end{abstract}")
                out.append("")
                in_abstract = False
            if appendix and not in_appendix:
                out.append(r"\appendix")
                in_appendix = True
            if text == "Abstract":
                out.append(r"\begin{abstract}")
                in_abstract = True
            else:
                level = len(heading.group(1))
                command = {2: "section", 3: "subsection", 4: "subsubsection"}[level]
                out.append("\\" + command + "{" + inline_tex(text) + "}")
            i += 1
            continue

        if not line.strip():
            flush_paragraph()
            list_kind = close_list(out, list_kind)
            i += 1
            continue

        unordered = re.match(r"^\s*-\s+(.*)$", line)
        ordered = re.match(r"^\s*\d+\.\s+(.*)$", line)
        if unordered or ordered:
            flush_paragraph()
            target = "itemize" if unordered else "enumerate"
            if list_kind != target:
                list_kind = close_list(out, list_kind)
                out.append(r"\begin{" + target + "}")
                list_kind = target
            item = (unordered or ordered).group(1)
            out.append(r"\item " + inline_tex(item))
            i += 1
            continue

        if line.startswith(">"):
            flush_paragraph()
            list_kind = close_list(out, list_kind)
            quote_lines = []
            while i < len(lines) and lines[i].startswith(">"):
                quote_lines.append(lines[i].lstrip("> ").rstrip("\n"))
                i += 1
            out.append(r"\begin{quote}")
            out.append(paragraph_to_tex(quote_lines))
            out.append(r"\end{quote}")
            out.append("")
            continue

        paragraph.append(line)
        i += 1

    flush_paragraph()
    close_list(out, list_kind)
    if in_abstract:
        out.append(r"\end{abstract}")
    return out


def render_tex(meta: PaperMeta, body: list[str], bib_name: str) -> str:
    title = inline_tex(meta.title)
    author = inline_tex(meta.author)
    date = inline_tex(meta.date)
    status = inline_tex(meta.status)
    version = inline_tex(meta.version)
    preamble = rf"""\documentclass[11pt]{{article}}
\usepackage[margin=1in]{{geometry}}
\usepackage{{amsmath,amssymb,amsthm}}
\usepackage{{booktabs,longtable,array}}
\usepackage{{enumitem}}
\usepackage{{microtype}}
\usepackage{{hyperref}}
\usepackage{{xcolor}}
\usepackage{{fontspec}}
\usepackage{{fvextra}}
\setmonofont{{DejaVu Sans Mono}}
\hypersetup{{colorlinks=true,linkcolor=blue,citecolor=blue,urlcolor=blue}}
\setlist{{nosep}}
\theoremstyle{{definition}}
\newtheorem{{definition}}{{Definition}}[section]
\theoremstyle{{plain}}
\newtheorem{{theorem}}[definition]{{Theorem}}
\newtheorem{{lemma}}[definition]{{Lemma}}
\newtheorem{{proposition}}[definition]{{Proposition}}
\theoremstyle{{remark}}
\newtheorem{{remark}}[definition]{{Remark}}
\title{{{title}}}
\author{{{author}}}
\date{{{date}}}

\begin{{document}}
\sloppy
\maketitle
\noindent\textbf{{Version:}} {version}\\
\textbf{{Status:}} {status}

"""
    tail = rf"""
\nocite{{*}}
\bibliographystyle{{plain}}
\bibliography{{{bib_name}}}
\end{{document}}
"""
    return preamble + "\n".join(body) + tail


def render_bib() -> str:
    entries: list[str] = []
    if not LEDGER.exists():
        return ""
    missing: list[str] = []
    for line in LEDGER.read_text(encoding="utf-8").splitlines():
        if not line.startswith("| `"):
            continue
        cells = split_table_row(line)
        if len(cells) < 3:
            continue
        key = cells[0].strip("`")
        if key in BIB_ENTRIES:
            entries.append(BIB_ENTRIES[key])
            continue
        missing.append(key)
    if missing:
        raise ValueError(
            "Missing concrete BibTeX entries for ledger keys: "
            + ", ".join(sorted(missing))
        )
    return "\n".join(entries)


def escape_bib(text: str) -> str:
    return text.replace("\\", "\\textbackslash{}").replace("{", "\\{").replace("}", "\\}")


def run_latexmk(tex_path: Path) -> None:
    subprocess.run(
        [
            "latexmk",
            "-xelatex",
            "-interaction=nonstopmode",
            "-halt-on-error",
            tex_path.name,
        ],
        cwd=tex_path.parent,
        check=True,
    )


def render_all(out_dir: Path, skip_pdf: bool) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    bib_path = out_dir / "core_references.bib"
    bib_path.write_text(render_bib(), encoding="utf-8")

    for slug, md_path in PAPERS:
        lines = md_path.read_text(encoding="utf-8").splitlines()
        meta = parse_meta(lines)
        body = convert_body(lines)
        tex = render_tex(meta, body, "core_references")
        tex_path = out_dir / f"{slug}.tex"
        tex_path.write_text(tex, encoding="utf-8")
        if not skip_pdf:
            run_latexmk(tex_path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--skip-pdf", action="store_true")
    args = parser.parse_args()
    render_all(args.out_dir, args.skip_pdf)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
