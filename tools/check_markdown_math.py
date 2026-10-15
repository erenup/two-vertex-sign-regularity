#!/usr/bin/env python3
r"""Static guard for the repository's GitHub Markdown math profile (stdlib).

Run with Python 3.11+: python3 -I -B tools/check_markdown_math.py
The same command with -O must give the same result. --root PATH checks another
Git worktree without writing to it. Only tracked .md files are inspected.

The macro blacklist, ambiguous norm bars, legacy backslash math delimiters,
and environment allowlist apply everywhere, including code examples.
Ordinary $...$ and $$...$$ reject backslash-escaped ASCII punctuation and
raw < > & _ * ` characters, which Markdown can consume before math rendering.
Use GitHub's protected $`...`$ inline form or fenced math blocks for those
formulas. These Markdown checks exclude code spans and fenced blocks.
Literal dollars outside code must be escaped. The environment allowlist is a
conservative subset of MathJax's matrix/AMS environments. This is a static
regression guard, not a complete TeX/Markdown parser or a live rendering test.
"""

import argparse
from bisect import bisect_right
from pathlib import Path
import re
import string
import subprocess
import sys


DISALLOWED = frozenset("""
operatorname newcommand renewcommand providecommand DeclareMathOperator
def gdef edef xdef let futurelet require usepackage documentclass
newenvironment renewenvironment newtheorem newtheoremstyle
newcount newdimen newskip newmuskip newtoks catcode csname endcsname
input include write openout read openin special htmlClass htmlId htmlStyle
""".split())
ENVIRONMENTS = frozenset("""
array matrix pmatrix bmatrix Bmatrix vmatrix Vmatrix smallmatrix
cases aligned alignedat gathered split
""".split())
COMMAND = re.compile(r"\\([A-Za-z]+)")
ENVIRONMENT = re.compile(r"\\(?:begin|end)\s*\{([^{}]*)\}")
FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})([^\n]*)$", re.MULTILINE)
MARKDOWN_ESCAPABLE = frozenset(string.punctuation)
RAW_MATH_HAZARDS = frozenset("<>&_*`")


def blank(text):
    return "".join("\n" if c == "\n" else " " for c in text)


def without_fences(text):
    """Mask block fences without changing offsets or line numbers."""
    parts = []
    last = 0
    opening = None
    for match in FENCE.finditer(text):
        marker, info = match.groups()
        if opening is None:
            if marker[0] == "`" and "`" in info:
                continue
            opening = (match.start(), marker)
        elif (marker[0] == opening[1][0]
              and len(marker) >= len(opening[1]) and not info.strip()):
            start = opening[0]
            parts.extend((text[last:start], blank(text[start:match.end()])))
            last = match.end()
            opening = None
    if opening is not None:
        start = opening[0]
        parts.extend((text[last:start], blank(text[start:])))
        last = len(text)
    return "".join(parts) + text[last:]


def findings(text):
    """Return deterministic (line, diagnostic) pairs, with duplicate pairs removed."""
    newlines = [i for i, char in enumerate(text) if char == "\n"]
    hits = set()

    def hit(offset, message):
        hits.add((bisect_right(newlines, offset) + 1, message))

    for match in COMMAND.finditer(text):
        if match.group(1) in DISALLOWED:
            hit(match.start(), "disallowed macro: " + match.group())
    for match in re.finditer(r"\\\|", text):
        hit(match.start(), r"ambiguous norm bars: use \lVert and \rVert")
    for match in re.finditer(r"\\[()\[\]]", text):
        hit(match.start(), "legacy math delimiter: use dollar or math-fence markup")
    for match in ENVIRONMENT.finditer(text):
        if match.group(1) not in ENVIRONMENTS:
            hit(match.start(), "environment outside supported profile: " + match.group(1))

    masked = without_fences(text)
    i = 0
    mode = None
    start = 0
    while i < len(masked):
        if masked[i] == "\\" and mode != "protected":
            if (mode in ("inline", "display") and i + 1 < len(masked)
                    and masked[i + 1] in MARKDOWN_ESCAPABLE):
                hit(i, "Markdown-escapable sequence in " + mode + " math: "
                    + masked[i:i + 2])
            i += 2
            continue
        if mode == "protected" and masked.startswith("`$", i):
            mode = None
            i += 2
        elif mode == "display" and masked.startswith("$$", i):
            mode = None
            i += 2
        elif mode == "inline" and masked[i] == "$":
            mode = None
            i += 1
        elif mode is not None:
            if mode in ("inline", "display") and masked[i] in RAW_MATH_HAZARDS:
                hit(i, "raw " + mode + " character: " + masked[i])
            i += 1
        elif masked.startswith("$`", i):
            start, mode, i = i, "protected", i + 2
        elif masked.startswith("$$", i):
            start, mode, i = i, "display", i + 2
        elif masked[i] == "$":
            start, mode, i = i, "inline", i + 1
        elif masked[i] == "`":
            run = re.match(r"`+", masked[i:]).group()
            closing = re.search(r"(?<!`)" + run + r"(?!`)", masked[i + len(run):])
            i = i + len(run) + closing.end() if closing else i + len(run)
        else:
            i += 1
    if mode is not None:
        hit(start, "unclosed " + mode + " math delimiter")
    return sorted(hits)


def self_check():
    """Small rejection controls run on every invocation, including under -O."""
    bad = [("$\\" + name + "{x}$", "disallowed macro") for name in sorted(DISALLOWED)]
    for delimiter in ("$", "$$"):
        bad += [(delimiter + "a\\" + char + "b" + delimiter,
                 "Markdown-escapable sequence") for char in sorted(MARKDOWN_ESCAPABLE)]
        bad += [(delimiter + "a" + char + "b" + delimiter,
                 "raw " + ("inline" if delimiter == "$" else "display"))
                for char in sorted(RAW_MATH_HAZARDS)]
    cases = (
        r"A^-_{ij}=\begin{cases}L_{ij},&i+j\text{ even},\\U_{ij},&i+j\text{ odd},\end{cases}"
        "\n\\qquad\n"
        r"A^+_{ij}=\begin{cases}U_{ij},&i+j\text{ even},\\L_{ij},&i+j\text{ odd}.\end{cases}"
    )
    bad += [
        (r"$\|T\|_2$", "ambiguous norm"),
        (r"\(x\)", "legacy math delimiter"),
        (r"\[x\]", "legacy math delimiter"),
        (r"$$\begin{document}x\end{document}$$", "environment outside"),
        ("$a<b$", "raw inline"), ("$a>b$", "raw inline"),
        ("$a&b$", "raw inline"), ("$a\n<b$", "raw inline"),
        ("`$ok$` $a<b$", "raw inline"),
        ("```text\n$ignored$\n```\n$a<b$", "raw inline"),
        ("$$\n" + cases + "\n$$", "Markdown-escapable sequence in display"),
        ("$" + cases + "$", "Markdown-escapable sequence in inline"),
        ("~~~text\n$ignored$\n~~~\n$$a_b$$", "raw display"),
        ("````text\n```\n$ignored$\n````\n$a_b$", "raw inline"),
        ("`$a_b$` $c_d$", "raw inline"),
        ("$`a_b`$ $c_d$", "raw inline"),
        ("$`a\\`$ $c_d$", "raw inline"),
        ("$x", "unclosed"), ("$$x", "unclosed"), ("$`x", "unclosed"),
    ]
    good = [
        r"$\mathrm{diag}(1,2)$ and $`\lVert T\rVert_2\leq1`$",
        r"$0\lt\delta\lt1/2$; $a\gt b$; $`a\&b`$; \$5",
        "$`a<b & b>c`$", "$$a+b=c$$", "```math\na<b\n```",
        "`$a<b$` and `` `$a>b$` ``", "```sh\n$a<b$\n```",
        "~~~text\n$a&b$\n~~~", "plain a<b, a>b & <br>",
        "```math\n" + cases + "\n```",
        "$`" + cases + "`$",
        r"$`\{a_b,a*b\}\,\!\_\*\\c`$",
        "```math\n" + r"\{a_b,a*b\}\,\!\_\*\\c" + "\n```",
        "$`a\\`$",
        "`$a_b$` and `` `$a*b$` ``",
        "   ```math\na_b * c & d < e > f\n   ```",
        "````text\n```\n$a_b$\n````",
        "~~~text\n```\n$a_b$\n~~~",
        "```math\na_b * c & d < e > f",
        "```math\n" + r"\begin{aligned}a&=b\\c&=d\end{aligned}" + "\n```",
        "```math\n" + r"\begin{pmatrix}1&0\\0&1\end{pmatrix}" + "\n```",
    ]
    for text, expected in bad:
        if not any(expected in message for _, message in findings(text)):
            raise ValueError("rejection control failed: " + repr(text))
    for text in good:
        if findings(text):
            raise ValueError("acceptance control failed: " + repr(text))


def tracked_markdown(root):
    top = subprocess.run(["git", "-C", str(root), "rev-parse", "--show-toplevel"],
                         check=True, capture_output=True).stdout.decode().strip()
    if Path(top).resolve() != root:
        raise ValueError("--root must name the Git worktree root")
    records = subprocess.run(["git", "-C", str(root), "ls-files", "-z", "--", "*.md"],
                             check=True, capture_output=True).stdout
    names = sorted(set(records.decode("utf-8").split("\0")) - {""})
    if not names:
        raise ValueError("no tracked Markdown files")
    for name in names:
        path = root / name
        if (not path.is_file() or path.is_symlink()
                or path.resolve() != path or not path.is_relative_to(root)):
            raise ValueError("missing, nonregular or redirected tracked file: " + name)
    return names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    root = parser.parse_args().root.resolve()
    self_check()
    names = tracked_markdown(root)
    total = 0
    for name in names:
        for line, message in findings((root / name).read_text(encoding="utf-8")):
            print(f"{name}:{line}: {message}")
            total += 1
    if total:
        print(f"FAIL: {total} findings in {len(names)} tracked Markdown files")
        return 1
    print(f"PASS: {len(names)} tracked Markdown files; controls passed")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, UnicodeError, ValueError, subprocess.CalledProcessError) as exc:
        print("ERROR: " + str(exc), file=sys.stderr)
        sys.exit(2)
