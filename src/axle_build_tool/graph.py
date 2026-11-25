"""Offline HTML rendering of the manifest as a Cytoscape.js graph.

`axbt graph` writes a single-page HTML visualization of the manifest's
dependency structure (by default `.axbt/graph.html`): compound nodes
module -> file -> declaration, with file-level import edges and
declaration-to-declaration edges from the extraction dependency lists
(populated by the outcome-record work).

**Colors key only on the outcome stamps, never inferred** (the stamp
contract records only successful, full, unstubbed submissions):

- `verified` (green) — has a verification stamp.
- `checked` (yellow) — has a check stamp but no verification stamp:
  checked-clean in full context, still awaiting kernel verification.
  Declaration kinds that can never verify (defs, ...) land on `done`
  (green), which is their terminal state ("done on their own tier").
- `unchecked` (orange) — neither stamp: never judged by a full,
  unstubbed payload.

Container nodes (files, modules) roll up to the weakest constituent
declaration state (orange > yellow > green); containers with no
extracted declarations (declaration-free import-only files) are
`empty` (grey). Manifests written before the stamp work degrade
automatically to the verified-vs-orange palette — no stub-and-hope
inference anywhere.

The page is interactive (pan/zoom, hover tooltips, click-to-highlight
a node's transitive dependency cone and inspect its metadata, live
search, and edge toggles) from the single pinned Cytoscape.js CDN
script alone. Data reaches the page as JSON embedded in a
`<script type="application/json">` block: `json.dumps` with every
`<`/`>` escaped to `\\u003c`/`\\u003e` — valid JSON that cannot form
`</script>` (or any tag) in the page — and every manifest-derived
string is escaped into tooltip markup with `html.escape`. Names are
never interpolated into HTML raw.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable
import html
import json
from pathlib import Path
import re
import textwrap
from typing import Any

from axle_build_tool.config import CACHE_DIRNAME
from axle_build_tool.manifest import Manifest, ManifestNode, closure_nodes
from axle_build_tool.payloads import (
    _find_standalone_comment_start,
    _is_attached_prefix_line,
    dotted_stem_of,
)
from axle_build_tool.stubbing import PROOF_KINDS as _VERIFIABLE_KINDS
from axle_build_tool.stubbing import bare_name

#: Active project root forwarded from `write_graph` so `build_graph_data`
#: keeps its two-argument signature for existing callers/tests.
_active_project_root: Path | None = None

_IMPORT_HEADER_RE = re.compile(r"^\s*import\s+[A-Za-z_][A-Za-z0-9_.]*\s*(?:--.*)?$")
_HEADING_RE = re.compile(r"^(#{1,4})\s+(.+)$")
_UL_RE = re.compile(r"^\s*[-*+]\s+(.+)$")
_OL_RE = re.compile(r"^\s*\d+\.\s+(.+)$")
_BQ_RE = re.compile(r"^\s*>\s?(.*)$")
_FENCE_RE = re.compile(r"```([^\n`]*)\n([\s\S]*?)```")
_DISPLAY_DOLLAR_RE = re.compile(r"\$\$([\s\S]+?)\$\$")
_DISPLAY_BRACKET_RE = re.compile(r"\\\[([\s\S]+?)\\\]")
_DISPLAY_ENV_RE = re.compile(
    r"(\\begin\{(align\*?|aligned|equation\*?|gather\*?|gathered|cases|pmatrix|bmatrix|vmatrix|matrix|CD)\}[\s\S]+?\\end\{\2\})"
)
_INLINE_CODE_RE = re.compile(r"`([^`\n]+)`")
_INLINE_PAREN_RE = re.compile(r"\\\(((?:[^\n]|\n(?!\s*\n))+?)\\\)")
_INLINE_DOLLAR_RE = re.compile(r"(?<!\\)\$(?!\s)((?:[^$\n]|\n(?!\s*\n))+?)(?<!\s)\$(?!\d)")
_LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)\s]+)\)")
_BOLD_RE = re.compile(r"\*\*(.+?)\*\*")
_ITALIC_RE = re.compile(r"(?<!\*)\*(?!\*)([^*\n]+?)(?<!\*)\*(?!\*)")
_PROSE_TEXTTT_RE = re.compile(r"\\(?:texttt|mathtt)\{([^{}\n]+)\}")
_PROSE_TEXTBF_RE = re.compile(r"\\textbf\{([^{}\n]+)\}")
_PROSE_TEXTIT_RE = re.compile(r"\\(?:textit|emph)\{([^{}\n]+)\}")


def _clean_lean_comment(raw: str) -> str:
    """Strip Lean comment delimiters (`/-!`, `/--`, `/-`, `-/`, `--`) and dedent."""
    stripped = raw.strip()
    if stripped.startswith(("/-!", "/--", "/-")):
        opener = stripped[:3] if stripped.startswith(("/-!", "/--")) else stripped[:2]
        body = stripped[len(opener):]
        if body.endswith("-/"):
            body = body[:-2]
        lines = body.splitlines()
        while lines and not lines[0].strip():
            lines.pop(0)
        while lines and not lines[-1].strip():
            lines.pop()
        if not lines:
            return ""
        first_had_inline = bool(stripped[len(opener):].splitlines()[0].strip()) if stripped[len(opener):].splitlines() else False
        if first_had_inline and len(lines) > 1:
            head = lines[0].lstrip()
            tail = textwrap.dedent("\n".join(lines[1:]))
            return f"{head}\n{tail}".strip()
        return textwrap.dedent("\n".join(lines)).strip()

    cleaned_lines: list[str] = []
    for line in stripped.splitlines():
        s = line.lstrip()
        if s.startswith("-- "):
            cleaned_lines.append(s[3:])
        elif s.startswith("--"):
            cleaned_lines.append(s[2:])
        else:
            cleaned_lines.append(line)
    return textwrap.dedent("\n".join(cleaned_lines)).strip()


def _extract_file_and_decl_sources(
    source: str, declarations: list[Any]
) -> tuple[str, dict[str, tuple[str, str, int]]]:
    """Extract the file's module docstring (`/-! ... -/`) and each
    declaration's `(leading_comment, code_text, start_line)` from raw Lean source.
    """
    lines = source.splitlines()
    if not lines:
        return "", {}

    ordered = sorted(declarations, key=lambda d: (d.line_pos, d.end_line_pos, d.name))
    first_decl_idx = max(0, ordered[0].line_pos - 1) if ordered else len(lines)

    # Module docstring (`/-! ... -/`) appearing before the first declaration.
    file_doc_parts: list[str] = []
    idx = 0
    header_limit = min(first_decl_idx, len(lines))
    while idx < header_limit:
        line_s = lines[idx].strip()
        if line_s.startswith("/-!"):
            if "-/" in line_s[3:]:
                file_doc_parts.append(_clean_lean_comment(lines[idx]))
                idx += 1
                continue
            close_idx = idx + 1
            while close_idx < header_limit and "-/" not in lines[close_idx]:
                close_idx += 1
            if close_idx < header_limit:
                file_doc_parts.append(
                    _clean_lean_comment("\n".join(lines[idx : close_idx + 1]))
                )
                idx = close_idx + 1
                continue
            break
        if line_s == "" or line_s == "prelude" or _IMPORT_HEADER_RE.match(lines[idx]):
            idx += 1
            continue
        idx += 1
    file_doc = "\n\n".join(part for part in file_doc_parts if part)

    decl_sources: dict[str, tuple[str, str, int]] = {}
    prev_end = 0
    for pos, decl in enumerate(ordered):
        start = max(0, decl.line_pos - 1)
        next_start = (
            ordered[pos + 1].line_pos - 1 if pos + 1 < len(ordered) else len(lines)
        )
        end = min(decl.end_line_pos, next_start, len(lines))
        if start >= len(lines) or end <= start:
            decl_sources[decl.name] = ("", decl.signature or "", decl.line_pos)
            continue

        code_start = start
        decl_doc = ""
        probe = start - 1
        bound = max(0, prev_end)
        while probe >= bound:
            stripped = lines[probe].strip()
            if stripped == "":
                probe -= 1
                continue
            if _is_attached_prefix_line(lines[probe]):
                code_start = probe
                probe -= 1
                continue
            open_idx = _find_standalone_comment_start(lines, probe, bound)
            if open_idx is not None:
                if lines[open_idx].lstrip().startswith("/-!"):
                    break
                decl_doc = _clean_lean_comment("\n".join(lines[open_idx : probe + 1]))
                break
            if lines[probe].lstrip().startswith("--"):
                top = probe
                while top - 1 >= bound and lines[top - 1].lstrip().startswith("--"):
                    top -= 1
                decl_doc = _clean_lean_comment("\n".join(lines[top : probe + 1]))
                break
            break

        decl_code = "\n".join(lines[code_start:end])
        decl_sources[decl.name] = (decl_doc, decl_code, code_start + 1)
        prev_end = max(prev_end, end)

    return file_doc, decl_sources


def _unescape_latex_text(s: str) -> str:
    """Unescape LaTeX text-mode escapes (`\\_`, `\\{`, `\\}`, `\\ `, etc.) in HTML-escaped text."""
    return (
        s.replace("\\_", "_")
        .replace("\\{", "&#123;")
        .replace("\\}", "&#125;")
        .replace("\\%", "%")
        .replace("\\#", "#")
        .replace("\\$", "$")
        .replace("\\&amp;", "&amp;")
        .replace("\\ ", " ")
    )


def _render_latex_math(tex: str, display: bool = False) -> str:
    """Emit a math container carrying raw LaTeX in `data-latex` for client-side KaTeX rendering."""
    normalized = tex.strip() if display else re.sub(r"\s*\n\s*", " ", tex.strip())
    escaped = html.escape(normalized, quote=True)
    if display:
        return f'<div class="math-display" data-latex="{escaped}">{escaped}</div>'
    return f'<span class="math-inline" data-latex="{escaped}">{escaped}</span>'


def _safe_link(match: re.Match[str]) -> str:
    label = match.group(1)
    url = match.group(2)
    unescaped_url = html.unescape(url).strip().lower()
    if unescaped_url.startswith(("https://", "http://", "#")) or (
        ":" not in unescaped_url.split("/", 1)[0]
    ):
        return f'<a href="{url}" target="_blank" rel="noopener noreferrer">{label}</a>'
    return label


def _render_inline_markdown(text: str) -> str:
    escaped = html.escape(text, quote=True).replace("\\$", "$")
    escaped = _LINK_RE.sub(_safe_link, escaped)
    escaped = _BOLD_RE.sub(r"<strong>\1</strong>", escaped)
    escaped = _ITALIC_RE.sub(r"<em>\1</em>", escaped)
    escaped = _PROSE_TEXTBF_RE.sub(r"<strong>\1</strong>", escaped)
    escaped = _PROSE_TEXTIT_RE.sub(r"<em>\1</em>", escaped)
    return escaped


_LEAN_DECL_KEYWORDS = frozenset({
    "theorem", "lemma", "def", "definition", "abbrev", "structure",
    "class", "instance", "inductive", "coinductive", "axiom", "constant",
    "opaque", "macro", "syntax", "elab",
})
_LEAN_KEYWORDS = _LEAN_DECL_KEYWORDS | frozenset({
    "example", "where", "with", "extends", "deriving", "import", "open",
    "section", "namespace", "end", "variable", "variables", "universe",
    "universes", "private", "protected", "noncomputable", "partial",
    "unsafe", "mutual", "by", "do", "let", "have", "show", "suffices",
    "from", "fun", "match", "if", "then", "else", "for", "in", "return",
    "calc", "obtain", "rcases", "rintro", "intro", "intros", "exact",
    "refine", "apply", "rw", "rwa", "erw", "simp", "simp_all", "dsimp",
    "simpa", "ring", "ring_nf", "linarith", "nlinarith", "omega",
    "positivity", "norm_num", "norm_cast", "push_cast", "assumption",
    "contradiction", "trivial", "rfl", "decide", "aesop", "tauto", "ext",
    "funext", "congr", "cases", "induction", "specialize", "generalize",
    "subst", "change", "unfold", "symm", "trans", "constructor", "left",
    "right", "use", "exfalso", "by_cases", "by_contra", "contrapose",
    "push_neg", "split", "case", "set_option", "attribute", "local",
    "scoped", "notation", "infixl", "infixr", "prefix", "postfix",
    "export", "hiding", "renaming", "rec", "using", "at", "only",
    "clear", "revert", "rename_i", "try", "repeat", "first", "all_goals",
    "any_goals", "focus", "skip", "done", "omega", "gcongr", "haveI",
    "letI", "set", "classical", "omega",
})
_LEAN_DOCTAGS = frozenset({"sorry", "admit"})
_LEAN_BUILT_INS = frozenset({
    "Type", "Prop", "Sort", "Nat", "Int", "Bool", "String", "Char",
    "Array", "List", "Option", "Prod", "Sum", "Sigma", "Subtype", "Fin",
    "UInt8", "UInt16", "UInt32", "UInt64", "USize", "Float", "IO", "Unit",
    "Empty", "True", "False", "Eq", "Ne", "And", "Or", "Not", "Iff",
    "Exists", "ℕ", "ℤ", "ℚ", "ℝ", "ℂ",
})
_LEAN_LITERALS = frozenset({"true", "false", "none", "some"})

_LEAN_NUM_RE = re.compile(r"(?:0[xX][0-9a-fA-F_]+|0[bB][01_]+|0[oO][0-7_]+|\d[\d_]*(?:\.\d[\d_]*)?)")
_LEAN_OP_RE = re.compile(
    r"(?::=|=>|->|<-|<->|\|->|<=|>=|/=|!=|<\||\|>|\+\+|::|"
    r"[→←↔↦∀∃λ∧∨¬≤≥≠∣∤∈∉⊆⊂⊇⊃∪∩×·∘∑∏⟨⟩▸⊢])"
)
_LEAN_IDENT_START = re.compile(r"[A-Za-z_\u03b1-\u03c9\u0391-\u03a9ℕℤℚℝℂ]")
_LEAN_IDENT_CONT = re.compile(r"[A-Za-z0-9_'\u2080-\u2089\u2070-\u2079\u207f\u1d62-\u1d6a\u03b1-\u03c9\u0391-\u03a9ℕℤℚℝℂ!?]")


def highlight_lean_lines(code: str) -> list[str]:
    """Syntax-highlight Lean 4 source into per-line HTML using `hljs-*` spans."""
    lines = code.split("\n")
    out_lines: list[str] = []
    block_depth = 0
    expect_title = False

    for line in lines:
        parts: list[str] = []
        i = 0
        n = len(line)
        while i < n:
            if block_depth > 0:
                start = i
                while i < n and block_depth > 0:
                    if line.startswith("/-", i):
                        block_depth += 1
                        i += 2
                    elif line.startswith("-/", i):
                        block_depth -= 1
                        i += 2
                    else:
                        i += 1
                parts.append(f'<span class="hljs-comment">{html.escape(line[start:i], quote=True)}</span>')
                continue

            if line.startswith("--", i):
                parts.append(f'<span class="hljs-comment">{html.escape(line[i:], quote=True)}</span>')
                i = n
                continue

            if line.startswith("/-", i):
                start = i
                block_depth = 1
                i += 2
                while i < n and block_depth > 0:
                    if line.startswith("/-", i):
                        block_depth += 1
                        i += 2
                    elif line.startswith("-/", i):
                        block_depth -= 1
                        i += 2
                    else:
                        i += 1
                parts.append(f'<span class="hljs-comment">{html.escape(line[start:i], quote=True)}</span>')
                continue

            if line.startswith("@[", i):
                start = i
                depth = 1
                i += 2
                while i < n and depth > 0:
                    if line[i] == "[":
                        depth += 1
                    elif line[i] == "]":
                        depth -= 1
                    i += 1
                parts.append(f'<span class="hljs-meta">{html.escape(line[start:i], quote=True)}</span>')
                continue

            if line[i] == "#" and i + 1 < n and (line[i + 1].isalpha() or line[i + 1] == "_"):
                end = i + 2
                while end < n and (line[end].isalnum() or line[end] == "_"):
                    end += 1
                parts.append(f'<span class="hljs-meta">{html.escape(line[i:end], quote=True)}</span>')
                i = end
                continue

            if line[i] == '"':
                start = i
                i += 1
                while i < n:
                    if line[i] == "\\" and i + 1 < n:
                        i += 2
                        continue
                    if line[i] == '"':
                        i += 1
                        break
                    i += 1
                parts.append(f'<span class="hljs-string">{html.escape(line[start:i], quote=True)}</span>')
                expect_title = False
                continue

            if line[i] == "'":
                char_m = re.match(r"'(?:\\.|[^'\\\n])'", line[i:])
                if char_m:
                    tok = char_m.group(0)
                    parts.append(f'<span class="hljs-string">{html.escape(tok, quote=True)}</span>')
                    i += len(tok)
                    expect_title = False
                    continue

            num_m = _LEAN_NUM_RE.match(line, i)
            if num_m:
                tok = num_m.group(0)
                parts.append(f'<span class="hljs-number">{html.escape(tok, quote=True)}</span>')
                i += len(tok)
                expect_title = False
                continue

            op_m = _LEAN_OP_RE.match(line, i)
            if op_m:
                tok = op_m.group(0)
                parts.append(f'<span class="hljs-operator">{html.escape(tok, quote=True)}</span>')
                i += len(tok)
                expect_title = False
                continue

            if _LEAN_IDENT_START.match(line[i]):
                end = i + 1
                if expect_title:
                    while end < n and (_LEAN_IDENT_CONT.match(line[end]) or line[end] == "."):
                        end += 1
                else:
                    while end < n and _LEAN_IDENT_CONT.match(line[end]):
                        end += 1
                word = line[i:end]
                esc = html.escape(word, quote=True)
                if expect_title:
                    parts.append(f'<span class="hljs-title">{esc}</span>')
                    expect_title = False
                elif word in _LEAN_DOCTAGS:
                    parts.append(f'<span class="hljs-doctag">{esc}</span>')
                elif word in _LEAN_KEYWORDS:
                    parts.append(f'<span class="hljs-keyword">{esc}</span>')
                    if word in _LEAN_DECL_KEYWORDS:
                        expect_title = True
                elif word in _LEAN_BUILT_INS:
                    parts.append(f'<span class="hljs-built_in">{esc}</span>')
                elif word in _LEAN_LITERALS:
                    parts.append(f'<span class="hljs-literal">{esc}</span>')
                else:
                    parts.append(esc)
                i = end
                continue

            ch = line[i]
            if not ch.isspace():
                expect_title = False
            parts.append(html.escape(ch, quote=True))
            i += 1
        out_lines.append("".join(parts))
    return out_lines


def highlight_lean_code(code: str) -> str:
    """Syntax-highlight a block of Lean 4 source code with `hljs-*` spans."""
    return "\n".join(highlight_lean_lines(code))


def render_markdown_latex(text: str) -> str:
    """Render Lean docstring Markdown + LaTeX (`$...$`, `$$...$$`) to safe HTML."""
    cleaned = text.replace("\x00", "").strip()
    if not cleaned:
        return ""

    tokens: list[str] = []

    def stash(replacement: str) -> str:
        idx = len(tokens)
        tokens.append(replacement)
        return f"\x00AXBT_TOK_{idx}\x00"

    def render_fence(match: re.Match[str]) -> str:
        lang = match.group(1).strip().lower()
        body = match.group(2).strip()
        inner = (
            highlight_lean_code(body)
            if lang in ("", "lean", "lean4")
            else html.escape(body, quote=True)
        )
        return stash(f'<pre class="md-code"><code>{inner}</code></pre>')

    working = _FENCE_RE.sub(render_fence, cleaned)
    working = _DISPLAY_DOLLAR_RE.sub(
        lambda m: stash(_render_latex_math(m.group(1), display=True)),
        working,
    )
    working = _DISPLAY_BRACKET_RE.sub(
        lambda m: stash(_render_latex_math(m.group(1), display=True)),
        working,
    )
    working = _DISPLAY_ENV_RE.sub(
        lambda m: stash(_render_latex_math(m.group(1), display=True)),
        working,
    )
    working = _INLINE_CODE_RE.sub(
        lambda m: stash(f'<code class="md-inline-code">{html.escape(m.group(1), quote=True)}</code>'),
        working,
    )
    working = _INLINE_PAREN_RE.sub(
        lambda m: stash(_render_latex_math(m.group(1), display=False)),
        working,
    )
    working = _INLINE_DOLLAR_RE.sub(
        lambda m: stash(_render_latex_math(m.group(1), display=False)),
        working,
    )
    working = _PROSE_TEXTTT_RE.sub(
        lambda m: stash(
            f'<code class="md-inline-code">{_unescape_latex_text(html.escape(m.group(1), quote=True))}</code>'
        ),
        working,
    )

    block_token_re = re.compile(r"^\x00AXBT_TOK_(\d+)\x00$")
    blocks: list[str] = []
    lines = working.splitlines()
    idx = 0
    while idx < len(lines):
        line = lines[idx]
        if not line.strip():
            idx += 1
            continue
        tok_m = block_token_re.match(line.strip())
        if tok_m and tokens[int(tok_m.group(1))].startswith(("<pre ", "<div ")):
            blocks.append(line.strip())
            idx += 1
            continue
        head_m = _HEADING_RE.match(line)
        if head_m:
            level = len(head_m.group(1))
            blocks.append(f"<h{level}>{_render_inline_markdown(head_m.group(2))}</h{level}>")
            idx += 1
            continue
        if _BQ_RE.match(line):
            quote_lines: list[str] = []
            while idx < len(lines) and (qm := _BQ_RE.match(lines[idx])):
                quote_lines.append(qm.group(1))
                idx += 1
            blocks.append(
                f"<blockquote><p>{_render_inline_markdown(' '.join(quote_lines))}</p></blockquote>"
            )
            continue
        if _UL_RE.match(line):
            items: list[str] = []
            while idx < len(lines) and (um := _UL_RE.match(lines[idx])):
                items.append(f"<li>{_render_inline_markdown(um.group(1))}</li>")
                idx += 1
            blocks.append(f"<ul>{''.join(items)}</ul>")
            continue
        if _OL_RE.match(line):
            items = []
            while idx < len(lines) and (om := _OL_RE.match(lines[idx])):
                items.append(f"<li>{_render_inline_markdown(om.group(1))}</li>")
                idx += 1
            blocks.append(f"<ol>{''.join(items)}</ol>")
            continue
        para_lines: list[str] = []
        while idx < len(lines):
            cur = lines[idx]
            if (
                not cur.strip()
                or _HEADING_RE.match(cur)
                or _BQ_RE.match(cur)
                or _UL_RE.match(cur)
                or _OL_RE.match(cur)
            ):
                break
            cur_tok = block_token_re.match(cur.strip())
            if cur_tok and tokens[int(cur_tok.group(1))].startswith(("<pre ", "<div ")):
                break
            para_lines.append(cur.strip())
            idx += 1
        if para_lines:
            blocks.append(f"<p>{_render_inline_markdown(' '.join(para_lines))}</p>")

    rendered = "\n".join(blocks)
    for tok_idx, tok_val in enumerate(tokens):
        rendered = rendered.replace(f"\x00AXBT_TOK_{tok_idx}\x00", tok_val)
    return rendered

#: Generated graph artifacts live in the cache alongside the payloads.
GRAPH_FILENAME = "graph.html"

#: The page's single external script from a CDN (pinned version; SRI
#: hash computed from the served bytes) — never bundled into axbt,
#: never fetched by it. All layout coordinates are computed
#: deterministically at build time in Python.
CYTOSCAPE_URL = "https://cdnjs.cloudflare.com/ajax/libs/cytoscape/3.31.0/cytoscape.min.js"
CYTOSCAPE_INTEGRITY = (
    "sha512-SRHUEtWi7EdmapdotitmlD7tNoeRXCtll4Y0yl2YYJB+m+IuIEvvHjZ7V34/k5ZFBtMN/"
    "uehjaerdJGr7hgt1g=="
)
KATEX_CSS_URL = "https://cdnjs.cloudflare.com/ajax/libs/KaTeX/0.16.9/katex.min.css"
KATEX_JS_URL = "https://cdnjs.cloudflare.com/ajax/libs/KaTeX/0.16.9/katex.min.js"

#: weakest -> strongest; containers roll up to the weakest constituent.
#: `done` ranks after `verified`: it is a never-verifiable kind's
#: terminal state (green), and a container with any kernel-pending
#: member still reads yellow.
_STATES = ["unchecked", "checked", "verified", "done"]
_EMPTY_STATE = "empty"

_LEGEND_TEXT = {
    "verified": "verified — has a kernel verification stamp",
    "checked": "checked — passed typecheck, awaiting kernel verification",
    "done": "done — checked clean, and this kind is never verifiable",
    "unchecked": "unchecked — never judged by a full, unstubbed check",
    _EMPTY_STATE: "empty — a file/module with no declarations extracted",
}

#: The red-asterisk marker for files whose source is new or changed.
_STAR = "\u2731"


def graph_path(project_root: Path) -> Path:
    """The default graph output path: `.axbt/graph.html`."""
    return project_root / CACHE_DIRNAME / GRAPH_FILENAME


def state_of(declaration: Any) -> str:
    """A declaration's pipeline state, keyed strictly on its stamps.

    Never-verifiable kinds (defs, instances, structures, ...) have no
    kernel tier: a clean check is their terminal state, recorded as
    `done` (green) rather than `checked` (yellow — reserved for
    declarations still awaiting kernel verification). Colors key only
    on the stamps, never inferred.
    """
    if declaration.verified_sig or declaration.verified_at:
        return "verified"
    if declaration.checked_sig or declaration.checked_at:
        return "checked" if declaration.kind in _VERIFIABLE_KINDS else "done"
    return "unchecked"


def rollup_state(states: list[str]) -> str:
    """The container state: the weakest constituent declaration's state.

    A declaration-free container is `empty` (grey): nothing was judged
    and nothing can be — not the same fact as "unchecked".
    """
    if not states:
        return _EMPTY_STATE
    return min(states, key=_STATES.index)


def rendered_nodes(
    manifest: Manifest, selected: list[ManifestNode]
) -> list[ManifestNode]:
    """The graph's file set: `selected` plus their full transitive
    dependency closure (the payload-closure walk, dependencies-first).

    `--select` reuses the selection machinery, so the rendered set of a
    declaration selection is its owning file (with all of its
    declarations) and every ancestor; a module selection is every file
    of the module and the union's ancestors.
    """
    rendered = closure_nodes(manifest, selected)
    return [rendered[name] for name in sorted(rendered)]


def _tooltip(title: str, lines: list[tuple[str, str]]) -> str:
    """A pre-escaped tooltip block for the page's JavaScript overlay.

    The title and every value pass through `html.escape` here, so the
    page can hand the result to `innerHTML` without any
    manifest-derived string ever touching HTML raw.
    """
    rows = "".join(
        f'<div class="row"><span class="k">{html.escape(key)}</span>'
        f"<code>{html.escape(value)}</code></div>"
        for key, value in lines
    )
    return f'<div class="tt">{html.escape(title)}</div><div class="rows">{rows}</div>'


#: Re-derive the declaration name from its node id (`decl:<file>:<name>`;
#: file stems and Lean names contain no colons).
def _decl_id_name(decl_id: str) -> str:
    return decl_id.removeprefix("decl:").rsplit(":", 1)[-1]


def _decl_counts_row(declarations: list[Any]) -> str:
    """The `3 verified, 2 checked, 1 unchecked` count line."""
    counts = {state: 0 for state in _STATES}
    for declaration in declarations:
        counts[state_of(declaration)] += 1
    return (
        f"{counts['verified']} verified, {counts['done']} done, "
        f"{counts['checked']} checked (unverified), "
        f"{counts['unchecked']} unchecked"
    )


def _status_text(node: ManifestNode) -> str:
    """The file's diff status with its marker if changed."""
    return f"{node.status} {_STAR}" if node.status in ("new", "changed") else node.status


#: Pill/badge and layered layout geometry constants (pixels).
_PILL_H = 28
_PILL_CHAR_W = 8
_PILL_PAD_X = 34
_PILL_MIN_W = 84

_DECL_ROW_STEP = 36      # 28px node height + 8px vertical gap
_SUBCOL_GAP = 18         # horizontal gap between sub-columns inside one file
_FILE_PAD_X = 20         # horizontal padding around declaration nodes in a file box
_FILE_PAD_Y = 20         # vertical padding around declaration nodes in a file box
_FILE_TITLE_H = 26       # vertical clearance above a file box for its title
_FILE_GAP_Y = 42         # vertical gap between stacked file boxes in a rank column
_RANK_GAP_X = 64         # horizontal gap between file rank columns within a module
_MODULE_PAD_X = 26       # horizontal padding inside a module box
_MODULE_GAP_X = 96       # horizontal gap between adjacent module boxes
_LAYOUT_TOP = 56
_MAX_MODULE_COLS = 4     # cap horizontal rank columns per module for balanced aspect ratio


def _pill_width(label: str) -> int:
    """Pixel width of a declaration pill/badge sized to enclose `label`."""
    return max(_PILL_MIN_W, len(label) * _PILL_CHAR_W + _PILL_PAD_X)


def _subcolumn_count(decl_count: int) -> int:
    """Number of side-by-side declaration sub-columns inside one file card."""
    if decl_count <= 10:
        return 1
    if decl_count <= 24:
        return 2
    if decl_count <= 45:
        return 3
    return 4


def _longest_paths(
    keys: Iterable[str],
    parents_of: Callable[[str], list[str]],
) -> dict[str, int]:
    """Compute longest-path depths iteratively, dropping cycle back-edges."""
    memo: dict[str, int] = {}
    visiting: set[str] = set()
    work: list[tuple[str, list[str] | None]] = []
    for start in keys:
        if start in memo:
            continue
        work.append((start, None))
        while work:
            node, parents = work.pop()
            if parents is not None:
                best = max((memo[p] for p in parents if p in memo), default=-1)
                memo[node] = 1 + best
                visiting.discard(node)
                continue
            if node in memo or node in visiting:
                continue
            visiting.add(node)
            node_parents = parents_of(node)
            work.append((node, node_parents))
            for parent in node_parents:
                if parent not in memo and parent not in visiting:
                    work.append((parent, None))
    return memo


def _order_file_declarations(declarations: list[Any]) -> list[Any]:
    """Order a file's declarations by intra-file dependency depth, then
    source line (`line_pos`), then name."""
    if not declarations:
        return []
    exact = {d.name: d.name for d in declarations}
    by_suffix: dict[str, list[str]] = {}
    for d in declarations:
        by_suffix.setdefault(d.name.rsplit(".", 1)[-1], []).append(d.name)

    intra_parents: dict[str, list[str]] = {}
    for d in declarations:
        parents: set[str] = set()
        for dep in d.dependencies:
            target = exact.get(dep)
            if target is None:
                candidates = by_suffix.get(dep.rsplit(".", 1)[-1], [])
                if len(candidates) == 1:
                    target = candidates[0]
            if target is not None and target != d.name:
                parents.add(target)
        intra_parents[d.name] = sorted(parents)

    ordered_keys = [
        d.name for d in sorted(declarations, key=lambda item: (item.line_pos, item.name))
    ]
    depths = _longest_paths(ordered_keys, lambda name: intra_parents[name])
    return sorted(
        declarations,
        key=lambda d: (depths.get(d.name, 0), d.line_pos, d.name),
    )


def _partition_module_columns(
    members: list[ManifestNode],
    intra_levels: dict[str, int],
    global_levels: dict[str, int],
) -> list[list[ManifestNode]]:
    """Arrange a module's files into left-to-right rank columns.

    When a module has up to `_MAX_MODULE_COLS` distinct intra-module
    dependency levels and each level has at most `_MAX_MODULE_COLS`
    files, every level gets its own dedicated rank column so intra-module
    chains and diamonds lay out directly left-to-right by rank. Larger
    modules wrap their level-ordered topological sequence into up to
    `_MAX_MODULE_COLS` balanced columns so wide or deep modules stay
    compact 2D grids while preserving topological order (every
    intra-module dependency lies strictly in an earlier column to the
    left or higher up in the same column).
    """
    if not members:
        return []
    ordered = sorted(
        members,
        key=lambda n: (intra_levels[n.name], global_levels[n.name], n.name),
    )
    by_rank: dict[int, list[ManifestNode]] = {}
    for node in ordered:
        by_rank.setdefault(intra_levels[node.name], []).append(node)
    ranks = [by_rank[r] for r in sorted(by_rank)]
    if len(ranks) <= _MAX_MODULE_COLS and all(
        len(group) <= _MAX_MODULE_COLS for group in ranks
    ):
        return ranks

    num_cols = min(_MAX_MODULE_COLS, max(2, len(ranks)))
    if len(ranks) == 1:
        num_cols = min(_MAX_MODULE_COLS, (len(ordered) + 3) // 4)
    col_size = (len(ordered) + num_cols - 1) // num_cols
    return [
        ordered[i : i + col_size]
        for i in range(0, len(ordered), col_size)
    ]


def _layout_positions(
    files: list[ManifestNode],
) -> tuple[dict[str, dict[str, int]], dict[str, dict[str, int]]]:
    """Deterministic 2D layered positions for modules, files, and declaration pills.

    Modules order left-to-right by dependency depth (breaking cross-module
    zig-zag cycles by minimum/average global file depth). Within each
    module, files spread left-to-right across rank columns by intra-module
    import depth and stack top-to-bottom within each rank column (ordered
    by parent Y-barycenter to reduce edge crossings). Inside each file,
    declaration pills order by `(intra_file_dep_depth, line_pos, name)`
    and wrap into balanced sub-columns with exact pill-width clearance so
    no two labels or boxes ever overlap.
    """
    by_name = {node.name: node for node in files}
    modules = sorted({node.module for node in files})

    global_file_levels = _longest_paths(
        sorted(by_name),
        lambda name: [p for p in sorted(by_name[name].parents) if p in by_name],
    )
    intra_file_levels = _longest_paths(
        sorted(by_name),
        lambda name: [
            p
            for p in sorted(by_name[name].parents)
            if p in by_name and by_name[p].module == by_name[name].module
        ],
    )

    # Module rank key from global file depths breaks cross-module zig-zag
    # import cycles in the natural upstream-to-downstream direction.
    mod_depth_key: dict[str, tuple[int, float, str]] = {}
    for module in modules:
        levels = [global_file_levels[n.name] for n in files if n.module == module]
        mod_depth_key[module] = (
            min(levels, default=0),
            sum(levels) / max(1, len(levels)),
            module,
        )

    module_parents: dict[str, set[str]] = {module: set() for module in modules}
    for node in files:
        for parent in node.parents:
            if parent in by_name and by_name[parent].module != node.module:
                module_parents[node.module].add(by_name[parent].module)

    ordered_modules_seed = sorted(modules, key=lambda m: mod_depth_key[m])
    module_levels = _longest_paths(
        ordered_modules_seed,
        lambda module: sorted(
            (
                p
                for p in module_parents[module]
                if module not in module_parents.get(p, set())
                or mod_depth_key[p] < mod_depth_key[module]
            ),
            key=lambda p: mod_depth_key[p],
        ),
    )

    positions: dict[str, dict[str, int]] = {}
    cells: dict[str, dict[str, int]] = {}
    file_center_y: dict[str, float] = {}

    cur_x = 0
    for module in sorted(
        modules, key=lambda name: (module_levels[name], mod_depth_key[name], name)
    ):
        module_start_x = cur_x
        module_members = [node for node in files if node.module == module]
        columns = _partition_module_columns(
            module_members, intra_file_levels, global_file_levels
        )

        col_x = module_start_x
        for col_index, col_nodes in enumerate(columns):
            if col_index > 0:
                # Re-sort same-rank members within the column by the Y
                # barycenter of their already-placed parent files.
                def _barycenter_key(
                    node: ManifestNode,
                ) -> tuple[int, int, int, float, str]:
                    placed = [
                        file_center_y[p]
                        for p in node.parents
                        if p in file_center_y
                    ]
                    bary = sum(placed) / len(placed) if placed else 0.0
                    return (
                        intra_file_levels[node.name],
                        global_file_levels[node.name],
                        0 if placed else 1,
                        bary,
                        node.name,
                    )

                col_nodes = sorted(col_nodes, key=_barycenter_key)

            y = _LAYOUT_TOP
            col_max_w = 0
            for member in col_nodes:
                ordered_decls = _order_file_declarations(member.declarations)
                title_w = len(dotted_stem_of(member)) * 8 + 36
                if not ordered_decls:
                    box_w = max(104, title_w)
                    box_h = _FILE_TITLE_H + 30 + _FILE_PAD_Y
                    cx = col_x + box_w // 2
                    cy = y + _FILE_TITLE_H + 15
                    positions[f"file:{member.name}"] = {"x": cx, "y": cy}
                    cells[f"file:{member.name}"] = {
                        "x1": col_x,
                        "y1": y,
                        "x2": col_x + box_w,
                        "y2": y + box_h,
                    }
                    file_center_y[member.name] = float(cy)
                    col_max_w = max(col_max_w, box_w)
                    y += box_h + _FILE_GAP_Y
                    continue

                num_subcols = _subcolumn_count(len(ordered_decls))
                rows_per_col = (len(ordered_decls) + num_subcols - 1) // num_subcols
                subcols = [
                    ordered_decls[i : i + rows_per_col]
                    for i in range(0, len(ordered_decls), rows_per_col)
                ]
                sc_widths = [
                    max(_pill_width(bare_name(d)) for d in sc) for sc in subcols
                ]
                pills_w = sum(sc_widths) + _SUBCOL_GAP * (len(subcols) - 1)
                max_rows = max(len(sc) for sc in subcols)
                pills_h = (max_rows - 1) * _DECL_ROW_STEP + _PILL_H
                box_w = max(pills_w + 2 * _FILE_PAD_X, title_w)
                box_h = _FILE_TITLE_H + pills_h + 2 * _FILE_PAD_Y

                first_subcol_left = col_x + (box_w - pills_w) // 2
                first_pill_cy = y + _FILE_TITLE_H + _FILE_PAD_Y + _PILL_H // 2

                subcol_left = first_subcol_left
                for sc, sc_w in zip(subcols, sc_widths):
                    pill_cx = subcol_left + sc_w // 2
                    for row_idx, decl in enumerate(sc):
                        pill_cy = first_pill_cy + row_idx * _DECL_ROW_STEP
                        positions[f"decl:{member.name}:{decl.name}"] = {
                            "x": pill_cx,
                            "y": pill_cy,
                        }
                    subcol_left += sc_w + _SUBCOL_GAP

                file_cx = col_x + box_w // 2
                file_cy = y + _FILE_TITLE_H + _FILE_PAD_Y + pills_h // 2
                positions[f"file:{member.name}"] = {"x": file_cx, "y": first_pill_cy}
                cells[f"file:{member.name}"] = {
                    "x1": col_x,
                    "y1": y,
                    "x2": col_x + box_w,
                    "y2": y + box_h,
                }
                file_center_y[member.name] = float(file_cy)
                col_max_w = max(col_max_w, box_w)
                y += box_h + _FILE_GAP_Y

            col_x += col_max_w + _RANK_GAP_X

        positions[f"module:{module}"] = {
            "x": module_start_x + _FILE_PAD_X,
            "y": _LAYOUT_TOP,
        }
        cur_x = max(col_x - _RANK_GAP_X, module_start_x) + _MODULE_PAD_X * 2 + _MODULE_GAP_X

    return positions, cells


def _indirect_ancestors_map(files: list[ManifestNode]) -> dict[str, set[str]]:
    """For each file, the set of ancestor files reachable in >= 2 import hops."""
    by_name = {node.name: node for node in files}
    direct_ancestors: dict[str, set[str]] = {}
    for node in files:
        visited: set[str] = set()
        stack = [p for p in node.parents if p in by_name]
        while stack:
            curr = stack.pop()
            if curr in visited:
                continue
            visited.add(curr)
            for gp in by_name[curr].parents:
                if gp in by_name and gp not in visited:
                    stack.append(gp)
        direct_ancestors[node.name] = visited

    indirect: dict[str, set[str]] = {}
    for node in files:
        ind: set[str] = set()
        for parent in node.parents:
            if parent in direct_ancestors:
                ind |= direct_ancestors[parent]
        indirect[node.name] = ind
    return indirect


def _effective_decl_states(
    files: list[ManifestNode],
) -> dict[tuple[str, str], str]:
    """Compute each declaration's state, treating non-verifiable kinds
    (defs, structures, instances, ...) as `done` (green) when they have
    been checked either directly (`checked_sig`) or as part of verifying
    a theorem in the same file or a downstream dependent declaration.

    `axbt verify` only stamps `verified_sig` on theorems/lemmas/examples,
    even though Lean's kernel elaborates and checks every definition and
    structure in the verified payload. Marking non-verifiable
    declarations in verified files (or depended on by verified/checked
    declarations) as `done` ensures verified files with definitions render
    green rather than orange.
    """
    raw_states: dict[tuple[str, str], str] = {}
    judged_deps: set[str] = set()
    file_has_verified: dict[str, bool] = {}

    for node in files:
        has_ver = any(
            bool(d.verified_sig or d.verified_at) for d in node.declarations
        )
        file_has_verified[node.name] = has_ver
        for decl in node.declarations:
            st = state_of(decl)
            raw_states[(node.name, decl.name)] = st
            if st in ("verified", "checked", "done"):
                for dep in decl.dependencies:
                    judged_deps.add(dep)
                    judged_deps.add(dep.rsplit(".", 1)[-1])

    effective: dict[tuple[str, str], str] = {}
    for node in files:
        for decl in node.declarations:
            st = raw_states[(node.name, decl.name)]
            if (
                st == "unchecked"
                and decl.kind not in _VERIFIABLE_KINDS
                and not decl.is_sorry
                and (
                    file_has_verified[node.name]
                    or decl.name in judged_deps
                    or decl.name.rsplit(".", 1)[-1] in judged_deps
                )
            ):
                st = "done"
            effective[(node.name, decl.name)] = st
    return effective


def _decl_counts_row_from_states(states: list[str]) -> str:
    """The `3 verified, 2 done, 1 checked, 0 unchecked` count line."""
    counts = {state: 0 for state in _STATES}
    for st in states:
        counts[st] += 1
    return (
        f"{counts['verified']} verified, {counts['done']} done, "
        f"{counts['checked']} checked (unverified), "
        f"{counts['unchecked']} unchecked"
    )


def build_graph_data(
    manifest: Manifest,
    files: list[ManifestNode],
    project_root: Path | None = None,
) -> dict[str, Any]:
    """Assemble the graph's data: compound nodes, edges, and counts.

    `files` is the rendered file set (expected: `rendered_nodes`' output
    — every member's dependency closure, so import edges' endpoints and
    the declaration dependencies' hosts are all present).
    """
    files = sorted(files, key=lambda node: node.name)
    modules = sorted({node.module for node in files})
    files_of_module: dict[str, list[ManifestNode]] = {module: [] for module in modules}

    root = (
        project_root
        if project_root is not None
        else (_active_project_root if _active_project_root is not None else Path.cwd())
    )

    edges: list[dict[str, Any]] = []
    edges_seen: set[tuple[str, str, str]] = set()
    effective_states = _effective_decl_states(files)

    # --- declare per-file data ------------------------------------------
    # Compounds must exist before their children in the elements list
    # (Cytoscape resolves containment), so the nodes list is assembled
    # modules-first: per-file data is computed below, then emitted.
    module_states: dict[str, list[str]] = {module: [] for module in modules}
    file_states_by_name: dict[str, list[str]] = {}
    file_nodes: list[dict[str, Any]] = []
    decl_nodes: list[dict[str, Any]] = []
    for node in files:
        files_of_module[node.module].append(node)
        file_members = _order_file_declarations(node.declarations)
        states = [effective_states[(node.name, decl.name)] for decl in file_members]
        file_states_by_name[node.name] = states
        module_states[node.module].extend(states)
        changed = node.status in ("new", "changed")
        file_label = dotted_stem_of(node) + (" " + _STAR if changed else "")
        decl_summary = _decl_counts_row_from_states(states)

        try:
            raw_source = (root / node.path).read_text(encoding="utf-8")
        except OSError:
            raw_source = ""
        file_doc, decl_sources = _extract_file_and_decl_sources(
            raw_source, node.declarations
        )
        file_doc_html = render_markdown_latex(file_doc)

        file_nodes.append(
            {
                "group": "file",
                "id": f"file:{node.name}",
                "label": file_label,
                "parent": f"module:{node.module}",
                "state": rollup_state(states),
                "changed": changed,
                "width": max(104, len(file_label) * 8 + 28),
                "path": node.path,
                "module": node.module,
                "status_text": _status_text(node),
                "decl_summary": decl_summary,
                "doc": file_doc,
                "doc_html": file_doc_html,
                "code": raw_source,
                "tooltip": _tooltip(
                    node.path,
                    [
                        ("module", node.module),
                        ("status", _status_text(node)),
                        ("md5", node.md5),
                        ("declarations", decl_summary),
                    ],
                ),
            }
        )
        file_verified_req_id = next(
            (d.verified_request_id for d in file_members if d.verified_request_id),
            None,
        )
        for decl in file_members:
            label = bare_name(decl)
            decl_state = effective_states[(node.name, decl.name)]
            checked_str = _stamp_row(
                decl.checked_sig, decl.checked_at, decl.checked_request_id
            )
            verified_str = _stamp_row(
                decl.verified_sig, decl.verified_at, decl.verified_request_id
            )
            if checked_str == "—" and decl_state == "done":
                checked_str = "checked in verified closure"
            decl_doc, decl_code, code_start_line = decl_sources.get(
                decl.name, ("", decl.signature or "", decl.line_pos)
            )
            if not decl_code:
                decl_code = decl.signature or ""
            decl_doc_html = render_markdown_latex(decl_doc)
            decl_nodes.append(
                {
                    "group": "declaration",
                    "id": f"decl:{node.name}:{decl.name}",
                    "label": label,
                    "full_name": decl.name,
                    "parent": f"file:{node.name}",
                    "module": node.module,
                    "state": decl_state,
                    "changed": changed,
                    "width": _pill_width(label),
                    # Shapes split by verifiability (see the template's
                    # style sheet): verifiable proof kinds render as
                    # ovals (ellipse), never-verifiable declarations
                    # (defs, instances, structures, ...) as solid
                    # sharp-cornered rectangles.
                    "kind": decl.kind,
                    "file_path": f"{node.path}:{decl.line_pos}",
                    "lines": f"{decl.line_pos}-{decl.end_line_pos}",
                    "is_sorry": decl.is_sorry,
                    "signature": decl.signature or "",
                    "doc": decl_doc,
                    "doc_html": decl_doc_html,
                    "code": decl_code,
                    "code_start_line": code_start_line,
                    "checked_sig": decl.checked_sig,
                    "checked_request_id": decl.checked_request_id,
                    "verified_sig": decl.verified_sig,
                    "verified_request_id": decl.verified_request_id,
                    "closure_verified_request_id": (
                        file_verified_req_id
                        if (decl_state == "done" and not decl.checked_request_id)
                        else None
                    ),
                    "checked_stamp": checked_str,
                    "verified_stamp": verified_str,
                    "external_deps": list(decl.external_dependencies),
                    "tooltip": _tooltip(
                        decl.name,
                        [
                            ("kind", decl.kind),
                            ("file", f"{node.path}:{decl.line_pos}"),
                            ("lines", f"{decl.line_pos}-{decl.end_line_pos}"),
                            ("sorry", "yes" if decl.is_sorry else "no"),
                            ("checked stamp", checked_str),
                            ("verified stamp", verified_str),
                        ],
                    ),
                }
            )

    # --- module compound nodes (their members' states are now known) ----
    module_nodes = [
        {
            "group": "module",
            "id": f"module:{module}",
            "label": module,
            "parent": None,
            "state": rollup_state(module_states[module]),
            "changed": False,
            "tooltip": _tooltip(
                module,
                [
                    (
                        dotted_stem_of(member),
                        f"{_status_text(member)}; {_decl_counts_row_from_states(file_states_by_name[member.name])}",
                    )
                    for member in files_of_module[module]
                ],
            ),
        }
        for module in modules
    ]
    #: Cytoscape requires compound parents to precede their children.
    nodes = [*module_nodes, *file_nodes, *decl_nodes]
    positions, cells = _layout_positions(files)
    for node in nodes:
        node["position"] = positions[node["id"]]
        if node["group"] == "file":
            node["cell"] = cells[node["id"]]

    # --- file-level import edges ----------------------------------------
    file_names = {node.name for node in files}
    indirect_ancestors = _indirect_ancestors_map(files)
    for node in files:
        for parent in sorted(node.parents):
            # Both endpoints are always in the rendered set (the closure
            # walk pulled every dependency in); the check is for direct
            # callers passing narrower file lists.
            if parent in file_names:
                key = (f"file:{parent}", f"file:{node.name}", "import")
                if key not in edges_seen:
                    edges_seen.add(key)
                    is_transitive = parent in indirect_ancestors.get(node.name, set())
                    edges.append(
                        {
                            "id": f"import:{parent}->{node.name}",
                            "source": key[0],
                            "target": key[1],
                            "kind": "import",
                            "transitive": is_transitive,
                            "tooltip": _tooltip(
                                "transitive import" if is_transitive else "import",
                                [("from", parent), ("into", node.name)],
                            ),
                        }
                    )

    # --- declaration-to-declaration edges --------------------------------
    # From the extraction dependency lists (the outcome-record work):
    # dependency -> dependent. Only edges resolving to exactly one
    # rendered declaration (by full name, then by unique bare-name
    # suffix) are drawn — ambiguous or external names are skipped,
    # never guessed.
    exact_ids: dict[str, list[str]] = {}
    suffix_ids: dict[str, list[str]] = {}
    for node in files:
        for decl in node.declarations:
            node_id = f"decl:{node.name}:{decl.name}"
            exact_ids.setdefault(decl.name, []).append(node_id)
            suffix_ids.setdefault(decl.name.rsplit(".", 1)[-1], []).append(node_id)

    for node in files:
        for decl in node.declarations:
            target = f"decl:{node.name}:{decl.name}"
            for dep in decl.dependencies:
                candidates = exact_ids.get(dep) or suffix_ids.get(
                    dep.rsplit(".", 1)[-1], []
                )
                if len(candidates) != 1 or candidates[0] == target:
                    continue
                key = (candidates[0], target, "depends")
                if key in edges_seen:
                    continue
                edges_seen.add(key)
                source_name = _decl_id_name(key[0])
                target_name = _decl_id_name(key[1])
                edges.append(
                    {
                        "id": f"dep:{key[0]}->{key[1]}",
                        "source": key[0],
                        "target": key[1],
                        "kind": "depends",
                        "transitive": False,
                        "tooltip": _tooltip(
                            "depends on",
                            [("declaration", source_name), ("used by", target_name)],
                        ),
                    }
                )

    declarations_total = sum(len(node.declarations) for node in files)
    return {
        "nodes": nodes,
        "edges": edges,
        "star": _STAR,
        "legend": [
            {"state": state, "text": _LEGEND_TEXT[state]}
            for state in (*_STATES, _EMPTY_STATE)
        ],
        "counts": {
            "modules": len(modules),
            "files": len(files),
            "declarations": declarations_total,
            "edges": len(edges),
        },
    }


def _stamp_row(sig: str | None, at: Any, request_id: str | None) -> str:
    """One stamp tier rendered for a tooltip (`—` when absent)."""
    if sig is None and at is None:
        return "—"
    parts = []
    if sig is not None:
        parts.append(sig[:8])
    if at is not None:
        parts.append(at.isoformat(timespec="seconds"))
    if request_id is not None:
        parts.append(f"request {request_id}")
    return "; ".join(parts)


def _embed(data: dict[str, Any]) -> str:
    """JSON-serialize `data` for safe embedding into a script tag.

    `<` and `>` are escaped to their `\\u003c`/`\\u003e` JSON escapes:
    the text stays exactly recoverable via `JSON.parse(textContent)`
    while incapable of forming a `</script>` (or any tag) anywhere in
    the page. Manifest-derived strings reach tooltip HTML only through
    `html.escape` (see `_tooltip`).
    """
    return json.dumps(data, ensure_ascii=True).replace("<", "\\u003c").replace(">", "\\u003e")


#: Compact drawer chrome: resizer handle, header controls, search bar with
#: live autocomplete, quick edge toggles, and the inspector container.
def _legend_markup(
    legend: list[dict[str, str]],
    star: str,
    counts: dict[str, int] | None = None,
) -> str:
    del legend, star
    header_meta = (
        f'<span class="sidebar-counts">{counts["files"]} files &middot; '
        f'{counts["declarations"]} decls</span>'
        if counts
        else ""
    )
    header = (
        '<div class="sidebar-head">'
        '<div class="sidebar-title-wrap">'
        '<span class="sidebar-brand">axbt graph</span>'
        f"{header_meta}"
        "</div>"
        '<div class="sidebar-actions">'
        '<button type="button" class="insp-btn" id="toggle-dock" data-action="toggle-dock">Side drawer</button>'
        '<button type="button" class="insp-btn" id="toggle-full" data-action="toggle-full">Full</button>'
        '<button type="button" class="insp-btn" id="toggle-drawer" data-action="toggle-drawer">Collapse</button>'
        "</div>"
        "</div>"
    )
    search = (
        '<div class="search-wrap">'
        '<div class="search-box">'
        '<input type="search" id="search-nodes" placeholder="Search file, declaration, sig, or doc…" autocomplete="off">'
        '<span id="search-count" class="search-count"></span>'
        "</div>"
        '<div id="search-autocomplete" class="search-ac" style="display:none;"></div>'
        "</div>"
    )
    controls = (
        '<div class="drawer-controls">'
        '<label class="ctrl-pill" title="declaration dependency arrows (tick to show; clicking a declaration always reveals its dependency neighborhood)">'
        '<input type="checkbox" id="toggle-decl-edges"> decl arrows</label>'
        '<label class="ctrl-pill" title="transitive file import arrows (tick to show shortcut imports alongside direct DAG edges)">'
        '<input type="checkbox" id="toggle-transitive-edges"> transitive imports</label>'
        '<button type="button" class="insp-btn" id="reset-positions">reset layout</button>'
        "</div>"
    )
    return (
        '<div id="drawer-resizer" class="drawer-resizer" title="Drag to resize drawer (double-click to toggle full page)"></div>'
        '<div class="drawer-top">'
        f"{header}{search}{controls}"
        "</div>"
        '<div class="drawer-body" id="drawer-body">'
        '<div id="inspector" style="display:none;"></div>'
        "</div>"
    )


def _render_html(data: dict[str, Any], title: str) -> str:
    """Render the single-file HTML from prebuilt graph data."""
    counts = data["counts"]
    page_title = (
        f"{html.escape(title)} — {counts['files']} files, "
        f"{counts['declarations']} declarations, {counts['edges']} edges"
    )
    replacements = {
        "__AXBT_TITLE__": page_title,
        "__AXBT_LEGEND__": _legend_markup(data["legend"], data["star"], counts),
        "__AXBT_DATA__": _embed(data),
        "__AXBT_CDN__": CYTOSCAPE_URL,
        "__AXBT_INTEGRITY__": CYTOSCAPE_INTEGRITY,
        "__AXBT_KATEX_CSS__": KATEX_CSS_URL,
        "__AXBT_KATEX_JS__": KATEX_JS_URL,
    }
    page = _HTML_TEMPLATE
    for token, value in replacements.items():
        page = page.replace(token, value)
    return page


def graph_html(manifest: Manifest, files: list[ManifestNode], title: str = "axbt graph") -> str:
    """Render the single-file HTML (Cytoscape.js from the pinned CDN)."""
    return _render_html(build_graph_data(manifest, files), title)


def write_graph(
    manifest: Manifest,
    project_root: Path,
    files: list[ManifestNode],
    output: Path | None = None,
    title: str = "axbt graph",
) -> tuple[Path, dict[str, int]]:
    """Render and write the graph HTML, returning (path, counts).

    Counts are the graph's node/edge tallies for the command's report.
    `output=None` defaults to `.axbt/graph.html`; an explicit path is
    honored as given (parents are created as needed).
    """
    global _active_project_root
    out = output if output is not None else graph_path(project_root)
    out.parent.mkdir(parents=True, exist_ok=True)
    prev_root = _active_project_root
    _active_project_root = project_root
    try:
        data = build_graph_data(manifest, files)
    finally:
        _active_project_root = prev_root
    out.write_text(_render_html(data, title), encoding="utf-8")
    return out, data["counts"]


# --- The page template ---------------------------------------------------
# Plain string with token placeholders (no f-string): the HTML/CSS/JS
# braces are content, and the only interpolated pieces are the escaped
# title, legend, and the `_embed`ed JSON. The embedded data cannot
# contain any `<`, so it can neither break out of its script tag nor
# collide with the placeholder tokens.
_HTML_TEMPLATE = """<!doctype html>
<html>
<head>
<meta charset="utf-8">
<title>__AXBT_TITLE__</title>
<link rel="stylesheet" href="__AXBT_KATEX_CSS__" crossorigin="anonymous">
<script src="__AXBT_CDN__" integrity="__AXBT_INTEGRITY__" crossorigin="anonymous"></script>
<script src="__AXBT_KATEX_JS__" crossorigin="anonymous"></script>
<style>
  :root { --serif-font: "Source Serif 4", "Source Serif Pro", "Iowan Old Style", "Charter", "Palatino Linotype", Georgia, ui-serif, serif; }
  body { margin: 0; height: 100vh; font-family: var(--serif-font); background: #0b101b; color: #dbe7f8; font-size: 14.5px; }
  #graph { position: fixed; inset: 0; }
  #legend { position: fixed; z-index: 30; background: rgba(15, 23, 42, 0.96);
            border: 1px solid #263859; padding: 12px 16px 14px; font-family: var(--serif-font);
            font-size: 14.5px; line-height: 1.65;
            box-shadow: 0 12px 36px rgba(0, 0, 0, 0.56); backdrop-filter: blur(8px);
            box-sizing: border-box; overflow-y: auto; }
  #legend.dock-side { top: 0; right: 0; bottom: 0; width: 420px; max-width: 100vw;
                      border-right: none; border-top: none; border-bottom: none; border-radius: 12px 0 0 12px; }
  #legend.dock-side.has-selection { width: 480px; }
  #legend.dock-bottom { left: 0; right: 0; bottom: 0; max-height: 48vh;
                        border-left: none; border-right: none; border-bottom: none; border-radius: 12px 12px 0 0; }
  #legend.dock-bottom .drawer-body { display: block; }
  #legend.full { top: 0 !important; right: 0 !important; bottom: 0 !important; left: 0 !important;
                 width: 100vw !important; height: 100vh !important; max-width: 100vw !important;
                 max-height: 100vh !important; border-radius: 0 !important; }
  #legend.collapsed { overflow: hidden; }
  #legend.dock-side.collapsed { bottom: auto; width: 360px !important; border-bottom: 1px solid #263859; border-radius: 0 0 0 12px; }
  #legend.dock-bottom.collapsed { height: auto !important; max-height: none !important; }
  #legend.collapsed .search-wrap,
  #legend.collapsed .drawer-controls,
  #legend.collapsed .drawer-body,
  #legend.collapsed .drawer-resizer { display: none; }
  .drawer-resizer { position: absolute; z-index: 4; background: transparent; transition: background .15s; }
  .drawer-resizer:hover, #legend.resizing .drawer-resizer { background: rgba(56, 189, 248, 0.35); }
  #legend.dock-side > .drawer-resizer { cursor: ew-resize; width: 8px; top: 0; bottom: 0; left: 0; }
  #legend.dock-bottom > .drawer-resizer { cursor: ns-resize; height: 8px; top: 0; left: 0; right: 0; }
  #legend .sidebar-head { display: flex; align-items: center; justify-content: space-between; gap: 8px; margin-bottom: 8px; }
  #legend .sidebar-title-wrap { display: flex; align-items: baseline; gap: 8px; flex-wrap: wrap; }
  #legend .sidebar-brand { font-weight: 700; font-size: 17px; color: #f8fafc; letter-spacing: .01em; }
  #legend .sidebar-counts { font-size: 12.5px; color: #8aa0c4; font-family: ui-monospace, monospace; }
  #legend .sidebar-actions { display: flex; align-items: center; gap: 5px; flex-shrink: 0; }
  #legend .search-wrap { position: relative; margin-bottom: 7px; }
  #legend .search-box { position: relative; display: flex; align-items: center; }
  #legend input[type="search"] { width: 100%; box-sizing: border-box; padding: 7px 78px 7px 10px; font-size: 14px;
                                 font-family: var(--serif-font); border: 1px solid #2e4369; border-radius: 6px;
                                 background: #131d31; color: #e6f0ff; outline: none; }
  #legend input[type="search"]::placeholder { color: #6e84a8; }
  #legend input[type="search"]:focus { border-color: #38bdf8; box-shadow: 0 0 0 2px rgba(56, 189, 248, 0.2); }
  #legend .search-count { position: absolute; right: 8px; font-size: 12px; color: #7dd3fc; pointer-events: none; font-family: ui-sans-serif, system-ui, sans-serif; }
  .search-ac { margin-top: 5px; max-height: 280px; overflow-y: auto; background: #0c1424;
               border: 1px solid #2e4369; border-radius: 7px; box-shadow: 0 8px 20px rgba(0, 0, 0, 0.45); }
  .ac-item { padding: 7px 10px; cursor: pointer; border-bottom: 1px solid #1b2a44; line-height: 1.4; }
  .ac-item:last-child { border-bottom: none; }
  .ac-item:hover, .ac-item.active { background: #182946; }
  .ac-top { display: flex; align-items: center; justify-content: space-between; gap: 6px; }
  .ac-name { font-family: ui-monospace, monospace; font-size: 13px; font-weight: 600; color: #f0f6fc; overflow-wrap: anywhere; }
  .ac-name mark { background: rgba(56, 189, 248, 0.28); color: #bae6fd; border-radius: 2px; padding: 0 1px; }
  .ac-kind { font-size: 11px; text-transform: uppercase; letter-spacing: .04em; color: #8aa2c8;
             font-family: ui-sans-serif, system-ui, sans-serif; background: #16233b; border: 1px solid #2a3e63;
             border-radius: 4px; padding: 0 5px; flex-shrink: 0; }
  .ac-meta { font-size: 12px; color: #7e95ba; margin-top: 2px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  .ac-preview { font-size: 13px; color: #a5b8d4; margin-top: 2px; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  .ac-empty { padding: 9px 11px; font-size: 13px; color: #8499bc; }
  #legend .drawer-controls { display: flex; flex-wrap: wrap; align-items: center; gap: 6px; margin-top: 2px; }
  #legend .ctrl-pill { display: inline-flex; align-items: center; gap: 5px; font: 500 12.5px/1.35 ui-sans-serif, system-ui, sans-serif;
                       color: #b8cae4; background: #131d31; border: 1px solid #283b5e; border-radius: 5px;
                       padding: 3px 8px; cursor: pointer; user-select: none; }
  #legend .ctrl-pill:hover { border-color: #38bdf8; color: #f0f6fc; }
  #legend .ctrl-pill input { margin: 0; accent-color: #38bdf8; }
  #legend .drawer-controls #reset-positions { margin-left: auto; }
  #legend .star { color: #ff6b6b; }
  .chip { display: inline-block; width: 12px; height: 12px; border-radius: 3px; margin-right: 7px; vertical-align: -.5px; flex-shrink: 0; }
  .chip.verified { background: #20c997; }
  .chip.done { background: #22b8cf; }
  .chip.checked { background: #f59f00; }
  .chip.unchecked { background: #ff6b35; }
  .chip.empty { background: #5c7099; }
  #legend .insp-btn { font: 500 12.5px/1.4 ui-sans-serif, system-ui, sans-serif; color: #cbd8ec;
                      background: #16233b; border: 1px solid #2e4369; border-radius: 5px;
                      padding: 3px 9px; cursor: pointer; white-space: nowrap; }
  #legend .insp-btn:hover { border-color: #38bdf8; color: #ffffff; background: #1d3254; }
  #legend .insp-btn.active { border-color: #38bdf8; background: #163a5c; color: #bae6fd; }
  #inspector { border-top: 1px solid #263859; margin-top: 10px; padding-top: 12px; font-size: 14.5px; line-height: 1.65; }
  #inspector .insp-head { display: flex; align-items: flex-start; justify-content: space-between; gap: 8px; }
  #inspector .insp-title { font-weight: 700; font-family: ui-monospace, monospace; font-size: 15.5px;
                           color: #f8fafc; overflow-wrap: anywhere; margin-bottom: 4px; }
  #inspector .insp-actions { display: flex; align-items: center; gap: 4px; flex-shrink: 0; }
  #inspector .insp-meta { color: #94a9c9; font-size: 13px; margin-bottom: 6px; }
  #inspector .insp-stamps { font-size: 12.5px; color: #7e95ba; margin-bottom: 8px; }
  #inspector .stamp-link { color: #7dd3fc; text-decoration: underline; text-underline-offset: 2px; font-family: ui-monospace, monospace; font-size: 12px; }
  #inspector .stamp-link:hover { color: #bae6fd; }
  #inspector .insp-doc { font-family: var(--serif-font); background: #0c1424; border: 1px solid #223250; border-left: 3px solid #38bdf8;
                         border-radius: 6px; padding: 10px 13px; margin: 8px 0; color: #e2ecf8; font-size: 15.5px; line-height: 1.7; }
  #inspector .insp-doc h1, #inspector .insp-doc h2, #inspector .insp-doc h3, #inspector .insp-doc h4 {
    margin: 4px 0 6px; color: #f8fafc; font-weight: 700; line-height: 1.35; }
  #inspector .insp-doc h1 { font-size: 18.5px; }
  #inspector .insp-doc h2 { font-size: 17px; }
  #inspector .insp-doc h3, #inspector .insp-doc h4 { font-size: 15.5px; }
  #inspector .insp-doc p { margin: 0 0 8px; }
  #inspector .insp-doc p:last-child { margin-bottom: 0; }
  #inspector .insp-doc ul, #inspector .insp-doc ol { margin: 4px 0 8px 20px; padding: 0; }
  #inspector .insp-doc blockquote { margin: 4px 0 8px; padding: 4px 10px; border-left: 2px solid #4f6d9a; color: #b8cae4; background: rgba(30, 48, 80, 0.35); }
  #inspector .insp-doc a { color: #7dd3fc; }
  #inspector .md-inline-code { font-family: ui-monospace, monospace; font-size: 13px; background: #16233b;
                               border: 1px solid #263859; border-radius: 4px; padding: 0 5px; color: #bae6fd; }
  #inspector pre.md-code { background: #080d17; border: 1px solid #233454; border-radius: 6px; padding: 8px 10px;
                           margin: 6px 0; overflow-x: auto; font-family: ui-monospace, monospace; font-size: 12.5px; color: #cbd8ec; }
  .math-inline { font-family: "KaTeX_Main", "Cambria Math", "STIX Two Math", Georgia, serif; color: #e0f2fe; padding: 0 1px; }
  .math-display { font-family: "KaTeX_Main", "Cambria Math", "STIX Two Math", Georgia, serif; color: #e0f2fe;
                  text-align: center; padding: 8px 10px; margin: 6px 0; background: #09101e;
                  border: 1px solid #1e2f4d; border-radius: 5px; overflow-x: auto; font-size: 15.5px; }
  .math-display .katex-display { margin: 0; }
  #inspector .katex { color: #e0f2fe; font-size: 1.05em; }
  #inspector details.insp-subgraph-view { margin: 8px 0; }
  #inspector details.insp-subgraph-view > summary { cursor: pointer; user-select: none; }
  #subgraph-canvas { height: 320px; margin-top: 6px; background: #080d17; border: 1px solid #233454; border-radius: 6px; }
  #legend.full #subgraph-canvas { height: 60vh; }
  #inspector .insp-hint { font-size: 12px; color: #7e95ba; margin-top: 4px; }
  #inspector .insp-subgraph-bar { display: flex; flex-wrap: wrap; gap: 6px; margin: 8px 0 4px; }
  #inspector .sg-pill { font-size: 12.5px; font-weight: 600; padding: 2px 9px; border-radius: 999px; border: 1px solid transparent; }
  #inspector .sg-pill.upstream { color: #bae6fd; background: rgba(56, 189, 248, 0.14); border-color: rgba(125, 211, 252, 0.4); }
  #inspector .sg-pill.downstream { color: #fbcfe8; background: rgba(244, 114, 182, 0.14); border-color: rgba(249, 168, 212, 0.4); }
  #inspector pre.insp-sig { background: #090e19; border: 1px solid #233454; border-radius: 6px;
                            padding: 8px 10px; margin: 6px 0; font-family: ui-monospace, monospace;
                            color: #bae6fd; font-size: 12.5px; white-space: pre-wrap; overflow-wrap: anywhere;
                            max-height: 140px; overflow-y: auto; }
  #inspector .insp-code-head { display: flex; align-items: center; justify-content: space-between; margin-top: 8px; }
  #inspector pre.insp-code { background: #080d17; border: 1px solid #233454; border-radius: 6px;
                             padding: 8px 0; margin: 5px 0; font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
                             color: #dbe7f8; font-size: 12.5px; line-height: 1.5; overflow: auto; max-height: 280px; }
  #legend.full #inspector pre.insp-code { max-height: 55vh; }
  #inspector .code-line { display: block; padding: 0 10px 0 0; white-space: pre; }
  #inspector .line-num { display: inline-block; min-width: 36px; padding: 0 8px 0 6px; margin-right: 8px;
                         text-align: right; color: #54698d; border-right: 1px solid #1b2a44; user-select: none; }
  #inspector details.insp-file-code { margin-top: 8px; }
  #inspector details.insp-file-code > summary { cursor: pointer; user-select: none; }
  .hljs-keyword { color: #c084fc; font-weight: 600; }
  .hljs-title { color: #60a5fa; font-weight: 600; }
  .hljs-built_in { color: #38bdf8; }
  .hljs-literal { color: #fb923c; }
  .hljs-number { color: #f472b6; }
  .hljs-string { color: #4ade80; }
  .hljs-comment { color: #64748b; font-style: italic; }
  .hljs-meta { color: #facc15; }
  .hljs-doctag { color: #f87171; font-weight: 700; }
  .hljs-operator { color: #94a3b8; }
  #inspector .insp-sec { font-weight: 600; color: #8499bc; margin-top: 8px; font-size: 12px; font-family: ui-sans-serif, system-ui, sans-serif;
                         text-transform: uppercase; letter-spacing: .04em; }
  #inspector .insp-sec.upstream { color: #7dd3fc; }
  #inspector .insp-sec.downstream { color: #f9a8d4; }
  #inspector .insp-mod-groups { display: flex; flex-direction: column; gap: 6px; margin-top: 4px; }
  #inspector .insp-mod-group { display: flex; flex-wrap: wrap; align-items: center; gap: 5px 6px; padding: 5px 8px;
                               background: rgba(12, 20, 36, 0.72); border: 1px solid #1e2f4d; border-radius: 6px; }
  #inspector .insp-mod-label { font-family: ui-sans-serif, system-ui, sans-serif; font-size: 11px; font-weight: 700;
                               color: #94a9c9; background: #16233b; border: 1px solid #2a3e63; border-radius: 4px;
                               padding: 1px 6px; letter-spacing: .02em; flex-shrink: 0; }
  #inspector .insp-mod-group .insp-chips { margin-top: 0; }
  #inspector .insp-chips { display: flex; flex-wrap: wrap; gap: 5px; margin-top: 4px; }
  #inspector .insp-chip { font-family: ui-monospace, monospace; font-size: 12.5px; background: #16233b;
                          border: 1px solid #2d436b; border-radius: 4px; padding: 2px 8px; cursor: pointer; color: #d0def2; }
  #inspector .insp-chip:hover { background: #1d3557; border-color: #38bdf8; color: #7dd3fc; }
  #inspector .insp-chip.upstream { border-color: rgba(125, 211, 252, 0.45); color: #bae6fd; }
  #inspector .insp-chip.upstream:hover { background: #163052; border-color: #7dd3fc; color: #e0f2fe; }
  #inspector .insp-chip.downstream { border-color: rgba(249, 168, 212, 0.45); color: #fbcfe8; }
  #inspector .insp-chip.downstream:hover { background: #3b1c36; border-color: #f9a8d4; color: #fce7f3; }
  #inspector .insp-chip.transitive { border-style: dashed; opacity: 0.88; }
  #inspector .insp-ext { font-family: ui-monospace, monospace; font-size: 12px; color: #8499bc;
                         background: #10192b; border: 1px solid #223250; border-radius: 4px; padding: 1px 6px; }
  @media (max-width: 820px) {
    #legend.dock-side:not(.full), #legend.dock-side.has-selection:not(.full), #legend.dock-bottom:not(.full) {
      left: 0; right: 0; top: auto; bottom: 0; width: auto; max-width: none; max-height: 52vh; border-radius: 12px 12px 0 0; }
  }
  #tooltip { position: fixed; z-index: 8; display: none; max-width: 420px; background: #0f172a;
             border: 1px solid #2e4369; border-radius: 8px; padding: 9px 12px; font-family: var(--serif-font);
             font-size: 13.5px; line-height: 1.6; color: #e2ecf8; box-shadow: 0 8px 24px rgba(0, 0, 0, 0.6); pointer-events: none; }
  #tooltip .tt { font-weight: 600; margin-bottom: 4px; overflow-wrap: anywhere; font-family: ui-monospace, monospace; color: #f8fafc; font-size: 13.5px; }
  #tooltip .row { overflow-wrap: anywhere; }
  #tooltip .k { color: #7e95ba; display: inline-block; min-width: 96px; margin-right: 6px; }
  #tooltip code { font-family: ui-monospace, monospace; font-size: 12.5px; color: #bae6fd; }
</style>
</head>
<body>
<div id="graph"></div>
<div id="tooltip"></div>
<div id="legend" class="drawer dock-bottom">
__AXBT_LEGEND__
</div>
<script type="application/json" id="graph-data">__AXBT_DATA__</script>
<script>
(function () {
  "use strict";
  var payload = JSON.parse(document.getElementById("graph-data").textContent);
  var tooltip = document.getElementById("tooltip");
  var inspector = document.getElementById("inspector");

  var cy = window.cytoscape({
    container: document.getElementById("graph"),
    boxSelectionEnabled: false,
    wheelSensitivity: 0.22,
    elements: payload.nodes
      .map(function (node) {
        return { data: node, classes: node.state, position: node.position };
      })
      .concat(
        payload.edges.map(function (edge) {
          var cls = edge.kind + (edge.transitive ? " transitive" : "");
          return { data: edge, classes: cls };
        })
      ),
    style: [
      { selector: "node", style: {
        label: "data(label)", "font-size": 11, "text-valign": "center", "text-halign": "center",
        color: "#e6f0ff", "font-family": "ui-sans-serif, system-ui, sans-serif", shape: "ellipse" } },
      { selector: "node[group='declaration']", style: {
        width: "data(width)", height: 28, "font-size": 11,
        "font-family": "ui-monospace, SFMono-Regular, Menlo, monospace",
        "text-valign": "center", "text-halign": "center",
        "border-style": "solid",
        shape: "rectangle" } },
      { selector: "node[kind='theorem'], node[kind='lemma'], node[kind='example']", style: {
        "border-style": "solid",
        shape: "ellipse" } },
      { selector: "node[group='file']", style: {
        shape: "roundrectangle", width: "data(width)", height: 28, "font-size": 12, "font-weight": 600 } },
      { selector: "node[state='verified']", style: {
        "background-color": "#0e3a2f", "border-color": "#20c997", "border-width": 1.8, color: "#d3f9d8" } },
      { selector: "node[state='done']", style: {
        "background-color": "#0c324a", "border-color": "#22b8cf", "border-width": 2, color: "#c5f6fa" } },
      { selector: "node[state='checked']", style: {
        "background-color": "#3b2a0a", "border-color": "#f59f00", "border-width": 1.8, color: "#ffec99" } },
      { selector: "node[state='unchecked']", style: {
        "background-color": "#3d1a11", "border-color": "#ff6b35", "border-width": 1.8, color: "#ffd8a8" } },
      { selector: "node[state='empty']", style: {
        "background-color": "#19253a", "border-color": "#5c7099", "border-width": 1.4, color: "#a5b8d4" } },
      { selector: "edge", style: {
        width: 1.5, "curve-style": "bezier", "line-color": "#4f6d9a", "target-arrow-color": "#4f6d9a",
        "target-arrow-shape": "triangle", "arrow-scale": 0.75, opacity: 0.84 } },
      { selector: "edge.transitive", style: {
        width: 1.1, "line-style": "dotted", opacity: 0.42 } },
      { selector: "edge[kind='depends']", style: {
        "line-color": "#60a5fa", "target-arrow-color": "#60a5fa", "line-style": "dashed", width: 1.4 } },
      { selector: "node:parent", style: {
        shape: "roundrectangle", "font-size": 12, "font-weight": 600, color: "#d0def2",
        "background-color": "#131d31", "background-opacity": 0.6, "border-color": "#2b3e63", "border-width": 1.3,
        padding: "16px",
        "text-valign": "top", "text-halign": "center", "text-margin-y": -6,
        "text-background-color": "#0b101b", "text-background-opacity": 0.9,
        "text-background-padding": "3px", "text-background-shape": "roundrectangle" } },
      { selector: "node:parent[group='module']", style: {
        "font-size": 14, "font-weight": 700, color: "#e6f0ff", padding: "24px", "text-margin-y": -8,
        "background-color": "#111a2e", "background-opacity": 0.5, "border-color": "#314873", "border-width": 1.6 } },
      { selector: "node:parent[group='file'][state='verified'], node:parent[group='file'][state='done']", style: {
        "background-color": "#0c2b26", "background-opacity": 0.45, "border-color": "#1aa179", "border-width": 1.5 } },
      { selector: "node:parent[group='file'][state='checked']", style: {
        "background-color": "#2e230a", "background-opacity": 0.45, "border-color": "#d99b16", "border-width": 1.5 } },
      { selector: "node:parent[group='file'][state='unchecked']", style: {
        "background-color": "#301610", "background-opacity": 0.45, "border-color": "#e8590c", "border-width": 1.5 } },
      { selector: "node:parent[group='file'][state='empty']", style: {
        "background-color": "#162136", "background-opacity": 0.45, "border-color": "#4a5f85" } },
      { selector: ".highlighted", style: { "border-color": "#38bdf8", "border-width": 2.5 } },
      { selector: "node.upstream", style: { "border-color": "#7dd3fc", "border-width": 2.6 } },
      { selector: "node.downstream", style: { "border-color": "#f9a8d4", "border-width": 2.6 } },
      { selector: ".selected-node", style: { "border-color": "#f8fafc", "border-width": 3 } },
      { selector: "edge.highlighted", style: { width: 2.4, "line-color": "#38bdf8", "target-arrow-color": "#38bdf8", opacity: 1 } },
      { selector: "edge.upstream", style: { width: 2.5, "line-color": "#7dd3fc", "target-arrow-color": "#7dd3fc", opacity: 1 } },
      { selector: "edge.downstream", style: { width: 2.5, "line-color": "#f9a8d4", "target-arrow-color": "#f9a8d4", opacity: 1 } },
      { selector: ".dimmed", style: { opacity: 0.2 } },
      { selector: "edge.hidden", style: { display: "none" } }
    ],
    layout: {
      // All coordinates are computed deterministically at build time
      // (2D layered rank columns + multi-column pill grids).
      name: "preset", padding: 40, fit: true
    }
  });

  // Copy initial preset positions so reset restores the exact build-time layout.
  var initialPositions = {};
  cy.nodes().forEach(function (node) {
    if (!node.isParent()) {
      initialPositions[node.id()] = { x: node.position("x"), y: node.position("y") };
    }
  });

  function spreadFileClusters() {
    // Layout is deterministic at build time; retained as a no-op hook
    // called by the reset button before restoring preset coordinates.
  }

  // -- interaction state -------------------------------------------------
  var marked = [];
  var currentTarget = null;
  var subgraphOpen = false;
  var subgraphCy = null;
  var dockMode = "bottom";
  var drawerCollapsed = false;
  var drawerFull = false;
  var customSideWidth = null;
  var customBottomHeight = null;
  var hasSelection = false;
  var acMatches = [];
  var activeAcIndex = -1;
  var drawer = document.getElementById("legend");
  var drawerResizer = document.getElementById("drawer-resizer");
  var toggleDockBtn = document.getElementById("toggle-dock");
  var toggleFullBtn = document.getElementById("toggle-full");
  var toggleDrawerBtn = document.getElementById("toggle-drawer");
  var declToggle = document.getElementById("toggle-decl-edges");
  var transToggle = document.getElementById("toggle-transitive-edges");
  var searchInput = document.getElementById("search-nodes");
  var searchCount = document.getElementById("search-count");
  var searchAutocomplete = document.getElementById("search-autocomplete");
  var depsHidden = declToggle ? !declToggle.checked : true;
  var transHidden = transToggle ? !transToggle.checked : true;

  function updateDrawerChrome() {
    var isFull = drawerFull && !drawerCollapsed;
    if (drawer) {
      drawer.className =
        "drawer " +
        (dockMode === "bottom" ? "dock-bottom" : "dock-side") +
        (hasSelection ? " has-selection" : "") +
        (isFull ? " full" : "") +
        (drawerCollapsed ? " collapsed" : "");
      if (isFull || drawerCollapsed) {
        drawer.style.width = "";
        drawer.style.height = "";
        drawer.style.maxHeight = "";
      } else if (dockMode === "side") {
        drawer.style.height = "";
        drawer.style.maxHeight = "";
        drawer.style.width = customSideWidth !== null ? customSideWidth + "px" : "";
      } else {
        drawer.style.width = "";
        if (customBottomHeight !== null) {
          drawer.style.height = customBottomHeight + "px";
          drawer.style.maxHeight = "100vh";
        } else {
          drawer.style.height = "";
          drawer.style.maxHeight = "";
        }
      }
    }
    if (toggleDockBtn) {
      toggleDockBtn.textContent = dockMode === "bottom" ? "Side drawer" : "Bottom drawer";
    }
    if (toggleFullBtn) {
      toggleFullBtn.textContent = isFull ? "Restore" : "Full";
      toggleFullBtn.className = "insp-btn" + (isFull ? " active" : "");
    }
    if (toggleDrawerBtn) {
      toggleDrawerBtn.textContent = drawerCollapsed ? "Expand" : "Collapse";
    }
  }

  function refreshEdgeVisibility() {
    cy.batch(function () {
      cy.edges('[kind = "depends"]').forEach(function (edge) {
        var revealed = marked.indexOf(edge) !== -1;
        edge.toggleClass("hidden", depsHidden && !revealed);
      });
      cy.edges('edge.transitive').forEach(function (edge) {
        var revealed = marked.indexOf(edge) !== -1;
        edge.toggleClass("hidden", transHidden && !revealed);
      });
    });
  }

  function hideAutocomplete() {
    activeAcIndex = -1;
    if (searchAutocomplete) {
      searchAutocomplete.style.display = "none";
      searchAutocomplete.innerHTML = "";
    }
  }

  function clearMark(keepSelection) {
    if (!keepSelection) {
      destroySubgraphView();
      currentTarget = null;
      hasSelection = false;
    }
    cy.batch(function () {
      cy.elements().removeClass("highlighted upstream downstream selected-node dimmed");
    });
    marked = [];
    if (!keepSelection && inspector) {
      inspector.style.display = "none";
      inspector.innerHTML = "";
      updateDrawerChrome();
    }
    refreshEdgeVisibility();
  }

  function transitiveCone(seed, edgeKind) {
    var upNodes = {};
    var upEdges = [];
    var upEdgeSeen = {};
    upNodes[seed.id()] = seed;

    // Upstream walk (predecessors along edgeKind)
    var upQueue = [seed];
    while (upQueue.length > 0) {
      var curr = upQueue.pop();
      curr.incomers('edge[kind = "' + edgeKind + '"]').forEach(function (edge) {
        if (!upEdgeSeen[edge.id()]) {
          upEdgeSeen[edge.id()] = true;
          upEdges.push(edge);
        }
        var src = edge.source();
        if (!upNodes[src.id()]) {
          upNodes[src.id()] = src;
          upQueue.push(src);
        }
      });
    }

    var downNodes = {};
    var downEdges = [];
    var downEdgeSeen = {};
    downNodes[seed.id()] = seed;

    // Downstream walk (successors along edgeKind)
    var downQueue = [seed];
    while (downQueue.length > 0) {
      var currDown = downQueue.pop();
      currDown.outgoers('edge[kind = "' + edgeKind + '"]').forEach(function (edge) {
        if (!downEdgeSeen[edge.id()]) {
          downEdgeSeen[edge.id()] = true;
          downEdges.push(edge);
        }
        var tgt = edge.target();
        if (!downNodes[tgt.id()]) {
          downNodes[tgt.id()] = tgt;
          downQueue.push(tgt);
        }
      });
    }

    var upstream = [];
    Object.keys(upNodes).forEach(function (id) {
      if (id !== seed.id()) { upstream.push(upNodes[id]); }
    });
    for (var i = 0; i < upEdges.length; i++) { upstream.push(upEdges[i]); }

    var downstream = [];
    Object.keys(downNodes).forEach(function (id) {
      if (id !== seed.id()) { downstream.push(downNodes[id]); }
    });
    for (var j = 0; j < downEdges.length; j++) { downstream.push(downEdges[j]); }

    var all = [seed].concat(upstream, downstream);
    return { upstream: upstream, downstream: downstream, all: all };
  }

  function escapeHtml(str) {
    return String(str == null ? "" : str)
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;")
      .replace(/"/g, "&quot;")
      .replace(/'/g, "&#39;");
  }

  function makeWordSet(wordsStr) {
    var set = {};
    var parts = wordsStr.split(" ");
    for (var i = 0; i < parts.length; i++) {
      if (parts[i]) { set[parts[i]] = true; }
    }
    return set;
  }

  var LEAN_DECL_KW = makeWordSet(
    "theorem lemma def definition abbrev structure class instance inductive coinductive axiom constant opaque macro syntax elab"
  );
  var LEAN_KW = makeWordSet(
    "theorem lemma def definition abbrev structure class instance inductive coinductive axiom constant opaque macro syntax elab " +
    "example where with extends deriving import open section namespace end variable variables universe universes private protected " +
    "noncomputable partial unsafe mutual by do let have show suffices from fun match if then else for in return calc obtain rcases " +
    "rintro intro intros exact refine apply rw rwa erw simp simp_all dsimp simpa ring ring_nf linarith nlinarith omega positivity " +
    "norm_num norm_cast push_cast assumption contradiction trivial rfl decide aesop tauto ext funext congr cases induction specialize " +
    "generalize subst change unfold symm trans constructor left right use exfalso by_cases by_contra contrapose push_neg split case " +
    "set_option attribute local scoped notation infixl infixr prefix postfix export hiding renaming rec using at only clear revert " +
    "rename_i try repeat first all_goals any_goals focus skip done gcongr haveI letI set classical"
  );
  var LEAN_DOCTAGS = makeWordSet("sorry admit");
  var LEAN_BUILT_INS = makeWordSet(
    "Type Prop Sort Nat Int Bool String Char Array List Option Prod Sum Sigma Subtype Fin " +
    "UInt8 UInt16 UInt32 UInt64 USize Float IO Unit Empty True False Eq Ne And Or Not Iff Exists " +
    "ℕ ℤ ℚ ℝ ℂ"
  );
  var LEAN_LITERALS = makeWordSet("true false none some");
  var LEAN_NUM_RE = /^(?:0[xX][0-9a-fA-F_]+|0[bB][01_]+|0[oO][0-7_]+|\\d[\\d_]*(?:\\.\\d[\\d_]*)?)/;
  var LEAN_OP_RE = /^(?::=|=>|->|<-|<->|\\|->|<=|>=|\\/=|!=|<\\||\\|>|\\+\\+|::|[→←↔↦∀∃λ∧∨¬≤≥≠∣∤∈∉⊆⊂⊇⊃∪∩×·∘∑∏⟨⟩▸⊢])/;
  var LEAN_IDENT_START = /^[A-Za-z_α-ωΑ-Ωℕℤℚℝℂ]/;
  var LEAN_IDENT_CONT = /^[A-Za-z0-9_'₀-₉⁰-⁹ⁿᵢ-ᵥα-ωΑ-Ωℕℤℚℝℂ!?]/;
  var LEAN_CHAR_RE = /^'(?:\\\\.|[^'\\\\\\n])'/;

  function highlightLeanLines(codeText) {
    var lines = String(codeText || "").split("\\n");
    var out = [];
    var blockDepth = 0;
    var expectTitle = false;

    for (var li = 0; li < lines.length; li++) {
      var line = lines[li];
      var parts = [];
      var i = 0;
      var n = line.length;
      while (i < n) {
        if (blockDepth > 0) {
          var cStart = i;
          while (i < n && blockDepth > 0) {
            if (line.slice(i, i + 2) === "/-") { blockDepth++; i += 2; }
            else if (line.slice(i, i + 2) === "-/") { blockDepth--; i += 2; }
            else { i++; }
          }
          parts.push('<span class="hljs-comment">' + escapeHtml(line.slice(cStart, i)) + '</span>');
          continue;
        }
        if (line.slice(i, i + 2) === "--") {
          parts.push('<span class="hljs-comment">' + escapeHtml(line.slice(i)) + '</span>');
          i = n;
          continue;
        }
        if (line.slice(i, i + 2) === "/-") {
          var bStart = i;
          blockDepth = 1;
          i += 2;
          while (i < n && blockDepth > 0) {
            if (line.slice(i, i + 2) === "/-") { blockDepth++; i += 2; }
            else if (line.slice(i, i + 2) === "-/") { blockDepth--; i += 2; }
            else { i++; }
          }
          parts.push('<span class="hljs-comment">' + escapeHtml(line.slice(bStart, i)) + '</span>');
          continue;
        }
        if (line.slice(i, i + 2) === "@[") {
          var aStart = i;
          var aDepth = 1;
          i += 2;
          while (i < n && aDepth > 0) {
            if (line[i] === "[") { aDepth++; }
            else if (line[i] === "]") { aDepth--; }
            i++;
          }
          parts.push('<span class="hljs-meta">' + escapeHtml(line.slice(aStart, i)) + '</span>');
          continue;
        }
        if (line[i] === "#" && i + 1 < n && /[A-Za-z_]/.test(line[i + 1])) {
          var mEnd = i + 2;
          while (mEnd < n && /[A-Za-z0-9_]/.test(line[mEnd])) { mEnd++; }
          parts.push('<span class="hljs-meta">' + escapeHtml(line.slice(i, mEnd)) + '</span>');
          i = mEnd;
          continue;
        }
        if (line[i] === '"') {
          var sStart = i;
          i++;
          while (i < n) {
            if (line[i] === "\\\\" && i + 1 < n) { i += 2; continue; }
            if (line[i] === '"') { i++; break; }
            i++;
          }
          parts.push('<span class="hljs-string">' + escapeHtml(line.slice(sStart, i)) + '</span>');
          expectTitle = false;
          continue;
        }
        if (line[i] === "'") {
          var chMatch = LEAN_CHAR_RE.exec(line.slice(i));
          if (chMatch) {
            parts.push('<span class="hljs-string">' + escapeHtml(chMatch[0]) + '</span>');
            i += chMatch[0].length;
            expectTitle = false;
            continue;
          }
        }
        var rest = line.slice(i);
        var numMatch = LEAN_NUM_RE.exec(rest);
        if (numMatch) {
          parts.push('<span class="hljs-number">' + escapeHtml(numMatch[0]) + '</span>');
          i += numMatch[0].length;
          expectTitle = false;
          continue;
        }
        var opMatch = LEAN_OP_RE.exec(rest);
        if (opMatch) {
          parts.push('<span class="hljs-operator">' + escapeHtml(opMatch[0]) + '</span>');
          i += opMatch[0].length;
          expectTitle = false;
          continue;
        }
        if (LEAN_IDENT_START.test(line[i])) {
          var idEnd = i + 1;
          while (idEnd < n && (LEAN_IDENT_CONT.test(line[idEnd]) || (expectTitle && line[idEnd] === "."))) {
            idEnd++;
          }
          var word = line.slice(i, idEnd);
          var escWord = escapeHtml(word);
          if (expectTitle) {
            parts.push('<span class="hljs-title">' + escWord + '</span>');
            expectTitle = false;
          } else if (LEAN_DOCTAGS[word]) {
            parts.push('<span class="hljs-doctag">' + escWord + '</span>');
          } else if (LEAN_KW[word]) {
            parts.push('<span class="hljs-keyword">' + escWord + '</span>');
            if (LEAN_DECL_KW[word]) { expectTitle = true; }
          } else if (LEAN_BUILT_INS[word]) {
            parts.push('<span class="hljs-built_in">' + escWord + '</span>');
          } else if (LEAN_LITERALS[word]) {
            parts.push('<span class="hljs-literal">' + escWord + '</span>');
          } else {
            parts.push(escWord);
          }
          i = idEnd;
          continue;
        }
        var ch = line[i];
        if (!/\\s/.test(ch)) { expectTitle = false; }
        parts.push(escapeHtml(ch));
        i++;
      }
      out.push(parts.join(""));
    }
    return out;
  }

  function highlightLeanInline(codeText) {
    return highlightLeanLines(codeText).join("\\n");
  }

  function renderCodeBlock(codeText, startLine) {
    var lines = highlightLeanLines(codeText);
    var base = typeof startLine === "number" && startLine > 0 ? startLine : 1;
    var rows = [];
    for (var i = 0; i < lines.length; i++) {
      rows.push(
        '<span class="code-line"><span class="line-num">' + (base + i) + '</span>' +
        lines[i] + '</span>'
      );
    }
    return '<pre class="insp-code">' + rows.join("") + '</pre>';
  }

  function nodeModuleOf(u) {
    var mod = u && u.data ? u.data("module") : "";
    if (mod) { return String(mod); }
    var parentId = u && u.data ? (u.data("parent") || "") : "";
    if (parentId.indexOf("file:") === 0) {
      var fileNode = cy.getElementById(parentId);
      if (fileNode && fileNode.length > 0 && fileNode.data("module")) {
        return String(fileNode.data("module"));
      }
      var raw = parentId.slice(5);
      var dotIdx = raw.indexOf(".");
      return dotIdx === -1 ? raw : raw.slice(0, dotIdx);
    }
    if (parentId.indexOf("module:") === 0) { return parentId.slice(7); }
    return "Other";
  }

  function appendChipGroup(htmlParts, title, cls, nodes, extraClass) {
    if (!nodes || nodes.length === 0) { return; }
    var secCls = cls === "upstream" ? "insp-sec upstream" : (cls === "downstream" ? "insp-sec downstream" : "insp-sec");
    var chipBase = cls === "upstream" ? "insp-chip upstream" : (cls === "downstream" ? "insp-chip downstream" : "insp-chip");
    var chipCls = chipBase + (extraClass ? " " + extraClass : "");
    var byModule = {};
    var modNames = [];
    for (var i = 0; i < nodes.length; i++) {
      var u = nodes[i];
      var mod = nodeModuleOf(u);
      if (!byModule[mod]) {
        byModule[mod] = [];
        modNames.push(mod);
      }
      byModule[mod].push(u);
    }
    modNames.sort();
    htmlParts.push('<div class="' + secCls + '">' + escapeHtml(title) + ' (' + nodes.length + ')</div><div class="insp-mod-groups">');
    for (var m = 0; m < modNames.length; m++) {
      var modName = modNames[m];
      var modNodes = byModule[modName];
      htmlParts.push(
        '<div class="insp-mod-group"><span class="insp-mod-label">' +
        escapeHtml(modName) + '</span><div class="insp-chips">'
      );
      for (var k = 0; k < modNodes.length; k++) {
        var item = modNodes[k];
        htmlParts.push(
          '<span class="' + chipCls + '" data-target-id="' + escapeHtml(item.id()) + '">' +
          escapeHtml(item.data("label")) + '</span>'
        );
      }
      htmlParts.push('</div></div>');
    }
    htmlParts.push('</div>');
  }

  function splitDirectAndTransitive(seed, edgeKind, cone) {
    var directUp = [];
    var directUpIds = {};
    seed.incomers('edge[kind = "' + edgeKind + '"]').sources().forEach(function (u) {
      if (!directUpIds[u.id()]) { directUpIds[u.id()] = true; directUp.push(u); }
    });
    var directDown = [];
    var directDownIds = {};
    seed.outgoers('edge[kind = "' + edgeKind + '"]').targets().forEach(function (dn) {
      if (!directDownIds[dn.id()]) { directDownIds[dn.id()] = true; directDown.push(dn); }
    });
    var transUp = [];
    for (var i = 0; i < cone.upstream.length; i++) {
      var upEl = cone.upstream[i];
      if (upEl.isNode && upEl.isNode() && !directUpIds[upEl.id()]) { transUp.push(upEl); }
    }
    var transDown = [];
    for (var j = 0; j < cone.downstream.length; j++) {
      var dnEl = cone.downstream[j];
      if (dnEl.isNode && dnEl.isNode() && !directDownIds[dnEl.id()]) { transDown.push(dnEl); }
    }
    return { directUp: directUp, transUp: transUp, directDown: directDown, transDown: transDown };
  }

  function axleShareUrl(route, reqId) {
    return "https:" + "//axle.axiommath.ai/" + route + "#r=" + encodeURIComponent(reqId);
  }

  function renderStampValue(stampText, route, reqId) {
    if (reqId) {
      return (
        '<a class="stamp-link" href="' + escapeHtml(axleShareUrl(route, reqId)) +
        '" target="_blank" rel="noopener noreferrer">' + escapeHtml(stampText) + ' &#8599;</a>'
      );
    }
    return escapeHtml(stampText);
  }

  function renderMathIn(container) {
    if (!container || !container.querySelectorAll) { return; }
    if (typeof window === "undefined" || !window.katex || typeof window.katex.render !== "function") { return; }
    var nodes = container.querySelectorAll("[data-latex]");
    for (var i = 0; i < nodes.length; i++) {
      var el = nodes[i];
      var tex = el.getAttribute("data-latex") || "";
      var isDisplay = el.className && el.className.indexOf("math-display") !== -1;
      try {
        window.katex.render(tex, el, {
          displayMode: isDisplay,
          throwOnError: false,
          strict: false,
          trust: false
        });
      } catch (_e) {
        el.textContent = tex;
      }
    }
  }

  // -- "View subgraph": a fresh canvas holding only the selected cone, laid
  // out on demand (layered, left to right) instead of the global layout.
  function subgraphNodes() {
    var out = [];
    for (var i = 0; i < marked.length; i++) {
      var el = marked[i];
      if (el.isNode && el.isNode() && !el.isParent() &&
          (el.data("group") === "declaration" || el.data("group") === "file")) {
        out.push(el);
      }
    }
    return out;
  }

  function subgraphSectionHtml() {
    var count = subgraphNodes().length;
    if (count < 2) { return ""; }
    return (
      '<details class="insp-subgraph-view"' + (subgraphOpen ? ' open' : '') + '>' +
      '<summary class="insp-sec">View subgraph (' + count + ' nodes)</summary>' +
      '<div id="subgraph-canvas"></div>' +
      '<div class="insp-hint">Fresh layout of the selected cone only. Click a node to select it in the main graph.</div>' +
      '</details>'
    );
  }

  function destroySubgraphView() {
    if (subgraphCy) {
      try { subgraphCy.destroy(); } catch (_e) { /* already gone */ }
      subgraphCy = null;
    }
  }

  function layeredPositions(nodes, edges) {
    var ids = nodes.map(function (n) { return n.id; });
    var rank = {};
    var preds = {};
    var succs = {};
    ids.forEach(function (id) { rank[id] = 0; preds[id] = []; succs[id] = []; });
    edges.forEach(function (e) {
      if (e.source === e.target) { return; }
      preds[e.target].push(e.source);
      succs[e.source].push(e.target);
    });
    for (var pass = 0; pass < ids.length; pass++) {
      var changed = false;
      edges.forEach(function (e) {
        if (e.source !== e.target && rank[e.target] < rank[e.source] + 1 && rank[e.source] < ids.length) {
          rank[e.target] = rank[e.source] + 1;
          changed = true;
        }
      });
      if (!changed) { break; }
    }
    var layers = [];
    var byId = {};
    nodes.forEach(function (n) {
      byId[n.id] = n;
      var r = Math.min(rank[n.id], ids.length);
      while (layers.length <= r) { layers.push([]); }
      layers[r].push(n.id);
    });
    layers = layers.filter(function (l) { return l.length > 0; });
    layers.forEach(function (l) {
      l.sort(function (a, b) { return String(byId[a].label).localeCompare(String(byId[b].label)); });
    });
    var order = {};
    function reindex() { layers.forEach(function (l) { l.forEach(function (id, i) { order[id] = i; }); }); }
    function sweep(layer, nbrs) {
      var bary = {};
      layer.forEach(function (id) {
        var ns = nbrs[id];
        if (ns.length === 0) { bary[id] = order[id]; return; }
        var sum = 0;
        ns.forEach(function (n) { sum += order[n]; });
        bary[id] = sum / ns.length;
      });
      layer.sort(function (a, b) { return bary[a] - bary[b] || order[a] - order[b]; });
      layer.forEach(function (id, i) { order[id] = i; });
    }
    reindex();
    for (var iter = 0; iter < 6; iter++) {
      for (var i = 1; i < layers.length; i++) { sweep(layers[i], preds); }
      for (var j = layers.length - 2; j >= 0; j--) { sweep(layers[j], succs); }
    }
    var maxW = 40;
    nodes.forEach(function (n) { maxW = Math.max(maxW, Number(n.width) || 40); });
    var gapX = maxW + 70;
    var gapY = 46;
    var pos = {};
    layers.forEach(function (l, li) {
      l.forEach(function (id, i) {
        pos[id] = { x: li * gapX, y: (i - (l.length - 1) / 2) * gapY };
      });
    });
    return pos;
  }

  function buildSubgraphView() {
    destroySubgraphView();
    var container = document.getElementById("subgraph-canvas");
    if (!container) { return; }
    var members = subgraphNodes();
    var idSet = {};
    members.forEach(function (n) { idSet[n.id()] = true; });
    var nodeData = members.map(function (n) { var dd = Object.assign({}, n.data()); delete dd.parent; return dd; });
    var edgeData = [];
    cy.edges().forEach(function (e) {
      if (e.hasClass("transitive")) { return; }
      if (idSet[e.source().id()] && idSet[e.target().id()]) {
        edgeData.push({ data: Object.assign({}, e.data()), classes: e.classes().join(" ") });
      }
    });
    var pos = layeredPositions(nodeData, edgeData.map(function (e) { return e.data; }));
    var elements = members.map(function (n, i) {
      return { data: nodeData[i], classes: n.classes().join(" "), position: pos[n.id()] };
    }).concat(edgeData);
    subgraphCy = window.cytoscape({
      container: container,
      elements: elements,
      style: cy.style().json().filter(function (rule) {
        return rule.selector.indexOf("hidden") === -1 && rule.selector.indexOf("dimmed") === -1;
      }),
      layout: { name: "preset", padding: 24, fit: true },
      wheelSensitivity: 0.22,
      boxSelectionEnabled: false
    });
    subgraphCy.on("tap", "node", function (evt) {
      var target = cy.getElementById(evt.target.id());
      if (target && target.length > 0) {
        selectElement(target);
        if (cy.animate) { cy.animate({ center: { eles: target }, duration: 220 }); }
      }
    });
  }

  function renderInspector(node) {
    if (!inspector) { return; }
    var d = node.data();
    var htmlParts = [];
    destroySubgraphView();
    var headerButtons =
      '<div class="insp-actions">' +
      '<button type="button" class="insp-btn" data-action="close-inspector" title="Close">&times;</button>' +
      '</div>';

    if (d.group === "declaration") {
      htmlParts.push(
        '<div class="insp-head"><div class="insp-title">' + escapeHtml(d.full_name || d.label) + '</div>' +
        headerButtons + '</div>'
      );
      htmlParts.push(
        '<div class="insp-meta"><span class="chip ' + escapeHtml(d.state) + '"></span>' +
        '<strong>' + escapeHtml(d.kind) + '</strong> &middot; ' +
        escapeHtml(d.file_path) + ' (lines ' + escapeHtml(d.lines) + ')' +
        (d.is_sorry ? ' &middot; <strong style="color:#ff6b6b;">sorry</strong>' : '') +
        '</div>'
      );
      htmlParts.push(
        '<div class="insp-stamps">' +
        '<div>checked: ' + renderStampValue(d.checked_stamp || "\u2014", d.checked_request_id ? "check" : "verify_proof", d.checked_request_id || d.closure_verified_request_id) + '</div>' +
        '<div>verified: ' + renderStampValue(d.verified_stamp || "\u2014", "verify_proof", d.verified_request_id) + '</div>' +
        '</div>'
      );
      if (d.doc_html) {
        htmlParts.push('<div class="insp-sec">Documentation</div><div class="insp-doc">' + d.doc_html + '</div>');
      }
      var sourceText = d.code || d.signature || "";
      if (sourceText) {
        htmlParts.push(
          '<div class="insp-code-head"><span class="insp-sec">Source</span>' +
          '<button type="button" class="insp-btn copy-code-btn">Copy</button></div>' +
          renderCodeBlock(sourceText, d.code ? d.code_start_line : 1)
        );
      }
      var declCone = transitiveCone(node, "depends");
      var declSplit = splitDirectAndTransitive(node, "depends", declCone);
      var upDeclTotal = declSplit.directUp.length + declSplit.transUp.length;
      var downDeclTotal = declSplit.directDown.length + declSplit.transDown.length;
      if (upDeclTotal > 0 || downDeclTotal > 0) {
        htmlParts.push(
          '<div class="insp-subgraph-bar">' +
          '<span class="sg-pill upstream">' + upDeclTotal + ' upstream</span>' +
          '<span class="sg-pill downstream">' + downDeclTotal + ' downstream</span>' +
          '</div>'
        );
        htmlParts.push(subgraphSectionHtml());
      }
      appendChipGroup(htmlParts, "Depends on", "upstream", declSplit.directUp, "");
      appendChipGroup(htmlParts, "Transitive upstream", "upstream", declSplit.transUp, "transitive");
      appendChipGroup(htmlParts, "Used by", "downstream", declSplit.directDown, "");
      appendChipGroup(htmlParts, "Transitive downstream", "downstream", declSplit.transDown, "transitive");
      if (d.external_deps && d.external_deps.length > 0) {
        htmlParts.push('<div class="insp-sec">External dependencies (' + d.external_deps.length + ')</div><div class="insp-chips">');
        for (var ex = 0; ex < d.external_deps.length; ex++) {
          htmlParts.push('<span class="insp-ext">' + escapeHtml(d.external_deps[ex]) + '</span>');
        }
        htmlParts.push('</div>');
      }
    } else if (d.group === "file") {
      htmlParts.push(
        '<div class="insp-head"><div class="insp-title">' + escapeHtml(d.path || d.label) + '</div>' +
        headerButtons + '</div>'
      );
      htmlParts.push(
        '<div class="insp-meta"><span class="chip ' + escapeHtml(d.state) + '"></span>' +
        'module <strong>' + escapeHtml(d.module) + '</strong> &middot; ' +
        escapeHtml(d.status_text) + '<br>' + escapeHtml(d.decl_summary) + '</div>'
      );
      if (d.doc_html) {
        htmlParts.push('<div class="insp-sec">Module Documentation</div><div class="insp-doc">' + d.doc_html + '</div>');
      }
      if (d.code) {
        var lineCount = String(d.code).split("\\n").length;
        htmlParts.push(
          '<details class="insp-file-code"><summary class="insp-sec">Source (' + lineCount + ' lines)</summary>' +
          '<div class="insp-code-head"><span></span><button type="button" class="insp-btn copy-code-btn">Copy</button></div>' +
          renderCodeBlock(d.code, 1) + '</details>'
        );
      }
      var fileCone = transitiveCone(node, "import");
      var fileSplit = splitDirectAndTransitive(node, "import", fileCone);
      var upFileTotal = fileSplit.directUp.length + fileSplit.transUp.length;
      var downFileTotal = fileSplit.directDown.length + fileSplit.transDown.length;
      if (upFileTotal > 0 || downFileTotal > 0) {
        htmlParts.push(
          '<div class="insp-subgraph-bar">' +
          '<span class="sg-pill upstream">' + upFileTotal + ' upstream</span>' +
          '<span class="sg-pill downstream">' + downFileTotal + ' downstream</span>' +
          '</div>'
        );
        htmlParts.push(subgraphSectionHtml());
      }
      appendChipGroup(htmlParts, "Imports", "upstream", fileSplit.directUp, "");
      appendChipGroup(htmlParts, "Transitive upstream", "upstream", fileSplit.transUp, "transitive");
      appendChipGroup(htmlParts, "Imported by", "downstream", fileSplit.directDown, "");
      appendChipGroup(htmlParts, "Transitive downstream", "downstream", fileSplit.transDown, "transitive");
      var members = node.children('[group = "declaration"]').toArray();
      appendChipGroup(htmlParts, "Declarations", "", members, "");
    } else {
      hasSelection = false;
      inspector.style.display = "none";
      updateDrawerChrome();
      return;
    }

    hasSelection = true;
    drawerCollapsed = false;
    inspector.innerHTML = htmlParts.join("");
    renderMathIn(inspector);
    inspector.style.display = "block";
    updateDrawerChrome();

    if (!inspector.querySelectorAll) { return; }
    var chips = inspector.querySelectorAll(".insp-chip");
    for (var i = 0; i < chips.length; i++) {
      chips[i].addEventListener("click", function () {
        var targetId = this.getAttribute("data-target-id");
        var targetNode = cy.getElementById(targetId);
        if (targetNode && targetNode.length > 0) {
          selectElement(targetNode);
          if (cy.animate) { cy.animate({ center: { eles: targetNode }, duration: 220 }); }
        }
      });
    }
    var sgDetails = inspector.querySelector("details.insp-subgraph-view");
    if (sgDetails) {
      sgDetails.addEventListener("toggle", function () {
        subgraphOpen = sgDetails.open;
        if (subgraphOpen) { buildSubgraphView(); } else { destroySubgraphView(); }
      });
      if (subgraphOpen) { buildSubgraphView(); }
    }
    var closeButtons = inspector.querySelectorAll('[data-action="close-inspector"]');
    for (var cl = 0; cl < closeButtons.length; cl++) {
      closeButtons[cl].addEventListener("click", function () {
        clearMark();
      });
    }
    var copyButtons = inspector.querySelectorAll(".copy-code-btn");
    for (var cp = 0; cp < copyButtons.length; cp++) {
      copyButtons[cp].addEventListener("click", function () {
        var btn = this;
        var text = d.code || d.signature || "";
        if (typeof navigator !== "undefined" && navigator.clipboard && navigator.clipboard.writeText) {
          navigator.clipboard.writeText(text).then(function () {
            btn.textContent = "Copied";
          });
        }
      });
    }
  }

  function selectElement(target) {
    clearMark(true);
    if (!target || target === cy) {
      clearMark();
      return;
    }
    currentTarget = target;
    var group = target.data && target.data("group");
    if (group === "declaration" || group === "file") {
      var edgeKind = group === "declaration" ? "depends" : "import";
      var cone = transitiveCone(target, edgeKind);
      marked = cone.all;
      cy.batch(function () {
        for (var i = 0; i < cone.upstream.length; i++) {
          cone.upstream[i].addClass("highlighted upstream");
        }
        for (var j = 0; j < cone.downstream.length; j++) {
          cone.downstream[j].addClass("highlighted downstream");
        }
        target.addClass("highlighted selected-node");
        renderInspector(target);
      });
    } else if (target.isEdge && target.isEdge()) {
      var src = target.source();
      var tgt = target.target();
      marked = [target, src, tgt];
      cy.batch(function () {
        target.addClass("highlighted");
        src.addClass("highlighted upstream");
        tgt.addClass("highlighted downstream");
      });
    } else {
      marked = target.closedNeighborhood().toArray();
      cy.batch(function () {
        for (var k = 0; k < marked.length; k++) {
          marked[k].addClass("highlighted");
        }
        if (target.isNode && target.isNode()) {
          target.addClass("selected-node");
          renderInspector(target);
        }
      });
    }
    refreshEdgeVisibility();
  }

  function moveTooltip(e) {
    var ev = e.originalEvent;
    if (!ev || typeof ev.clientX !== "number") { return; }
    tooltip.style.left = ev.clientX + 14 + "px";
    tooltip.style.top = ev.clientY + 14 + "px";
  }

  function highlightMatch(text, q) {
    var raw = String(text || "");
    var idx = raw.toLowerCase().indexOf(q);
    if (idx === -1) { return escapeHtml(raw); }
    return (
      escapeHtml(raw.slice(0, idx)) +
      "<mark>" + escapeHtml(raw.slice(idx, idx + q.length)) + "</mark>" +
      escapeHtml(raw.slice(idx + q.length))
    );
  }

  function rankSearchMatch(n, q) {
    var label = (n.data("label") || "").toLowerCase();
    var fullName = (n.data("full_name") || "").toLowerCase();
    var path = (n.data("path") || "").toLowerCase();
    var sig = (n.data("signature") || "").toLowerCase();
    var doc = (n.data("doc") || "").toLowerCase();
    if (label === q || fullName === q) { return 0; }
    if (label.indexOf(q) === 0) { return 1; }
    if (fullName.indexOf(q) === 0 || path.indexOf(q) === 0) { return 2; }
    if (label.indexOf(q) !== -1 || fullName.indexOf(q) !== -1 || path.indexOf(q) !== -1) { return 3; }
    if (sig.indexOf(q) !== -1) { return 4; }
    if (doc.indexOf(q) !== -1) { return 5; }
    return -1;
  }

  function renderAutocomplete(matches, q) {
    if (searchCount) {
      searchCount.textContent = q ? (matches.length + (matches.length === 1 ? " match" : " matches")) : "";
    }
    if (!searchAutocomplete) { return; }
    if (!q) {
      hideAutocomplete();
      return;
    }
    if (matches.length === 0) {
      searchAutocomplete.innerHTML = '<div class="ac-empty">No matching files, declarations, or docs</div>';
      searchAutocomplete.style.display = "block";
      return;
    }
    var limit = Math.min(matches.length, 12);
    var rows = [];
    for (var i = 0; i < limit; i++) {
      var n = matches[i];
      var d = n.data();
      var title = d.group === "declaration" ? (d.full_name || d.label) : (d.path || d.label);
      var kindTag = d.group === "declaration" ? d.kind : "file";
      var meta = d.group === "declaration" ? d.file_path : (d.module + " \u00b7 " + d.decl_summary);
      var previewRaw = (d.doc || d.signature || "").replace(/\\s+/g, " ").trim();
      if (previewRaw.length > 90) { previewRaw = previewRaw.slice(0, 87) + "..."; }
      rows.push(
        '<div class="ac-item' + (i === activeAcIndex ? ' active' : '') + '" data-target-id="' + escapeHtml(n.id()) + '">' +
        '<div class="ac-top"><span class="ac-name"><span class="chip ' + escapeHtml(d.state) + '"></span>' +
        highlightMatch(title, q) + '</span><span class="ac-kind">' + escapeHtml(kindTag) + '</span></div>' +
        '<div class="ac-meta">' + escapeHtml(meta) + '</div>' +
        (previewRaw ? '<div class="ac-preview">' + highlightMatch(previewRaw, q) + '</div>' : '') +
        '</div>'
      );
    }
    searchAutocomplete.innerHTML = rows.join("");
    searchAutocomplete.style.display = "block";
    if (searchAutocomplete.querySelectorAll) {
      var items = searchAutocomplete.querySelectorAll(".ac-item");
      for (var k = 0; k < items.length; k++) {
        items[k].addEventListener("click", function () {
          var targetId = this.getAttribute("data-target-id");
          var targetNode = cy.getElementById(targetId);
          if (targetNode && targetNode.length > 0) {
            selectElement(targetNode);
            if (cy.animate) { cy.animate({ center: { eles: targetNode }, duration: 220 }); }
            hideAutocomplete();
          }
        });
      }
    }
  }

  function updateAutocompleteActive() {
    if (!searchAutocomplete || !searchAutocomplete.querySelectorAll) { return; }
    var items = searchAutocomplete.querySelectorAll(".ac-item");
    for (var i = 0; i < items.length; i++) {
      if (i === activeAcIndex) {
        items[i].classList.add("active");
        if (items[i].scrollIntoView) { items[i].scrollIntoView({ block: "nearest" }); }
      } else {
        items[i].classList.remove("active");
      }
    }
  }

  if (declToggle) {
    declToggle.addEventListener("change", function () {
      depsHidden = !declToggle.checked;
      clearMark();
    });
  }
  if (transToggle) {
    transToggle.addEventListener("change", function () {
      transHidden = !transToggle.checked;
      clearMark();
    });
  }
  if (searchInput) {
    searchInput.addEventListener("input", function () {
      var q = searchInput.value.trim().toLowerCase();
      if (!q) {
        acMatches = [];
        hideAutocomplete();
        if (searchCount) { searchCount.textContent = ""; }
        clearMark();
        return;
      }
      var scored = [];
      cy.nodes().forEach(function (n) {
        var g = n.data("group");
        if (g !== "declaration" && g !== "file") { return; }
        var score = rankSearchMatch(n, q);
        if (score !== -1) {
          scored.push({ node: n, score: score, grp: g === "file" ? 0 : 1, lbl: (n.data("label") || "").toLowerCase() });
        }
      });
      scored.sort(function (a, b) {
        if (a.score !== b.score) { return a.score - b.score; }
        if (a.grp !== b.grp) { return a.grp - b.grp; }
        if (a.lbl.length !== b.lbl.length) { return a.lbl.length - b.lbl.length; }
        return a.lbl < b.lbl ? -1 : (a.lbl > b.lbl ? 1 : 0);
      });
      acMatches = scored.map(function (entry) { return entry.node; });
      activeAcIndex = acMatches.length > 0 ? 0 : -1;
      cy.batch(function () {
        cy.elements().removeClass("highlighted upstream downstream selected-node dimmed");
        if (acMatches.length > 0) {
          cy.nodes('[group = "declaration"]').addClass("dimmed");
          for (var i = 0; i < acMatches.length; i++) {
            acMatches[i].removeClass("dimmed").addClass("highlighted");
          }
        }
      });
      renderAutocomplete(acMatches, q);
    });
    searchInput.addEventListener("keydown", function (ev) {
      var shownCount = Math.min(acMatches.length, 12);
      if (ev.key === "ArrowDown" && shownCount > 0) {
        if (ev.preventDefault) { ev.preventDefault(); }
        activeAcIndex = (activeAcIndex + 1) % shownCount;
        updateAutocompleteActive();
      } else if (ev.key === "ArrowUp" && shownCount > 0) {
        if (ev.preventDefault) { ev.preventDefault(); }
        activeAcIndex = activeAcIndex <= 0 ? shownCount - 1 : activeAcIndex - 1;
        updateAutocompleteActive();
      } else if (ev.key === "Enter") {
        if (ev.preventDefault) { ev.preventDefault(); }
        if (acMatches.length > 0) {
          var chosen = acMatches[activeAcIndex >= 0 && activeAcIndex < shownCount ? activeAcIndex : 0];
          selectElement(chosen);
          if (cy.animate) { cy.animate({ center: { eles: chosen }, duration: 220 }); }
          hideAutocomplete();
        }
      } else if (ev.key === "Escape") {
        if (searchAutocomplete && searchAutocomplete.style.display !== "none") {
          hideAutocomplete();
        } else {
          searchInput.value = "";
          acMatches = [];
          if (searchCount) { searchCount.textContent = ""; }
          clearMark();
        }
      }
    });
  }

  if (typeof document.addEventListener === "function") {
    document.addEventListener("click", function (ev) {
      if (!searchAutocomplete || searchAutocomplete.style.display === "none") { return; }
      var t = ev.target;
      if (t === searchInput || (searchAutocomplete.contains && searchAutocomplete.contains(t))) { return; }
      hideAutocomplete();
    });
  }

  cy.on("tap", function (e) {
    if (e.target === cy) { clearMark(); return; }
    selectElement(e.target);
  });
  cy.on("mouseover", "node", function (e) {
    tooltip.innerHTML = e.target.data("tooltip") || "";
    tooltip.style.display = "block";
    moveTooltip(e);
  });
  cy.on("mousemove", "node", function (e) { moveTooltip(e); });
  cy.on("mouseout", "node", function () { tooltip.style.display = "none"; });
  if (drawer && drawer.addEventListener) {
    drawer.addEventListener("mouseenter", function () { tooltip.style.display = "none"; });
  }

  var resetButton = document.getElementById("reset-positions");
  if (resetButton) {
    resetButton.addEventListener("click", function () {
      if (searchInput) { searchInput.value = ""; }
      acMatches = [];
      hideAutocomplete();
      if (searchCount) { searchCount.textContent = ""; }
      clearMark();
      cy.batch(function () {
        cy.nodes().forEach(function (node) {
          var preset = initialPositions[node.id()];
          if (preset !== undefined) { node.position(preset); }
        });
      });
      spreadFileClusters();
      cy.fit(undefined, 40);
    });
  }

  if (toggleDockBtn && toggleDockBtn.addEventListener) {
    toggleDockBtn.addEventListener("click", function () {
      dockMode = dockMode === "bottom" ? "side" : "bottom";
      drawerCollapsed = false;
      drawerFull = false;
      updateDrawerChrome();
    });
  }
  if (toggleFullBtn && toggleFullBtn.addEventListener) {
    toggleFullBtn.addEventListener("click", function () {
      drawerFull = !drawerFull;
      if (drawerFull) { drawerCollapsed = false; }
      updateDrawerChrome();
    });
  }
  if (toggleDrawerBtn && toggleDrawerBtn.addEventListener) {
    toggleDrawerBtn.addEventListener("click", function () {
      drawerCollapsed = !drawerCollapsed;
      updateDrawerChrome();
    });
  }
  if (drawerResizer && drawerResizer.addEventListener) {
    var draggingResize = false;
    var applyDragSize = function (clientX, clientY) {
      var vw = typeof window !== "undefined" && window.innerWidth ? window.innerWidth : 1200;
      var vh = typeof window !== "undefined" && window.innerHeight ? window.innerHeight : 800;
      drawerCollapsed = false;
      if (dockMode === "side") {
        var nextW = Math.max(280, Math.min(vw, Math.round(vw - clientX)));
        if (nextW >= vw - 16) {
          drawerFull = true;
          customSideWidth = vw;
        } else {
          drawerFull = false;
          customSideWidth = nextW;
        }
      } else {
        var nextH = Math.max(96, Math.min(vh, Math.round(vh - clientY)));
        if (nextH >= vh - 16) {
          drawerFull = true;
          customBottomHeight = vh;
        } else {
          drawerFull = false;
          customBottomHeight = nextH;
        }
      }
      updateDrawerChrome();
    };
    drawerResizer.addEventListener("mousedown", function (ev) {
      if (ev.preventDefault) { ev.preventDefault(); }
      draggingResize = true;
      if (drawer && drawer.classList) { drawer.classList.add("resizing"); }
    });
    drawerResizer.addEventListener("touchstart", function (ev) {
      draggingResize = true;
      if (drawer && drawer.classList) { drawer.classList.add("resizing"); }
      if (ev.touches && ev.touches[0]) {
        applyDragSize(ev.touches[0].clientX, ev.touches[0].clientY);
      }
    });
    drawerResizer.addEventListener("dblclick", function () {
      drawerFull = !drawerFull;
      drawerCollapsed = false;
      updateDrawerChrome();
    });
    if (typeof document.addEventListener === "function") {
      document.addEventListener("mousemove", function (ev) {
        if (!draggingResize) { return; }
        applyDragSize(ev.clientX, ev.clientY);
      });
      document.addEventListener("touchmove", function (ev) {
        if (!draggingResize || !ev.touches || !ev.touches[0]) { return; }
        applyDragSize(ev.touches[0].clientX, ev.touches[0].clientY);
      });
      var stopResize = function () {
        if (!draggingResize) { return; }
        draggingResize = false;
        if (drawer && drawer.classList) { drawer.classList.remove("resizing"); }
      };
      document.addEventListener("mouseup", stopResize);
      document.addEventListener("touchend", stopResize);
      document.addEventListener("touchcancel", stopResize);
    }
  }

  refreshEdgeVisibility();
  updateDrawerChrome();
  spreadFileClusters();
  cy.fit(undefined, 40);

  cy.on("resize", function () { cy.fit(undefined, 40); });
})();
</script>
</body>
</html>
"""
