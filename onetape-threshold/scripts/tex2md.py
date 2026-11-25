#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Regenerate paper/paper.md from paper/paper.tex (the reference version).

The LaTeX source is first rewritten into plain LaTeX that pandoc understands (numbered theorem
headings, resolved \\ref and \\cite, section numbers, the bibliography as a list), then converted
with `pandoc -f latex -t gfm`, and the headings are shifted one level down under a title block.

Usage, from this directory:  python3 tex2md.py ../paper/paper.tex ../paper/paper.md
Requires pandoc (tested with 3.12).
"""
import re
import subprocess
import sys

THM_ENVS = {
    "theorem": "Theorem", "lemma": "Lemma", "proposition": "Proposition",
    "corollary": "Corollary", "conjecture": "Conjecture", "definition": "Definition", "remark": "Remark",
}


def braced(s, i):
    """Return (content, end) for the brace group starting at s[i] == '{'."""
    assert s[i] == "{", s[i:i + 30]
    depth = 0
    for j in range(i, len(s)):
        if s[j] == "{":
            depth += 1
        elif s[j] == "}":
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
    raise ValueError("unbalanced braces")


def bracketed(s, i):
    """Return (content, end) for an optional [..] argument at s[i], or (None, i)."""
    if i < len(s) and s[i] == "[":
        depth = 0
        for j in range(i, len(s)):
            if s[j] == "[":
                depth += 1
            elif s[j] == "]":
                depth -= 1
                if depth == 0:
                    return s[i + 1:j], j + 1
    return None, i


def replace_cmd(s, name, fn, nargs=1, opt=False):
    """Replace every \\name[opt]{a1}...{an} by fn(opt, args)."""
    out, i = [], 0
    pat = re.compile(r"\\" + name + r"(?![A-Za-z])")
    while True:
        m = pat.search(s, i)
        if not m:
            out.append(s[i:])
            return "".join(out)
        out.append(s[i:m.start()])
        j = m.end()
        o = None
        if opt:
            o, j = bracketed(s, j)
        args = []
        for _ in range(nargs):
            while s[j] in " \n":
                j += 1
            a, j = braced(s, j)
            args.append(a)
        out.append(fn(o, args))
        i = j


def number_labels(body):
    """Assign LaTeX-style numbers to sections, theorem-like environments and tables."""
    labels = {}
    sec = sub = thm = tab = 0
    current = None
    tok = re.compile(r"\\(section|subsection)(\*?)\{|\\begin\{(" + "|".join(THM_ENVS)
                     + r"|table)\}|\\label\{([^}]*)\}")
    for m in tok.finditer(body):
        if m.group(1) == "section" and not m.group(2):
            sec += 1
            sub = 0
            current = str(sec)
        elif m.group(1) == "subsection" and not m.group(2):
            sub += 1
            current = f"{sec}.{sub}"
        elif m.group(3) == "table":
            tab += 1
            current = str(tab)
        elif m.group(3):
            thm += 1
            current = str(thm)
        elif m.group(4):
            labels[m.group(4)] = current
    return labels


def convert(tex):
    pre_end = tex.index(r"\begin{document}")
    preamble = tex[:pre_end]
    body = tex[pre_end + len(r"\begin{document}"):tex.index(r"\end{document}")]
    title, _ = braced(preamble, preamble.index(r"\title{") + len(r"\title"))
    author, _ = braced(preamble, preamble.index(r"\author{") + len(r"\author"))
    date, _ = braced(preamble, preamble.index(r"\date{") + len(r"\date"))
    macros = "\n".join(l for l in preamble.splitlines()
                       if l.startswith(r"\newcommand") and not re.match(r"\\newcommand\{\\(lean|leanus)\}", l))

    labels = number_labels(body)
    body = body.replace(r"\maketitle", "")
    body = body.replace(r"\begin{abstract}", r"\section*{Abstract}").replace(r"\end{abstract}", "")
    body = replace_cmd(body, "texorpdfstring", lambda o, a: a[0], nargs=2)
    body = replace_cmd(body, "lean", lambda o, a: r"\texttt{" + a[0] + "}")
    body = re.sub(r"~(\\ref\{)", r" \1", body)
    body = replace_cmd(body, "ref", lambda o, a: labels[a[0]])
    body = re.sub(r"\\label\{[^}]*\}", "", body)

    def cite(o, a):
        keys = ", ".join(k.strip() for k in a[0].split(","))
        return "{}[" + keys + (", " + o if o else "") + "]"
    body = replace_cmd(body, "cite", cite, opt=True)

    counters = {"sec": 0, "sub": 0}

    def section(m):
        star, name = m.group(2), m.group(3)
        if m.group(1) == "section":
            if star:
                return r"\section*{" + name + "}"
            counters["sec"] += 1
            counters["sub"] = 0
            return r"\section*{" + f"{counters['sec']}. " + name + "}"
        counters["sub"] += 1
        return r"\subsection*{" + f"{counters['sec']}.{counters['sub']} " + name + "}"
    body = re.sub(r"\\(section|subsection)(\*?)\{((?:[^{}]|\{[^{}]*\})*)\}", section, body)
    body = replace_cmd(body, "paragraph", lambda o, a: r"\textbf{" + a[0] + "}\n\n")

    thm = {"n": 0}

    def thm_begin(m):
        env = m.group(1)
        thm["n"] += 1
        o, j = bracketed(m.string, m.end())
        head = r"\textbf{" + f"{THM_ENVS[env]} {thm['n']}" + "}"
        return head + (f" ({o})" if o else "") + ". ", j
    out, i = [], 0
    beg = re.compile(r"\\begin\{(" + "|".join(THM_ENVS) + r")\}")
    while True:
        m = beg.search(body, i)
        if not m:
            out.append(body[i:])
            break
        out.append(body[i:m.start()])
        head, j = thm_begin(m)
        out.append(head)
        i = j
    body = "".join(out)
    body = re.sub(r"\\end\{(" + "|".join(THM_ENVS) + r")\}", "", body)

    out, i = [], 0
    while True:
        k = body.find(r"\begin{proof}", i)
        if k < 0:
            out.append(body[i:])
            break
        out.append(body[i:k])
        o, j = bracketed(body, k + len(r"\begin{proof}"))
        out.append(r"\emph{" + (o if o else "Proof") + ".} ")
        i = j
    body = "".join(out)
    body = body.replace(r"\qedhere", "").replace(r"\end{proof}", "\n\n∎\n\n")
    body = re.sub(r"\.?\s*\n\n∎\n\n", lambda m: m.group(0), body)

    body = re.sub(r"\\item\[([^\]]*)\]", lambda m: r"\item \textbf{" + m.group(1) + "} ", body)

    def table(m):
        t = m.group(0)
        cap, _ = braced(t, t.index(r"\caption{") + len(r"\caption"))
        n = table.count = getattr(table, "count", 0) + 1
        tab = t[t.index(r"\begin{tabular}"):t.index(r"\end{tabular}") + len(r"\end{tabular}")]
        tab = re.sub(r"\\(toprule|bottomrule)", "", tab).replace(r"\midrule", r"\hline", 1)
        tab = tab.replace(r"\midrule", "")
        return tab + "\n\n" + r"\emph{Table " + str(n) + ": " + cap + "}\n"
    body = re.sub(r"\\begin\{table\}.*?\\end\{table\}", table, body, flags=re.S)

    def bib(m):
        items = re.split(r"\\bibitem\[([^\]]*)\]\{[^}]*\}", m.group(1))
        lines = []
        for k in range(1, len(items), 2):
            text = " ".join(items[k + 1].replace(r"\newblock", " ").split())
            lines.append(r"\item {}[" + items[k] + "] " + text)
        return "\\section*{References}\n\\begin{itemize}\n" + "\n".join(lines) + "\n\\end{itemize}\n"
    body = re.sub(r"\\begin\{thebibliography\}\{[^}]*\}(.*?)\\end\{thebibliography\}", bib, body,
                  flags=re.S)

    src = macros + "\n\\begin{document}\n" + body + "\n\\end{document}\n"
    md = subprocess.run(["pandoc", "-f", "latex", "-t", "gfm", "--wrap=none"], input=src,
                        capture_output=True, text=True, check=True).stdout
    md = re.sub(r"^(#+) ", lambda m: "#" + m.group(1) + " ", md, flags=re.M)
    md = re.sub(r"^#### (.*)$", r"**\1**", md, flags=re.M)
    md = md.replace("\n\n∎\n\n", " ∎\n\n")

    def mathblock(m):
        b = m.group(0).replace(r"\begin{align*}", r"\begin{aligned}").replace(r"\end{align*}", r"\end{aligned}")
        return b.replace("~", " ")
    md = re.sub(r"``` math\n.*?\n```", mathblock, md, flags=re.S)
    refs = md.index("## References")
    tail = md[refs:]
    while True:
        t = re.sub(r"(\n- [^\n]*)\n\n(?=- )", r"\1\n", tail)
        if t == tail:
            break
        tail = t
    md = md[:refs] + tail
    md = re.sub(r"(\n- [^\n]*) ∎\n", r"\1\n\n∎\n", md)

    def clean(s):
        s = s.replace("\\\\", " ").replace("$", "")
        s = re.sub(r"\\(mathsf|textsf)\{(\w+)\}", r"\2", s)
        s = s.replace("--", "–")
        return " ".join(s.split())
    head = f"# {clean(title)}\n\n**{author}** · {date}\n\n*Markdown rendering of `paper.tex`, which is the reference version.*\n\n"
    return head + md.lstrip()


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    tex = open(sys.argv[1], encoding="utf-8").read()
    open(sys.argv[2], "w", encoding="utf-8").write(convert(tex))


if __name__ == "__main__":
    main()
