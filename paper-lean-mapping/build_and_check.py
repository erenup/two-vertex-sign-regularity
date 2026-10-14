#!/usr/bin/env python3
"""Check the paper-result inventory and its evidence map using only the standard library."""

import argparse
import copy
import html
import json
from pathlib import Path, PurePosixPath
import re


ROOT = Path(__file__).resolve().parents[1]
ENVIRONMENTS = ("theorem", "proposition", "lemma", "corollary", "example", "remark")
STATUSES = ("paper only", "formal result", "formal consequence", "formal ingredient", "exact example")


def need(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def safe_path(root, relative):
    need(isinstance(relative, str) and relative, "invalid relative path")
    parts = PurePosixPath(relative)
    need(not parts.is_absolute() and ".." not in parts.parts and "\\" not in relative,
         "unsafe relative path: " + relative)
    path = root.joinpath(*parts.parts)
    need(path.is_file() and not path.is_symlink(), "missing file: " + relative)
    need(path.resolve().is_relative_to(root.resolve()), "path outside repository: " + relative)
    return path


def uncomment_tex(text):
    return re.sub(r"(?<!\\)%[^\n]*", "", text)


def paper_inventory(texts, entry):
    """Read this manuscript's explicit input tree and shared section counter."""
    used = []

    def expand(path):
        need(path in texts, "missing paper input: " + path)
        need(path not in used, "repeated or cyclic paper input: " + path)
        used.append(path)
        content = uncomment_tex(texts[path])
        need("\\include{" not in content, "unsupported paper include")

        def include(match):
            relative = match.group(1)
            need(not relative.startswith("/") and ".." not in PurePosixPath(relative).parts,
                 "unsafe paper input")
            filename = relative if relative.endswith(".tex") else relative + ".tex"
            return expand(str(PurePosixPath("paper") / filename))

        # Store file ownership for result anchors before expanding the source.
        content = re.sub(r"\\begin\{(" + "|".join(ENVIRONMENTS) + r")\}",
                         lambda m: "@@FILE{" + path + "}" + m.group(0), content)
        return re.sub(r"\\input\{([^{}]+)\}", include, content)

    source = expand(entry)
    need(set(used) == set(texts), "paper input inventory mismatch")
    need(re.search(r"\\newtheorem\{theorem\}\{Theorem\}\[section\]", source) is not None,
         "unsupported theorem counter")
    definitions = re.findall(r"\\newtheorem\*?\{([^{}]+)\}", source)
    need(set(definitions) == set(ENVIRONMENTS) and len(definitions) == len(ENVIRONMENTS),
         "unsupported theorem environment inventory")
    for environment in ENVIRONMENTS[1:]:
        pattern = r"\\newtheorem\{" + environment + r"\}\[theorem\]\{[^{}]+\}"
        need(re.search(pattern, source) is not None, "unsupported shared result counter")
    need("\\setcounter{theorem}" not in source and "\\addtocounter{theorem}" not in source
         and "\\appendix" not in source and "\\counterwithin" not in source,
         "unsupported result renumbering")
    labels = re.findall(r"\\label\{([^{}]+)\}", source)
    need(len(labels) == len(set(labels)), "duplicate paper label")
    results = []
    section = 0
    count = 0
    token = re.compile(r"\\section(\*)?\{([^{}]+)\}|@@FILE\{([^{}]+)\}\\begin\{(" +
                       "|".join(ENVIRONMENTS) + r")\}(?:\[([^\]]*)\])?")
    section_title = ""
    for match in token.finditer(source):
        if match.group(2) is not None:
            if match.group(1) is None:
                section += 1
                count = 0
                section_title = match.group(2)
            continue
        path, environment = match.group(3), match.group(4)
        count += 1
        end = source.find("\\end{" + environment + "}", match.end())
        need(end >= 0, "unterminated numbered result")
        body = source[match.end():end]
        anchor = re.match(r"\s*\\label\{([^{}]+)\}", body)
        need(anchor is not None, "numbered result lacks an initial paper label")
        results.append({"label": anchor.group(1), "file": path,
                        "environment": environment, "number": f"{section}.{count}",
                        "section": str(section), "section_title": section_title,
                        "optional_title": match.group(5) or ""})
    need(results, "empty numbered-result inventory")
    return results, sorted(labels)


def lean_code(text):
    """Erase nested comments and strings, preserving line breaks."""
    result = []
    index = 0
    depth = 0
    string = False
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1
                result.extend("  ")
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                result.extend("  ")
                index += 2
            else:
                result.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif string:
            if text[index] == "\\" and index + 1 < len(text):
                result.extend("  ")
                index += 2
            else:
                if text[index] == '"':
                    string = False
                result.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif text.startswith("/-", index):
            depth = 1
            result.extend("  ")
            index += 2
        elif text.startswith("--", index):
            end = text.find("\n", index)
            if end == -1:
                end = len(text)
            result.extend(" " * (end - index))
            index = end
        elif text[index] == '"':
            string = True
            result.append(" ")
            index += 1
        else:
            result.append(text[index])
            index += 1
    need(depth == 0 and not string, "unterminated Lean comment or string")
    return "".join(result)


def declarations(text):
    namespace = []
    blocks = []
    found = set()
    for line in lean_code(text).splitlines():
        start = re.match(r"\s*(namespace|section)(?:\s+([\w.']+))?\s*$", line)
        if start:
            kind, name = start.groups()
            need(kind == "section" or name is not None, "unnamed Lean namespace")
            blocks.append((kind, name))
            if kind == "namespace":
                namespace.append(name)
            continue
        end = re.match(r"\s*end(?:\s+([\w.']+))?\s*$", line)
        if end:
            need(bool(blocks), "unmatched Lean end")
            kind, name = blocks.pop()
            need(end.group(1) is None or end.group(1) == name, "mismatched Lean end")
            if kind == "namespace":
                namespace.pop()
            continue
        declaration = re.match(r"\s*(?:@\[[^\]]+\]\s*)*(theorem|lemma)\s+([\w.']+)\b", line)
        if declaration:
            name = ".".join(namespace + [declaration.group(2)])
            need(name not in found, "duplicate Lean declaration")
            found.add(name)
    need(not blocks, "unclosed Lean namespace or section")
    return found


def check_map(data, paper_texts, lean_texts, files):
    need(set(data) == {"schema_version", "paper_entry", "paper_files", "numbered_results",
                       "ingredients", "other_labels", "checks", "scope"}, "mapping schema keys")
    need(type(data["schema_version"]) is int and data["schema_version"] == 1, "mapping schema version")
    need(data["paper_files"] == sorted(paper_texts), "paper source list mismatch")
    actual, labels = paper_inventory(paper_texts, data["paper_entry"])
    mapped = data["numbered_results"]
    need(isinstance(mapped, list) and len(mapped) == len(actual), "numbered result inventory mismatch")
    keys = ("label", "file", "environment", "number", "section", "section_title", "optional_title")
    need([{key: entry.get(key) for key in keys} for entry in mapped] == actual,
         "numbered result inventory mismatch")
    numbered_labels = {entry["label"] for entry in actual}
    need(data["other_labels"] == sorted(set(labels) - numbered_labels), "other-label inventory mismatch")
    checks = data["checks"]
    need(isinstance(checks, list), "invalid check catalogue")
    check_ids = set()
    for check in checks:
        need(set(check) == {"id", "path", "command_path", "command", "scope"}, "check schema keys")
        need(check["id"] not in check_ids, "duplicate exact check")
        check_ids.add(check["id"])
        need(check["path"] in files, "missing exact check: " + check["path"])
        need(check["command_path"] in files, "missing check entry point: " + check["command_path"])
        need(check["command"] == "python3 -B " + check["command_path"], "check command/path mismatch")
        need(isinstance(check["scope"], str) and check["scope"], "missing check scope")
    declaration_sets = {path: declarations(content) for path, content in lean_texts.items()}
    ingredient_ids = set()
    for entry in mapped + data["ingredients"]:
        is_numbered = "environment" in entry
        expected = set(keys) | {"title", "statement", "status", "scope", "lean", "checks"} if is_numbered else {
            "id", "title", "labels", "statement", "status", "scope", "lean", "checks"}
        need(set(entry) == expected, "result schema keys")
        need(entry["status"] in STATUSES, "unknown evidence status")
        for key in ("title", "statement", "scope"):
            need(isinstance(entry[key], str) and entry[key], "empty result description")
        if not is_numbered:
            need(entry["id"] not in ingredient_ids, "duplicate ingredient")
            ingredient_ids.add(entry["id"])
            need(entry["labels"] and len(set(entry["labels"])) == len(entry["labels"]),
                 "invalid ingredient label list")
            for label in entry["labels"]:
                need(label in labels, "missing paper label: " + label)
        need(isinstance(entry["checks"], list) and len(set(entry["checks"])) == len(entry["checks"]),
             "invalid exact-check list")
        need(set(entry["checks"]) <= check_ids, "unknown exact-check reference")
        need(entry["status"] != "exact example" or entry["checks"], "exact example lacks a check")
        need(isinstance(entry["lean"], list), "invalid declaration list")
        need(entry["status"] in ("paper only", "exact example") or entry["lean"], "formal evidence lacks a theorem")
        cited = set()
        for item in entry["lean"]:
            need(set(item) == {"name", "file", "scope"}, "Lean-reference schema keys")
            need((item["file"], item["name"]) not in cited, "duplicate Lean reference")
            cited.add((item["file"], item["name"]))
            need(item["file"] in declaration_sets, "missing Lean source: " + item["file"])
            need(item["name"] in declaration_sets[item["file"]],
                 "missing Lean declaration: " + item["name"])
            need(isinstance(item["scope"], str) and item["scope"], "missing formal scope")
    need(isinstance(data["scope"], list) and all(isinstance(s, str) and s for s in data["scope"]),
         "invalid global scope")
    return len(actual), len(ingredient_ids)


def cell(text):
    return html.escape(text, quote=False).replace("&lt;br&gt;", "<br>") \
        .replace("|", "&#124;").replace("\n", " ")


def render(data):
    lines = ["# Results by paper section", "",
             "The numbering follows the [paper](../paper/main.pdf). This file is generated from "
             "[mapping.json](mapping.json); the checker verifies the complete numbered-result inventory.", "",
             "Each formal scope is stated separately. Exact computations check finite instances or "
             "explicit arithmetic identities. The full matrix theorem is proved by the cited Lean declaration; finite examples do not supply its universal quantifiers.", ""]

    def result(entry, title):
        references = "<br>".join("[" + item["name"] + "](../" + item["file"] + "): " + item["scope"]
                                   for item in entry["lean"]) or "No declaration cited."
        exact = ", ".join("[" + key + "](#" + key + ")" for key in entry["checks"]) or "None assigned."
        return "| " + " | ".join(map(cell, [title, entry["statement"],
                    "**" + entry["status"].capitalize() + ".** " + entry["scope"] + "<br>" + references,
                    exact])) + " |"

    section = None
    for entry in data["numbered_results"]:
        if entry["section"] != section:
            section = entry["section"]
            lines += ["", "## " + section + ". " + entry["section_title"], "",
                      "| Result | Statement | Evidence and exact scope | Exact checks |",
                      "|---|---|---|---|"]
        lines.append(result(entry, entry["environment"].capitalize() + " " + entry["number"] +
                            " — " + entry["title"] + "<br>`" + entry["label"] + "`"))
        lines.append("") if entry is data["numbered_results"][-1] else None
    lines += ["", "## The three induction cases in Section 7", "",
              "These entries identify the three proved exclusion contracts used by the main theorem. They are not additional numbered paper results.", "",
              "| Ingredient | Statement | Evidence and exact scope | Exact checks |", "|---|---|---|---|"]
    for entry in data["ingredients"]:
        lines.append(result(entry, entry["title"] + "<br>" + ", ".join("`" + s + "`" for s in entry["labels"])))
    lines += ["", "## Exact computation commands", "",
              "Run these commands from the repository root. The [single entry point](../verification/run.py) "
              "runs the mathematical checks and their rejection controls; see [VERIFICATION.md](../VERIFICATION.md).", ""]
    for check in data["checks"]:
        lines += ["### " + check["id"], "", check["scope"], ""]
        if check["path"] != check["command_path"]:
            lines += ["The command below runs [" + PurePosixPath(check["path"]).name + "](../" +
                      check["path"] + ") through its suite, which supplies its required output arguments.", ""]
        lines += ["```sh", check["command"], "```", ""]
    lines += ["## Formal boundaries and scope", ""]
    lines.extend("- " + scope for scope in data["scope"])
    return "\n".join(lines) + "\n"


def negative_controls(data, papers, lean, files):
    count = 0

    def reject(label, change, fragment):
        nonlocal count
        changed_data, changed_papers, changed_lean, changed_files = (
            copy.deepcopy(data), dict(papers), dict(lean), set(files))
        change(changed_data, changed_papers, changed_lean, changed_files)
        try:
            check_map(changed_data, changed_papers, changed_lean, changed_files)
        except SystemExit as exc:
            need(str(exc).startswith("FAIL: ") and fragment in str(exc), "wrong rejection: " + label)
            count += 1
            return
        raise SystemExit("FAIL: accepted corruption: " + label)

    reject("omitted result", lambda d, p, l, f: d["numbered_results"].pop(), "numbered result inventory")
    reject("duplicate result", lambda d, p, l, f: d["numbered_results"].append(d["numbered_results"][0]),
           "numbered result inventory")
    reject("wrong number", lambda d, p, l, f: d["numbered_results"][0].update(number="1.99"),
           "numbered result inventory")
    reject("missing paper label", lambda d, p, l, f: p.update({"paper/main.tex":
           p["paper/main.tex"].replace("\\label{thm:main}", "\\label{thm:absent}", 1)}),
           "numbered result inventory")
    reject("unlabelled result", lambda d, p, l, f: p.update({"paper/main.tex":
           p["paper/main.tex"].replace("\\label{thm:main}", "", 1)}), "initial paper label")
    reject("missing input", lambda d, p, l, f: p.pop("paper/main.tex"), "paper source list")
    reject("missing ingredient label", lambda d, p, l, f: d["ingredients"][0].update(labels=["eq:absent"]),
           "missing paper label")
    formal = next(index for index, entry in enumerate(data["numbered_results"])
                  if entry["lean"] and entry["status"] != "paper only")
    item = data["numbered_results"][formal]["lean"][0]
    reject("nonexistent declaration", lambda d, p, l, f: d["numbered_results"][formal]["lean"][0].update(
           name="IV01.absentTheorem"), "missing Lean declaration")
    short = item["name"].split(".")[-1]
    reject("declaration removed from source", lambda d, p, l, f: l.update({item["file"]:
           l[item["file"]].replace("theorem " + short, "theorem absentTheorem", 1)}),
           "missing Lean declaration")
    reject("comment is not a declaration", lambda d, p, l, f: l.update({item["file"]:
           "/-\n" + l[item["file"]] + "\n-/\n"}), "missing Lean declaration")
    reject("missing exact checker", lambda d, p, l, f: f.remove(d["checks"][0]["path"]), "missing exact check")
    reject("unknown check reference", lambda d, p, l, f: d["numbered_results"][0].update(checks=["absent"]),
           "unknown exact-check reference")
    reject("formal claim without theorem", lambda d, p, l, f: d["numbered_results"][formal].update(lean=[]),
           "formal evidence lacks a theorem")
    example = next(index for index, entry in enumerate(data["numbered_results"])
                   if entry["status"] == "exact example")
    reject("example without check", lambda d, p, l, f: d["numbered_results"][example].update(checks=[]),
           "exact example lacks a check")
    reject("string is not a declaration", lambda d, p, l, f: l.update({item["file"]:
           'def exampleText : String := "theorem ' + short + ' : True"\n'}),
           "missing Lean declaration")
    reject("wrong namespace", lambda d, p, l, f: l.update({item["file"]:
           l[item["file"]].replace("namespace IV01", "namespace Absent", 1)
                            .replace("end IV01", "end Absent", 1)}),
           "missing Lean declaration")
    reject("unsupported counter change", lambda d, p, l, f: p.update({"paper/main.tex":
           p["paper/main.tex"] + "\n\\setcounter{theorem}{7}\n"}), "unsupported result renumbering")
    reject("unknown evidence status", lambda d, p, l, f: d["numbered_results"][0].update(status="absent"),
           "unknown evidence status")
    reject("missing other label", lambda d, p, l, f: d["other_labels"].pop(),
           "other-label inventory")
    reject("duplicate Lean reference", lambda d, p, l, f: d["numbered_results"][formal]["lean"].append(
           d["numbered_results"][formal]["lean"][0]), "duplicate Lean reference")
    reject("duplicate exact check", lambda d, p, l, f: d["checks"].append(d["checks"][0]),
           "duplicate exact check")
    try:
        json.loads('{"same": 1, "same": 2}', object_pairs_hook=unique_object)
    except SystemExit as exc:
        need(str(exc).startswith("FAIL: duplicate JSON key:"), "wrong duplicate-JSON-key rejection")
        count += 1
    else:
        raise SystemExit("FAIL: accepted duplicate JSON key")
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate by-section.md after validating the map")
    args = parser.parse_args()
    path = ROOT / "paper-lean-mapping/mapping.json"
    data = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_object)
    papers = {relative: safe_path(ROOT, relative).read_text(encoding="utf-8") for relative in data["paper_files"]}
    lean_paths = {item["file"] for entry in data["numbered_results"] + data["ingredients"] for item in entry["lean"]}
    lean = {relative: safe_path(ROOT, relative).read_text(encoding="utf-8") for relative in lean_paths}
    check_paths = {check[key] for check in data["checks"] for key in ("path", "command_path")}
    files = {path for path in check_paths if safe_path(ROOT, path)}
    results, ingredients = check_map(data, papers, lean, files)
    expected = render(data)
    table = ROOT / "paper-lean-mapping/by-section.md"
    if args.write:
        table.write_text(expected, encoding="utf-8")
    need(table.is_file() and table.read_text(encoding="utf-8") == expected, "by-section.md differs from mapping.json")
    controls = negative_controls(data, papers, lean, files)
    print(f"PASS: {results} numbered paper results, {ingredients} induction cases; labels, declarations, "
          f"exact-check paths and section table; {controls} rejection controls")


if __name__ == "__main__":
    try:
        main()
    except (OSError, UnicodeError, ValueError, TypeError, KeyError, AttributeError, IndexError) as exc:
        raise SystemExit("FAIL: invalid mapping or input: " + str(exc)) from None
