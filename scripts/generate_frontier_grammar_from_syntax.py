from __future__ import annotations

from pathlib import Path

from generate_partial_from_syntax import Elem, Production, parse_syntax_rules


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "LwRust" / "Extractor" / "Generated" / "FrontierGrammar.lean"


BASE_CATS = {
    "cty": "cty",
    "clval": "clval",
    "cterm": "cterm",
}

LIST_CATS = {
    "clval": ("clvals", "clvalsTail"),
    "cterm": ("cterms", "ctermsTail"),
}

ATOM_TERMINALS = {
    "ident": "ident",
    "num": "num",
    "term": "lifetime",
}

TOKEN_TERMINALS = {
    '"cty_unit"': "ctyUnit",
    '"cty_int"': "ctyInt",
    '"cty_bool"': "ctyBool",
    '"()"': "unit",
    '"true"': "trueLit",
    '"false"': "falseLit",
    '"&"': "amp",
    '"["': "lbrack",
    '"]"': "rbrack",
    '","': "comma",
    '"box"': "box",
    '"*"': "star",
    '"block"': "block",
    '"{"': "lbrace",
    '"}"': "rbrace",
    '"let"': "letKw",
    '"mut"': "mutKw",
    '":="': "assign",
    '"copy"': "copyKw",
    '"=="': "eqEq",
    '"if"': "ifKw",
    '"else"': "elseKw",
    '"while"': "whileKw",
}

TERMINAL_ORDER = [
    "ctyUnit",
    "ctyInt",
    "ctyBool",
    "unit",
    "trueLit",
    "falseLit",
    "amp",
    "lbrack",
    "rbrack",
    "comma",
    "box",
    "star",
    "block",
    "lbrace",
    "rbrace",
    "letKw",
    "mutKw",
    "assign",
    "copyKw",
    "eqEq",
    "ifKw",
    "elseKw",
    "whileKw",
    "ident",
    "num",
    "lifetime",
]

DEFAULT_ATOM_TOKENS = {
    "ident": '.ident "__fw_default"',
    "num": ".num 0",
    "term": ".lifetime LwRust.Core.Lifetime.root",
}

DEFAULT_RULES = {
    "cty": "ctyUnit",
    "clval": "clvalVar",
    "cterm": "ctermUnit",
}


def cat_name(cat: str) -> str:
    return BASE_CATS[cat]


def list_cat_name(cat: str) -> str:
    return LIST_CATS[cat][0]


def tail_cat_name(cat: str) -> str:
    return LIST_CATS[cat][1]


def terminal_of(elem: Elem) -> str:
    if elem.kind == "token":
        return TOKEN_TERMINALS[elem.raw]
    if elem.kind == "atom":
        return ATOM_TERMINALS[elem.raw]
    raise ValueError(f"element {elem!r} is not a terminal")


def sym_of(elem: Elem) -> str:
    if elem.kind in {"token", "atom"}:
        return f".token .{terminal_of(elem)}"
    if elem.kind == "cat":
        return f".cat .{cat_name(elem.cat)}"
    if elem.kind == "list":
        return f".cat .{list_cat_name(elem.cat)}"
    raise ValueError(elem)


def rhs(elems: list[Elem]) -> str:
    return "[" + ", ".join(sym_of(elem) for elem in elems) + "]"


def render_rule_def(name: str, lhs: str, rhs_src: str) -> list[str]:
    return [
        f"def {name}Rule : Rule Cat Terminal :=",
        f'  {{ name := "{name}", lhs := .{lhs}, rhs := {rhs_src} }}',
        "",
    ]


def render_prod_rule(prod: Production) -> list[str]:
    return render_rule_def(prod.name, cat_name(prod.target_cat), rhs(prod.elems))


def render_list_rules(cat: str) -> list[str]:
    list_cat, tail_cat = LIST_CATS[cat]
    item_cat = cat_name(cat)
    prefix = list_cat
    tail_prefix = tail_cat[0].lower() + tail_cat[1:]
    return [
        *render_rule_def(f"{prefix}Empty", list_cat, "[]"),
        *render_rule_def(
            f"{prefix}Cons",
            list_cat,
            f"[.cat .{item_cat}, .cat .{tail_cat}]",
        ),
        *render_rule_def(f"{tail_prefix}Empty", tail_cat, "[]"),
        *render_rule_def(
            f"{tail_prefix}Cons",
            tail_cat,
            f"[.token .comma, .cat .{item_cat}, .cat .{tail_cat}]",
        ),
    ]


def default_tree_expr_for_elem(elem: Elem) -> str:
    if elem.kind == "token":
        return f".token (Tok.{terminal_of(elem)})"
    if elem.kind == "atom":
        return f".token ({DEFAULT_ATOM_TOKENS[elem.raw]})"
    if elem.kind == "cat":
        return f"defaultTree .{cat_name(elem.cat)}"
    if elem.kind == "list":
        return f"defaultTree .{list_cat_name(elem.cat)}"
    raise ValueError(elem)


def default_token_expr(terminal: str) -> str:
    if terminal == "ident":
        return '.ident "__fw_default"'
    if terminal == "num":
        return ".num 0"
    if terminal == "lifetime":
        return ".lifetime LwRust.Core.Lifetime.root"
    return f".{terminal}"


def default_tree_expr_for_prod(prod: Production) -> str:
    children = ", ".join(default_tree_expr_for_elem(elem) for elem in prod.elems)
    return f'.node "{prod.name}" [{children}]'


def default_tree_expr(cat: str, productions: list[Production]) -> str:
    if cat in DEFAULT_RULES:
        rule = DEFAULT_RULES[cat]
        for prod in productions:
            if prod.name == rule:
                return default_tree_expr_for_prod(prod)
        raise ValueError(f"missing default production {rule}")
    for _item_cat, (list_cat, tail_cat) in LIST_CATS.items():
        if cat == list_cat:
            return f'.node "{list_cat}Empty" []'
        if cat == tail_cat:
            tail_prefix = tail_cat[0].lower() + tail_cat[1:]
            return f'.node "{tail_prefix}Empty" []'
    raise ValueError(f"no default tree for category {cat}")


def used_list_cats(productions: list[Production]) -> list[str]:
    out: list[str] = []
    for prod in productions:
        for elem in prod.elems:
            if elem.kind == "list" and elem.cat not in out:
                out.append(elem.cat)
    return out


def render() -> str:
    productions = parse_syntax_rules()
    list_cats = used_list_cats(productions)
    rule_names = [prod.name for prod in productions]
    list_rule_names: list[str] = []
    for cat in list_cats:
        list_cat, tail_cat = LIST_CATS[cat]
        tail_prefix = tail_cat[0].lower() + tail_cat[1:]
        list_rule_names.extend([
            f"{list_cat}Empty",
            f"{list_cat}Cons",
            f"{tail_prefix}Empty",
            f"{tail_prefix}Cons",
        ])

    cat_constructors = ["cty", "clval", "cterm"]
    for cat in list_cats:
        cat_constructors.extend(LIST_CATS[cat])

    lines: list[str] = [
        "import LwRust.Extractor.Frontier",
        "",
        "/-!",
        "Generated FW-Rust grammar for parser frontiers.",
        "",
        "This file is generated from the syntax declarations and checked",
        "`SyntaxSemantics` annotations in `LwRust.Extractor.CompleteProgram`.",
        "Re-generate it with `scripts/generate_frontier_grammar_from_syntax.py`.",
        "-/",
        "",
        "namespace ConservativeExtractor",
        "namespace GrammarFrontier",
        "namespace FwRust",
        "",
        "inductive Cat where",
    ]
    lines.extend(f"  | {name}" for name in cat_constructors)
    lines.extend([
        "  deriving Repr, DecidableEq",
        "",
        "inductive Terminal where",
    ])
    lines.extend(f"  | {name}" for name in TERMINAL_ORDER)
    lines.extend([
        "  deriving Repr, DecidableEq",
        "",
        "inductive Tok where",
    ])
    for terminal in TERMINAL_ORDER:
        if terminal == "ident":
            lines.append("  | ident (name : Name)")
        elif terminal == "num":
            lines.append("  | num (value : Int)")
        elif terminal == "lifetime":
            lines.append("  | lifetime (lifetime : Lifetime)")
        else:
            lines.append(f"  | {terminal}")
    lines.extend([
        "  deriving Repr, DecidableEq",
        "",
        "def accepts : Terminal → Tok → Prop",
    ])
    for terminal in TERMINAL_ORDER:
        if terminal == "ident":
            lines.append("  | .ident, .ident _ => True")
        elif terminal == "num":
            lines.append("  | .num, .num _ => True")
        elif terminal == "lifetime":
            lines.append("  | .lifetime, .lifetime _ => True")
        else:
            lines.append(f"  | .{terminal}, .{terminal} => True")
    lines.extend([
        "  | _, _ => False",
        "",
        "def acceptsBool : Terminal → Tok → Bool",
    ])
    for terminal in TERMINAL_ORDER:
        if terminal == "ident":
            lines.append("  | .ident, .ident _ => Bool.true")
        elif terminal == "num":
            lines.append("  | .num, .num _ => Bool.true")
        elif terminal == "lifetime":
            lines.append("  | .lifetime, .lifetime _ => Bool.true")
        else:
            lines.append(f"  | .{terminal}, .{terminal} => Bool.true")
    lines.extend([
        "  | _, _ => Bool.false",
        "",
        "theorem acceptsBool_sound {terminal : Terminal} {tok : Tok}",
        "    (h : acceptsBool terminal tok = Bool.true) :",
        "    accepts terminal tok := by",
        "  cases terminal <;> cases tok <;>",
        "    simp [acceptsBool, accepts] at h ⊢",
        "",
        "theorem acceptsBool_complete {terminal : Terminal} {tok : Tok}",
        "    (h : accepts terminal tok) :",
        "    acceptsBool terminal tok = Bool.true := by",
        "  cases terminal <;> cases tok <;>",
        "    simp [acceptsBool, accepts] at h ⊢",
        "",
        "open Sym",
        "",
    ])

    for prod in productions:
        lines.extend(render_prod_rule(prod))
    for cat in list_cats:
        lines.extend(render_list_rules(cat))

    all_rules = rule_names + list_rule_names
    lines.extend([
        "def grammar : Grammar Cat Terminal Tok :=",
        "  { rules := [",
    ])
    for index, name in enumerate(all_rules):
        comma = "," if index + 1 < len(all_rules) else ""
        lines.append(f"      {name}Rule{comma}")
    lines.extend([
        "    ]",
        "    accepts := accepts }",
        "",
        "def checkableGrammar : CheckableGrammar Cat Terminal Tok :=",
        "  { grammar with",
        "    acceptsBool := acceptsBool",
        "    acceptsBool_sound := by",
        "      intro terminal tok h",
        "      exact acceptsBool_sound h",
        "    acceptsBool_complete := by",
        "      intro terminal tok h",
        "      exact acceptsBool_complete h }",
        "",
        "def defaultToken : Terminal → Tok",
    ])
    for terminal in TERMINAL_ORDER:
        lines.append(f"  | .{terminal} => {default_token_expr(terminal)}")
    lines.extend([
        "",
        "theorem defaultToken_valid (terminal : Terminal) :",
        "    acceptsBool terminal (defaultToken terminal) = Bool.true := by",
        "  cases terminal <;> native_decide",
        "",
        "def defaultTree : Cat → Tree Tok",
    ])
    for cat in cat_constructors:
        lines.append(f"  | .{cat} => {default_tree_expr(cat, productions)}")
    lines.extend([
        "",
        "theorem defaultTree_valid (cat : Cat) :",
        "    CheckableGrammar.checkTree checkableGrammar cat",
        "      (defaultTree cat) = Bool.true := by",
        "  cases cat <;> native_decide",
        "",
        "def defaultRawCompletion (cat : Cat) : CheckableGrammar.RawCompletion Tok :=",
        "  { suffix := (defaultTree cat).tokens",
        "    tree := defaultTree cat }",
        "",
        "theorem defaultRawCompletion_valid (cat : Cat) :",
        "    (defaultRawCompletion cat).valid checkableGrammar cat [] =",
        "      Bool.true := by",
        "  cases cat <;> native_decide",
        "",
        "def defaults : CheckableGrammar.Defaults checkableGrammar :=",
        "  { defaultToken := defaultToken",
        "    defaultToken_valid := by",
        "      intro terminal",
        "      exact defaultToken_valid terminal",
        "    defaultTree := defaultTree",
        "    defaultTree_valid := by",
        "      intro cat",
        "      exact defaultTree_valid cat }",
        "",
        "end FwRust",
        "end GrammarFrontier",
        "end ConservativeExtractor",
        "",
    ])
    return "\n".join(lines)


def main() -> None:
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(render())


if __name__ == "__main__":
    main()
