from __future__ import annotations

import re
import sys
from collections import OrderedDict
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "formalization" / "ConservativeExtractor" / "CompleteProgram.lean"
TEMPLATE = ROOT / "formalization" / "ConservativeExtractor" / "Template" / "PartialProgram.lean"
OUTPUT = ROOT / "formalization" / "ConservativeExtractor" / "Generated" / "PartialProgram.lean"
LATEX_OUTPUT = ROOT / "paper" / "figures" / "grammar" / "generated-core-syntax.tex"
LATEX_COMPLETIONS_OUTPUT = ROOT / "paper" / "figures" / "grammar" / "generated-core-completions.tex"
MARKER = "/-- INSERT GRAMMAR HERE --/"


CATS = {
    "cty": ("Ty", "PartialTy", "CompletesTy"),
    "cplace": ("Place", "PartialPlace", "CompletesPlace"),
    "cexpr": ("Expr", "PartialExpr", "CompletesExpr"),
    "cstmt": ("Stmt", "PartialStmt", "CompletesStmt"),
    "cblock": ("Block", "PartialBlock", "CompletesBlock"),
    "cbranch": ("(Name × Block)", "PartialBranch", "CompletesBranch"),
    "cparam": ("(Name × Ty)", "PartialParam", "CompletesParam"),
}


LIST_CATS = {
    "cty": ("List Ty", "PartialTys", "CompletesTys"),
    "cplace": ("List Place", "PartialPlaces", "CompletesPlaces"),
    "cexpr": ("List Expr", "PartialExprs", "CompletesExprs"),
    "cstmt": ("List Stmt", "PartialStmts", "CompletesStmts"),
    "cblock": ("List Block", "PartialBlocks", "CompletesBlocks"),
    "cbranch": ("List (Name × Block)", "PartialBranches", "CompletesBranches"),
    "cparam": ("List (Name × Ty)", "PartialParams", "CompletesParams"),
}


ATOM_TYPES = {
    "ident": "Name",
}


PARTIAL_ATOMS = {
    "ident": ("Name", "PartialName", "CompletesName"),
}


NULLARY_AST = {
    "ctyUnit": "Ty.unit",
    "ctyNever": "Ty.never",
    "ctyBool": "Ty.bool",
    "ctyInt": "Ty.int",
    "cexprUnit": "Expr.unit",
    "cexprPanic": "Expr.panic",
}


# Surface syntax that is intentionally not a direct constructor application.
# The field order still comes from the checked syntax declaration; these entries
# only describe the checked macro-style desugaring target.
SUGAR_SPECS = {
    "cexprTrue": ("Expr.bool true", []),
    "cexprFalse": ("Expr.bool false", []),
    "cexprName": ("Expr.place (Place.var {f})", [("f", "Name")]),
    "cbranchNamed": ("({x}, {body})", [("x", "Name"), ("body", "Block")]),
    "cparamNamed": ("({x}, {τ})", [("x", "Name"), ("τ", "Ty")]),
    "cblockBraces": ("{stmts}", [("stmts", "List Stmt")]),
}


def cap(s: str) -> str:
    return s[:1].upper() + s[1:]


def lower(s: str) -> str:
    return s[:1].lower() + s[1:]


def paren_arg(s: str) -> str:
    if s.startswith("(") and s.endswith(")"):
        return s
    if any(x in s for x in [" ", "++", "::", "(", ")", "×"]):
        return f"({s})"
    return s


def app(head: str, args: list[str]) -> str:
    if not args:
        return head
    return head + " " + " ".join(paren_arg(a) for a in args)


def subst(template: str, values: dict[str, str]) -> str:
    out = template
    for k, v in values.items():
        out = out.replace("{" + k + "}", v)
    return out


@dataclass(frozen=True)
class Elem:
    kind: str
    raw: str
    cat: str | None = None

    @property
    def complete_type(self) -> str:
        if self.kind == "cat":
            return CATS[self.cat][0]
        if self.kind == "list":
            return f"List {CATS[self.cat][0]}"
        if self.raw == "num":
            raise AssertionError("num type is production-specific")
        return ATOM_TYPES[self.raw]

    @property
    def partial_type(self) -> str | None:
        if self.kind == "cat":
            return CATS[self.cat][1]
        if self.kind == "list":
            return LIST_CATS[self.cat][1]
        return None


@dataclass
class Production:
    name: str
    target_cat: str
    elems: list[Elem]
    ast: str
    field_names: list[str]
    field_types: list[str]


@dataclass
class Rule:
    production: Production
    state_name: str
    fields: list[tuple[str, str]]
    index: int
    mode: str


def tokenize(body: str) -> list[str]:
    return re.findall(r'"[^"]*"|\S+', body)


def parse_elem(tok: str) -> Elem:
    if tok.startswith('"'):
        return Elem("token", tok)
    if tok.endswith(",*"):
        return Elem("list", tok, tok[:-2])
    if tok in CATS:
        return Elem("cat", tok, tok)
    if tok in ["ident", "num", "term"]:
        return Elem("atom", tok)
    raise ValueError(f"unsupported syntax token: {tok}")


def is_partial_atom(elem: Elem) -> bool:
    return elem.kind == "atom" and elem.raw in PARTIAL_ATOMS


def split_top_level_words(s: str) -> list[str]:
    out: list[str] = []
    start = 0
    depth = 0
    for i, ch in enumerate(s):
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        elif ch.isspace() and depth == 0:
            if start < i:
                out.append(s[start:i])
            start = i + 1
    if start < len(s):
        out.append(s[start:])
    return out


def parse_field_groups(src: str) -> list[tuple[str, str]]:
    fields: list[tuple[str, str]] = []
    groups: list[str] = []
    i = 0
    while i < len(src):
        if src[i] != "(":
            i += 1
            continue
        start = i + 1
        depth = 1
        i += 1
        while i < len(src) and depth:
            if src[i] == "(":
                depth += 1
            elif src[i] == ")":
                depth -= 1
            i += 1
        groups.append(src[start:i - 1])
    for group in groups:
        if " : " not in group:
            continue
        names, typ = group.split(" : ", 1)
        for name in split_top_level_words(names.strip()):
            fields.append((name, typ.strip()))
    return fields


def parse_complete_constructors() -> dict[str, dict[str, list[tuple[str, str]]]]:
    constructors: dict[str, dict[str, list[tuple[str, str]]]] = {}
    lines = SOURCE.read_text().splitlines()
    current: str | None = None
    pending: str | None = None
    for raw in lines:
        line = raw.strip()
        m = re.match(r"inductive (Ty|Place|Expr|Stmt) where$", line)
        if m:
            if current is not None and pending is not None:
                body = pending[2:].strip()
                name = body.split()[0]
                constructors[current][name] = parse_field_groups(body)
            current = m.group(1)
            constructors[current] = {}
            pending = None
            continue
        if current is None:
            continue
        if line == "deriving Repr":
            if pending is not None:
                body = pending[2:].strip()
                name = body.split()[0]
                constructors[current][name] = parse_field_groups(body)
                pending = None
            current = None
            continue
        if line.startswith("| "):
            if pending is not None:
                body = pending[2:].strip()
                name = body.split()[0]
                constructors[current][name] = parse_field_groups(body)
            pending = line
        elif pending is not None and line:
            pending += " " + line
        else:
            continue
    return constructors


def constructor_for_syntax(name: str) -> tuple[str, str] | None:
    if name in SUGAR_SPECS or name in NULLARY_AST:
        return None
    mapping = {
        "cty": "Ty",
        "cplace": "Place",
        "cexpr": "Expr",
        "cstmt": "Stmt",
    }
    for prefix, type_name in mapping.items():
        if name.startswith(prefix):
            suffix = name[len(prefix):]
            ctor = lower(suffix)
            aliases = {
                "let": "letStmt",
            }
            ctor = aliases.get(ctor, ctor)
            return type_name, ctor
    return None


def direct_ast(type_name: str, ctor: str, fields: list[tuple[str, str]]) -> str:
    return app(f"{type_name}.{ctor}", ["{" + name + "}" for name, _ in fields])


def parse_syntax_rules() -> list[Production]:
    rules: list[Production] = []
    constructors = parse_complete_constructors()
    pattern = re.compile(r"^syntax \(name := ([^)]+)\) (.*) : (\w+)$")
    for line in SOURCE.read_text().splitlines():
        m = pattern.match(line.strip())
        if not m:
            continue
        name, body, target_cat = m.groups()
        if target_cat not in CATS:
            continue
        elems = [parse_elem(tok) for tok in tokenize(body)]
        if name in SUGAR_SPECS:
            ast, typed_fields = SUGAR_SPECS[name]
            field_names = [name for name, _ in typed_fields]
            field_types = [typ for _, typ in typed_fields]
        elif name in NULLARY_AST:
            ast = NULLARY_AST[name]
            field_names: list[str] = []
            field_types: list[str] = []
        else:
            direct = constructor_for_syntax(name)
            if direct is None:
                raise KeyError(name)
            type_name, ctor = direct
            typed_fields = constructors[type_name][ctor]
            ast = direct_ast(type_name, ctor, typed_fields)
            field_names = [name for name, _ in typed_fields]
            field_types = [typ for _, typ in typed_fields]
        rules.append(Production(name, target_cat, elems, ast, field_names, field_types))
    return rules


def elem_type(prod: Production, elem: Elem) -> str:
    for _i, candidate, _name, typ in field_elems(prod):
        if candidate is elem:
            return typ
    return elem.complete_type


def field_elems(prod: Production) -> list[tuple[int, Elem, str, str]]:
    out = []
    field_idx = 0
    for i, elem in enumerate(prod.elems):
        if elem.kind in ["cat", "atom", "list"]:
            out.append((i, elem, prod.field_names[field_idx], prod.field_types[field_idx]))
            field_idx += 1
    return out


def fields_before(prod: Production, index: int) -> list[tuple[str, str]]:
    out = []
    for i, elem, name, typ in field_elems(prod):
        if i >= index:
            break
        out.append((name, typ))
    return out


def fields_after(prod: Production, index: int) -> list[tuple[str, str]]:
    out = []
    for i, elem, name, typ in field_elems(prod):
        if i <= index:
            continue
        out.append((name, typ))
    return out


def state_name(prod: Production, elem: Elem, field_name: str, mode: str, index: int) -> str:
    target = prod.target_cat
    if target == "cexpr" and elem.kind == "cat" and elem.cat == "cexpr" and index == 0:
        return "exprPrefix"
    if target == "cstmt" and elem.kind == "cat" and elem.cat == "cstmt" and index == 0:
        return "stmtPrefix"
    if target == "cexpr" and elem.kind == "atom" and elem.raw == "ident" and index == 0:
        return "namePrefix"
    if prod.name == "ctyFn" and field_name == "params":
        return "fnParamTys"
    base = prod.name
    for prefix in ["cty", "cplace", "cexpr", "cstmt", "cblock", "cbranch", "cparam"]:
        if base.startswith(prefix):
            base = lower(base[len(prefix):])
            break
    return f"{base}{cap(field_name)}"


def token_label(raw: str) -> str:
    tok = raw[1:-1]
    labels = {
        ".": "Dot",
        ":": "Colon",
        ":=": "Assign",
        "=>": "Arrow",
        "(": "Lparen",
        ")": "Rparen",
        "[": "Lbrack",
        "]": "Rbrack",
        "{": "Lbrace",
        "}": "Rbrace",
        "<": "Lt",
        ">": "Gt",
        ",": "Comma",
    }
    if tok in labels:
        return labels[tok]
    cleaned = re.sub(r"[^A-Za-z0-9]+", " ", tok).title().replace(" ", "")
    return cleaned or "Token"


def state_name_for_token(prod: Production, elem: Elem) -> str:
    base = prod.name
    for prefix in ["cty", "cplace", "cexpr", "cstmt", "cblock", "cbranch", "cparam"]:
        if base.startswith(prefix):
            base = lower(base[len(prefix):])
            break
    return f"{base}{token_label(elem.raw)}"


def next_field_after(prod: Production, index: int) -> Elem | None:
    for elem in prod.elems[index + 1:]:
        if elem.kind in ["cat", "atom", "list"]:
            return elem
    return None


def token_frontier_is_redundant(prod: Production, index: int) -> bool:
    elem = next_field_after(prod, index)
    if elem is None:
        return True
    return elem.kind in ["cat", "list"] or is_partial_atom(elem)


def derive_states(productions: list[Production]):
    states: dict[str, OrderedDict[str, list[tuple[str, str]]]] = {cat: OrderedDict() for cat in CATS}
    rules: dict[str, list[Rule]] = {cat: [] for cat in CATS}

    for prod in productions:
        field_list = field_elems(prod)
        for i, elem, fname, ftype in field_list:
            before = fields_before(prod, i)
            if elem.kind == "cat":
                sname = state_name(prod, elem, fname, "cat", i)
                fields = before + [(fname, CATS[elem.cat][1])]
                add_state(states[prod.target_cat], sname, fields)
                rules[prod.target_cat].append(Rule(prod, sname, fields, i, "cat"))
            elif elem.kind == "atom":
                sname = state_name(prod, elem, fname, "atom", i)
                field_type = PARTIAL_ATOMS[elem.raw][1] if is_partial_atom(elem) else ftype
                fields = before + [(fname, field_type)]
                add_state(states[prod.target_cat], sname, fields)
                rules[prod.target_cat].append(Rule(prod, sname, fields, i, "atom"))
            elif elem.kind == "list":
                base = state_name(prod, elem, fname, "list", i)
                fields = before + [(fname, LIST_CATS[elem.cat][1])]
                add_state(states[prod.target_cat], base, fields)
                rules[prod.target_cat].append(Rule(prod, base, fields, i, "list"))
        for i, elem in enumerate(prod.elems):
            if elem.kind != "token":
                continue
            before = fields_before(prod, i)
            after = fields_after(prod, i)
            if not before or not after or token_frontier_is_redundant(prod, i):
                continue
            sname = state_name_for_token(prod, elem)
            add_state(states[prod.target_cat], sname, before)
            rules[prod.target_cat].append(Rule(prod, sname, before, i, "token"))
    return states, rules


def add_state(states: OrderedDict[str, list[tuple[str, str]]], name: str, fields: list[tuple[str, str]]) -> None:
    old = states.get(name)
    if old is not None and old != fields:
        raise ValueError(f"state {name} has incompatible fields: {old} vs {fields}")
    states.setdefault(name, fields)


def unique(fields: list[tuple[str, str]]) -> list[tuple[str, str]]:
    seen = set()
    out = []
    for f in fields:
        if f[0] in seen:
            continue
        seen.add(f[0])
        out.append(f)
    return out


def describe_production(prod: Production) -> str:
    return prod.ast


def state_origins(rules: dict[str, list[Rule]]) -> dict[str, dict[str, list[Production]]]:
    origins: dict[str, dict[str, list[Production]]] = {cat: {} for cat in CATS}
    seen: dict[str, dict[str, set[str]]] = {cat: {} for cat in CATS}
    for cat, cat_rules in rules.items():
        for rule in cat_rules:
            state_seen = seen[cat].setdefault(rule.state_name, set())
            if rule.production.name in state_seen:
                continue
            state_seen.add(rule.production.name)
            origins[cat].setdefault(rule.state_name, []).append(rule.production)
    return origins


def origin_comment(productions: list[Production]) -> str:
    return "; ".join(describe_production(prod) for prod in productions)


def used_list_cats(productions: list[Production]) -> list[str]:
    used = {elem.cat for prod in productions for elem in prod.elems if elem.kind == "list"}
    return [cat for cat in CATS if cat in used]


def render_list_inductive(cat: str) -> list[str]:
    complete, partial, _rel = CATS[cat]
    list_complete, list_partial, _list_rel = LIST_CATS[cat]
    return [
        f"inductive {list_partial} where",
        "  | cutoff",
        f"  | done (xs : {list_complete})",
        f"  | elems (pre : {list_complete}) (tail : Option {partial})",
        "  deriving Repr",
    ]


def render_inductive(
    cat: str,
    state_map: OrderedDict[str, list[tuple[str, str]]],
    origins: dict[str, list[Production]],
) -> list[str]:
    complete, partial, _rel = CATS[cat]
    lines = [f"inductive {partial} where"]
    lines.append("  | cutoff")
    lines.append(f"  | done (x : {complete})")
    last_comment: str | None = None
    for name, fields in state_map.items():
        if name in origins:
            comment = origin_comment(origins[name])
            if comment != last_comment:
                lines.append(f"  -- derived from: {comment}")
                last_comment = comment
        args = "".join(f" ({fname} : {fty})" for fname, fty in fields)
        lines.append(f"  | {name}{args}")
    lines.append("  deriving Repr")
    return lines


def render_rule(rule: Rule) -> list[str]:
    prod = rule.production
    _complete, partial, rel = CATS[prod.target_cat]
    elem = prod.elems[rule.index]
    names = {name: name for name, _ in fields_before(prod, rule.index)}
    binders = list(rule.fields)
    premises: list[str] = []
    partial_values = {name: name for name, _ in rule.fields}

    if rule.mode == "cat":
        fname = field_name_at(prod, rule.index)
        completed = f"{fname}'"
        binders.append((completed, CATS[elem.cat][0]))
        premises.append(f"{CATS[elem.cat][2]} {fname} {completed}")
        names[fname] = completed
        for name, typ in fields_after(prod, rule.index):
            binders.append((name, typ))
            names[name] = name
        suffix = ""
    elif rule.mode == "atom":
        fname = field_name_at(prod, rule.index)
        if is_partial_atom(elem):
            completed = f"{fname}'"
            complete_type, _partial_type, rel_name = PARTIAL_ATOMS[elem.raw]
            binders.append((completed, complete_type))
            premises.append(f"{rel_name} {fname} {completed}")
            names[fname] = completed
        else:
            names[fname] = fname
        for name, typ in fields_after(prod, rule.index):
            binders.append((name, typ))
            names[name] = name
        suffix = ""
    elif rule.mode == "list":
        fname = field_name_at(prod, rule.index)
        completed = f"{fname}'"
        _list_complete, _list_partial, list_rel = LIST_CATS[elem.cat]
        binders.append((completed, f"List {CATS[elem.cat][0]}"))
        premises.append(f"{list_rel} {fname} {completed}")
        names[fname] = completed
        for name, typ in fields_after(prod, rule.index):
            binders.append((name, typ))
            names[name] = name
        suffix = ""
    elif rule.mode == "token":
        for name, _typ in fields_before(prod, rule.index):
            names[name] = name
        for name, typ in fields_after(prod, rule.index):
            binders.append((name, typ))
            names[name] = name
        suffix = ""
    else:
        raise ValueError(rule.mode)

    target = subst(prod.ast, names)
    partial_term = app(f"{partial}.{rule.state_name}", [partial_values[name] for name, _ in rule.fields])
    ctor = f"{prod.name}_{rule.state_name}{suffix}"
    lines = [f"  | {ctor}{binder_group(unique(binders))} :"]
    lines.extend(f"      {p} →" for p in premises)
    lines.append(f"      {rel} ({partial_term}) ({target})")
    return lines


def render_list_relation(cat: str) -> list[str]:
    elem_complete, elem_partial, elem_rel = CATS[cat]
    list_complete, list_partial, list_rel = LIST_CATS[cat]
    out: list[str] = []
    out.append(f"inductive {list_rel} : {list_partial} → {list_complete} → Prop where")
    out.append("  | done {xs} :")
    out.append(f"      {list_rel} ({list_partial}.done xs) xs")
    out.append("  | cutoff {xs} :")
    out.append(f"      {list_rel} {list_partial}.cutoff xs")
    out.append(f"  | elemsDone {{pre : {list_complete}}} {{suffix : {list_complete}}} :")
    out.append(f"      {list_rel} ({list_partial}.elems pre none) (pre ++ suffix)")
    out.append(
        f"  | elemsTail {{pre : {list_complete}}} {{suffix : {list_complete}}} "
        f"{{frontier : {elem_partial}}} {{frontierCompletion : {elem_complete}}} :"
    )
    out.append(f"      {elem_rel} frontier frontierCompletion →")
    out.append(
        f"      {list_rel} ({list_partial}.elems pre (some frontier)) "
        f"(pre ++ frontierCompletion :: suffix)"
    )
    return out


LATEX_SYMBOLS = {
    "cty": r"\tau",
    "cplace": "p",
    "cexpr": "e",
    "cstmt": "s",
    "cblock": "B",
    "cbranch": "r",
    "cparam": "a",
}

TYPE_LATEX = {
    "Ty": r"\tau",
    "Place": "p",
    "Expr": "e",
    "Stmt": "s",
    "Block": "B",
    "Name": "x",
    "Nat": "i",
    "Int": "n",
    "Bool": "b",
    "(Name × Block)": "r",
    "(Name × Ty)": "a",
    "List Ty": r"\overline{\tau}",
    "List Place": r"\overline{p}",
    "List Expr": r"\overline{e}",
    "List Stmt": r"\overline{s}",
    "List Block": r"\overline{B}",
    "List (Name × Block)": r"\overline{r}",
    "List (Name × Ty)": r"\overline{a}",
    "Option (List Stmt)": "W",
}

TOKEN_LATEX = {
    "cty_unit": r"\mathsf{unit}",
    "cty_never": r"\mathsf{never}",
    "cty_bool": r"\mathsf{bool}",
    "cty_int": r"\mathsf{int}",
    "cexpr_unit": "()",
    "cexpr_panic": r"\mathsf{panic}",
    "cexpr_true": r"\mathsf{true}",
    "cexpr_false": r"\mathsf{false}",
    "cexpr_if": r"\kw{if}",
    "cexpr_else": r"\kw{else}",
    "cexpr_match": r"\kw{match}",
    "cexpr_loop": r"\kw{loop}",
    "cstmt_assert": r"\mathsf{assert}",
    "cstmt_let": r"\kw{let}",
    "cstmt_break": r"\kw{break}",
    "cstmt_return": r"\kw{return}",
    "cstmt_fn": r"\mathsf{fun}",
    "=>": r"\Rightarrow",
    "==": r"\mathrel{\mathsf{==}}",
    ":=": ":=",
    "&mut": r"\&\mathsf{mut}",
    "&": r"\&",
    "*": "*",
    "+": "+",
    ".": ".",
    "_": r"\_",
    "(": "(",
    ")": ")",
    "[": "(",
    "]": ")",
    "{": r"\mathopen[",
    "}": r"\mathclose]",
    "<": "(",
    ">": ")",
    ":": ":",
}

PREFIX_TOKEN_LATEX = {
    "cty_": r"\mathsf{{{}}}",
    "cexpr_": r"\mathsf{{{}}}",
    "cstmt_": r"\kw{{{}}}",
}

DISPLAY_CATS = ["cty", "cplace", "cexpr", "cstmt", "cblock", "cbranch", "cparam"]


def latex_hat(symbol: str) -> str:
    return rf"\hat{{{symbol}}}"


def latex_complete_type(typ: str) -> str:
    return TYPE_LATEX[typ]


def latex_partial_type(typ: str) -> str:
    if typ == "PartialName":
        return r"\hat{x}"
    for cat, (_complete, partial, _rel) in CATS.items():
        if typ == partial:
            return latex_hat(LATEX_SYMBOLS[cat])
    for cat, (_complete, partial, _rel) in LIST_CATS.items():
        if typ == partial:
            return rf"\widehat{{{latex_complete_type('List ' + CATS[cat][0])}}}"
    return latex_complete_type(typ)


def latex_complete_field(name: str, typ: str) -> str:
    if typ == "List Stmt" and name in {"body", "thenBody", "elseBody", "wildcard"}:
        return "B"
    if typ == "Name" and name in {"f", "name"}:
        return "f"
    if typ == "Nat" and name == "tag":
        return "i"
    return latex_complete_type(typ)


def latex_atom(elem: Elem, field_name: str | None, field_type: str | None, partial: bool) -> str:
    if elem.raw == "ident":
        base = "f" if field_name in {"f", "name"} else "x"
        return rf"\hat{{{base}}}" if partial else base
    if elem.raw == "num":
        return "n" if field_name == "n" or field_type == "Int" else "i"
    return latex_complete_type(field_type or elem.complete_type)


def latex_token(raw: str) -> str:
    tok = raw[1:-1]
    if tok in TOKEN_LATEX:
        return TOKEN_LATEX[tok]
    for prefix, template in PREFIX_TOKEN_LATEX.items():
        if tok.startswith(prefix):
            return template.format(tok[len(prefix):])
    return rf"\kw{{{tok}}}"


def latex_list_frontier_done(elems: str) -> str:
    return ""


def latex_list_frontier_tail(elems: str, partial_elem: str) -> str:
    return rf"{elems}\,{partial_elem}"


def latex_elem_value(
    elem: Elem,
    field_name: str | None,
    field_type: str | None,
    partial: bool,
) -> str:
    if elem.kind == "token":
        return latex_token(elem.raw)
    if elem.kind == "cat":
        return latex_partial_type(CATS[elem.cat][1]) if partial else latex_complete_field(field_name or "", CATS[elem.cat][0])
    if elem.kind == "list":
        return latex_partial_type(LIST_CATS[elem.cat][1]) if partial else latex_complete_field(field_name or "", f"List {CATS[elem.cat][0]}")
    if elem.kind == "atom":
        return latex_atom(elem, field_name, field_type, partial)
    raise ValueError(elem.kind)


def latex_render_elems(
    prod: Production,
    partial_index: int | None = None,
) -> str:
    parts: list[str] = []
    field_idx = 0
    for i, elem in enumerate(prod.elems):
        field_name = None
        field_type = None
        if elem.kind in ["cat", "atom", "list"]:
            field_name = prod.field_names[field_idx]
            field_type = prod.field_types[field_idx]
            field_idx += 1
        parts.append(latex_elem_value(elem, field_name, field_type, partial_index == i))
        if partial_index == i:
            break
    return latex_cleanup(parts)


def latex_cleanup(parts: list[str]) -> str:
    out = r"\,".join(parts)
    replacements = [
        (r"(\,", "("), (r"\,)", ")"), (r"[\,", "["), (r"\,]", "]"),
        (r"\,.\,", "."), (r"\,:\,", ":"), (r"\,:=\,", ":="),
        (r"\,+\,", "+"), (r"\,,", ","),
        (r"\mathsf{prod}\,", r"\mathsf{prod}"),
        (r"\mathsf{sum}\,", r"\mathsf{sum}"),
        (r"\mathsf{fn}\,", r"\mathsf{fn}"),
        (r"*\," , "*"),
        (r"f\,(", "f("),
        (r"f\square\,(", r"f\square("),
    ]
    for old, new in replacements:
        out = out.replace(old, new)
    return out


def latex_complete_alt(prod: Production) -> str:
    return latex_render_elems(prod)


def latex_partial_alt(rule: Rule) -> str:
    if rule.mode == "token":
        return latex_render_elems(rule.production, rule.index) + r"\square"
    return latex_render_elems(rule.production, rule.index)


def latex_frontier_condition(rule: Rule) -> str:
    elem = rule.production.elems[rule.index]
    if rule.mode == "token":
        return ""
    field = field_name_at(rule.production, rule.index)
    if rule.mode == "cat":
        partial = latex_partial_type(CATS[elem.cat][1])
        complete = latex_complete_field(field, CATS[elem.cat][0])
    elif rule.mode == "list":
        partial = latex_partial_type(LIST_CATS[elem.cat][1])
        complete = latex_complete_field(field, LIST_CATS[elem.cat][0])
    elif rule.mode == "atom" and is_partial_atom(elem):
        partial = latex_atom(elem, field, PARTIAL_ATOMS[elem.raw][0], partial=True)
        complete = latex_complete_field(field, PARTIAL_ATOMS[elem.raw][0])
    else:
        return ""
    return rf"\quad\text{{if }}{partial}\leadsto {complete}"


def latex_join(alts: list[str]) -> str:
    return r"\mid ".join(dict.fromkeys(alts))


def chunked(xs: list[str], n: int) -> list[list[str]]:
    return [xs[i:i + n] for i in range(0, len(xs), n)]


def dedupe(xs: list[str]) -> list[str]:
    return list(dict.fromkeys(xs))


def render_latex_array(rows: list[tuple[str, list[str]]], chunk_size: int = 4) -> list[str]:
    out = [r"\begin{array}{rcl}"]
    rendered_rows: list[tuple[str, str, str]] = []
    for lhs, alts in rows:
        chunks = chunked(list(dict.fromkeys(alts)), chunk_size)
        for i, chunk in enumerate(chunks):
            rhs = latex_join(chunk)
            if i > 0:
                rhs = r"\mid " + rhs
            rendered_rows.append((lhs if i == 0 else "", "::=" if i == 0 else "", rhs))
    for idx, (lhs, rel, rhs) in enumerate(rendered_rows):
        suffix = r"\\" if idx + 1 < len(rendered_rows) else ""
        out.append(rf"  {lhs} &{rel}& {rhs}{suffix}")
    out.append(r"\end{array}")
    return out


def render_partial_latex_array(
    rows: list[tuple[str, list[tuple[Production | None, list[str]]]]],
    chunk_size: int = 3,
) -> list[str]:
    out = [r"\begin{array}{rcl}"]
    rendered_rows: list[tuple[str, str, str]] = []
    for lhs, groups in rows:
        first_for_lhs = True
        seen: set[str] = set()
        for _prod, alts in groups:
            fresh = [alt for alt in alts if alt not in seen]
            seen.update(fresh)
            if not fresh:
                continue
            chunks = chunked(fresh, chunk_size)
            for i, chunk in enumerate(chunks):
                rhs = latex_join(chunk)
                if not first_for_lhs or i > 0:
                    rhs = r"\mid " + rhs
                rendered_rows.append((lhs if first_for_lhs else "", "::=" if first_for_lhs else "", rhs))
                first_for_lhs = False
    for idx, (lhs, rel, rhs) in enumerate(rendered_rows):
        suffix = r"\\" if idx + 1 < len(rendered_rows) else ""
        out.append(rf"  {lhs} &{rel}& {rhs}{suffix}")
    out.append(r"\end{array}")
    return out


def render_completion_latex_array(groups: list[tuple[Production, list[Rule]]]) -> list[str]:
    out = [r"\begin{array}{rcl}"]
    grouped_rows: OrderedDict[str, list[str]] = OrderedDict()
    for prod, prod_rules in groups:
        for rule in prod_rules:
            lhs = latex_partial_alt(rule)
            rhs = latex_complete_alt(prod)
            condition = latex_frontier_condition(rule)
            grouped_rows.setdefault(lhs, []).append(rhs + condition)
    rows: list[tuple[str, str, str]] = []
    for lhs, rhss in grouped_rows.items():
        unique_rhss = dedupe(rhss)
        rows.append((lhs, r"\leadsto", unique_rhss[0]))
        for rhs in unique_rhss[1:]:
            rows.append((r"\text{or}\quad " + lhs, r"\leadsto", rhs))
    for idx, (lhs, rel, rhs) in enumerate(rows):
        suffix = r"\\" if idx + 1 < len(rows) else ""
        out.append(rf"  {lhs} &{rel}& {rhs}{suffix}")
    out.append(r"\end{array}")
    return out


def generate_latex_completions() -> str:
    productions = parse_syntax_rules()
    _states, rules = derive_states(productions)
    grouped: list[tuple[Production, list[Rule]]] = []
    for prod in productions:
        if prod.target_cat not in DISPLAY_CATS:
            continue
        prod_rules = [
            rule for rule in rules[prod.target_cat]
            if rule.production is prod
            and (rule.mode != "atom" or is_partial_atom(rule.production.elems[rule.index]))
        ]
        if prod_rules:
            grouped.append((prod, prod_rules))

    list_rows = []
    for cat in used_list_cats(productions):
        if cat not in DISPLAY_CATS and cat != "cbranch" and cat != "cparam":
            continue
        elems = latex_complete_type(LIST_CATS[cat][0])
        elem = latex_complete_type(CATS[cat][0])
        partial_elem = latex_partial_type(CATS[cat][1])
        list_rows.append((
            latex_list_frontier_tail(elems, partial_elem),
            r"\leadsto",
            rf"{elems}\circ{{}}\mathopen[{elem}\mathclose]\circ{{}}S\quad\text{{if }}{partial_elem}\leadsto {elem}",
        ))

    lines = [
        "% Generated by scripts/generate_partial_from_syntax.py from",
        "% formalization/ConservativeExtractor/CompleteProgram.lean.",
        "% Do not edit by hand.",
        r"\[",
    ]
    lines.extend(render_completion_latex_array(grouped))
    lines.extend([
        r"\]",
        r"Here $S$ ranges over arbitrary complete suffixes of the corresponding list category.",
        r"\[",
        r"\begin{array}{rcl}",
    ])
    for idx, (lhs, rel, rhs) in enumerate(list_rows):
        suffix = r"\\" if idx + 1 < len(list_rows) else ""
        lines.append(rf"  {lhs} &{rel}& {rhs}{suffix}")
    lines.extend([
        r"\end{array}",
        r"\]",
    ])
    return "\n".join(lines)


def generate_latex() -> str:
    productions = parse_syntax_rules()
    _states, rules = derive_states(productions)
    by_cat: dict[str, list[Production]] = {cat: [] for cat in CATS}
    for prod in productions:
        by_cat[prod.target_cat].append(prod)

    complete_rows = [
        (LATEX_SYMBOLS[cat], [latex_complete_alt(prod) for prod in by_cat[cat]])
        for cat in DISPLAY_CATS
    ]

    partial_rows = []
    for cat in DISPLAY_CATS:
        symbol = LATEX_SYMBOLS[cat]
        groups: list[tuple[Production | None, list[str]]] = [(None, [r"\square", symbol])]
        for prod in by_cat[cat]:
            alts = [
                latex_partial_alt(rule)
                for rule in rules[cat]
                if rule.production is prod
                and (rule.mode != "atom" or is_partial_atom(rule.production.elems[rule.index]))
            ]
            if alts:
                groups.append((prod, alts))
        partial_rows.append((latex_hat(symbol), groups))

    list_rows = []
    for cat in used_list_cats(productions):
        if cat not in DISPLAY_CATS and cat != "cbranch" and cat != "cparam":
            continue
        elems = latex_complete_type(LIST_CATS[cat][0])
        partial_elem = latex_partial_type(CATS[cat][1])
        lhs = latex_partial_type(LIST_CATS[cat][1])
        list_rows.append((lhs, [r"\square", elems, latex_list_frontier_tail(elems, partial_elem)]))

    lines = [
        "% Generated by scripts/generate_partial_from_syntax.py from",
        "% formalization/ConservativeExtractor/CompleteProgram.lean.",
        "% Do not edit by hand.",
        r"\[",
    ]
    lines.extend(render_latex_array(complete_rows, chunk_size=4))
    lines.extend([
        r"\]",
        "",
        r"We write partial forms with hats:",
        r"\[",
    ])
    lines.extend(render_partial_latex_array(partial_rows, chunk_size=3))
    lines.extend([
        r"\]",
        r"The generated list-frontier forms used above are:",
        r"\[",
    ])
    lines.extend(render_latex_array(list_rows))
    lines.extend([r"\]"])
    return "\n".join(lines)


def field_name_at(prod: Production, index: int) -> str:
    for i, _elem, name, _typ in field_elems(prod):
        if i == index:
            return name
    raise KeyError(index)


def binder_group(fields: list[tuple[str, str]]) -> str:
    return "".join(f" {{{name} : {typ}}}" for name, typ in fields)


def generate() -> str:
    productions = parse_syntax_rules()
    states, rules = derive_states(productions)
    origins = state_origins(rules)
    list_cats = used_list_cats(productions)
    lines: list[str] = []
    lines.append("inductive PartialName where")
    lines.append("  | cutoff")
    lines.append("  | done (x : Name)")
    lines.append("  | prefix (x : Name)")
    lines.append("  deriving Repr")
    lines.append("")
    lines.append("mutual")
    lines.append("")
    for idx, cat in enumerate(list_cats):
        if idx:
            lines.append("")
        lines.extend(render_list_inductive(cat))
    if list_cats:
        lines.append("")
    for idx, cat in enumerate(CATS):
        if idx:
            lines.append("")
        lines.extend(render_inductive(cat, states[cat], origins[cat]))
    lines.append("")
    lines.append("end")
    lines.append("")
    lines.append("abbrev PartialProgram := PartialBlock")
    lines.append("")
    lines.append("inductive CompletesName : PartialName → Name → Prop where")
    lines.append("  | done {x} :")
    lines.append("      CompletesName (PartialName.done x) x")
    lines.append("  | cutoff {x} :")
    lines.append("      CompletesName PartialName.cutoff x")
    lines.append("  | prefix {x y} :")
    lines.append("      CompletesName (PartialName.prefix x) y")
    lines.append("")
    lines.append("mutual")
    lines.append("")
    for idx, cat in enumerate(list_cats):
        if idx:
            lines.append("")
        lines.extend(render_list_relation(cat))
    if list_cats:
        lines.append("")
    for idx, cat in enumerate(CATS):
        complete, partial, rel = CATS[cat]
        if idx:
            lines.append("")
        lines.append(f"inductive {rel} : {partial} → {complete} → Prop where")
        lines.append("  | done {x} :")
        lines.append(f"      {rel} ({partial}.done x) x")
        lines.append(f"  | cutoff {{x}} :")
        lines.append(f"      {rel} {partial}.cutoff x")
        last_prod: str | None = None
        for rule in rules[cat]:
            if rule.production.name != last_prod:
                lines.append(f"  -- derived from: {describe_production(rule.production)}")
                last_prod = rule.production.name
            lines.extend(render_rule(rule))
    lines.append("")
    lines.append("end")
    return "\n".join(lines)


def write_outputs() -> dict[Path, str]:
    rendered = generate()
    template = TEMPLATE.read_text()
    if MARKER not in template:
        raise ValueError(f"template marker missing: {MARKER}")
    return {
        OUTPUT: template.replace(MARKER, rendered),
        LATEX_OUTPUT: generate_latex(),
        LATEX_COMPLETIONS_OUTPUT: generate_latex_completions(),
    }


def main() -> None:
    outputs = write_outputs()
    if sys.argv[1:] == ["--check"]:
        stale = [path for path, content in outputs.items() if path.read_text() != content]
        if stale:
            for path in stale:
                print(f"stale generated file: {path.relative_to(ROOT)}")
            raise SystemExit(1)
        return
    if sys.argv[1:]:
        raise SystemExit(f"usage: {Path(sys.argv[0]).name} [--check]")
    for path, content in outputs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)


if __name__ == "__main__":
    main()
