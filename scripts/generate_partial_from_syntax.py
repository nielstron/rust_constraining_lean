from __future__ import annotations

import re
from collections import OrderedDict
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "FWRust" / "Sealor" / "CompleteProgram.lean"
TEMPLATE = ROOT / "FWRust" / "Sealor" / "Template" / "PartialProgram.lean"
OUTPUT = ROOT / "FWRust" / "Sealor" / "Generated" / "PartialProgram.lean"
MARKER = "/-- INSERT GRAMMAR HERE --/"


CATS = {
    "cty": ("Ty", "PartialTy", "CompletesTy"),
    "clval": ("LVal", "PartialLVal", "CompletesLVal"),
    "cterm": ("Term", "PartialTerm", "CompletesTerm"),
}

LIST_CATS = {
    "clval": ("List LVal", "PartialLVals", "CompletesLVals"),
    "cterm": ("List Term", "PartialTerms", "CompletesTerms"),
}

ATOM_TYPES = {
    "ident": "Name",
    "num": "Int",
    "term": "Lifetime",
}

PARTIAL_ATOMS = {
    "ident": ("Name", "PartialName", "CompletesName"),
}


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
            return LIST_CATS[self.cat][0]
        return ATOM_TYPES[self.raw]

    @property
    def partial_type(self) -> str | None:
        if self.kind == "cat":
            return CATS[self.cat][1]
        if self.kind == "list":
            return LIST_CATS[self.cat][1]
        if self.kind == "atom" and self.raw in PARTIAL_ATOMS:
            return PARTIAL_ATOMS[self.raw][1]
        return None


@dataclass(frozen=True)
class Production:
    name: str
    target_cat: str
    elems: list[Elem]
    ast: str
    field_names: list[str]
    field_types: list[str]


@dataclass(frozen=True)
class Rule:
    production: Production
    state_name: str
    fields: list[tuple[str, str]]
    index: int | None
    prefix_len: int | None = None
    field_map: tuple[tuple[str, str], ...] = ()


def cap(s: str) -> str:
    return s[:1].upper() + s[1:]


def lower(s: str) -> str:
    return s[:1].lower() + s[1:]


def tokenize(body: str) -> list[str]:
    return re.findall(r'"[^"]*"|\S+', body)


def split_top_level_words(src: str) -> list[str]:
    return [word for word in src.strip().split() if word]


def parse_param_groups(src: str) -> list[tuple[str, str]]:
    fields: list[tuple[str, str]] = []
    for names, typ in re.findall(r"\(([^:]+?)\s*:\s*([^)]+)\)", src):
        for name in split_top_level_words(names):
            fields.append((name, typ.strip()))
    return fields


def ctor_rhs_to_template(rhs: str, fields: list[tuple[str, str]]) -> str:
    out = rhs.strip()
    for name, _typ in fields:
        out = re.sub(rf"\b{re.escape(name)}\b", "{" + name + "}", out)
    return out


def parse_ctor_specs() -> dict[str, tuple[str, list[tuple[str, str]]]]:
    text = SOURCE.read_text()
    block_match = re.search(r"namespace SyntaxCtor(?P<body>.*?)end SyntaxCtor", text, re.S)
    if not block_match:
        raise ValueError("missing namespace SyntaxCtor in complete syntax file")
    body = block_match.group("body")
    pattern = re.compile(
        r"abbrev\s+(?P<name>\w+)_ctor\s*"
        r"(?P<params>(?:\([^)]*\)\s*)*)"
        r":\s*(?P<ret>[^\n]+?)\s*:=\s*"
        r"(?P<rhs>.*?)(?=\n\s*\n|$)",
        re.S,
    )
    specs: dict[str, tuple[str, list[tuple[str, str]]]] = {}
    for match in pattern.finditer(body):
        name = match.group("name")
        fields = parse_param_groups(match.group("params"))
        args = " ".join("{" + field + "}" for field, _ in fields)
        ast = f"SyntaxCtor.{name}_ctor" + (f" {args}" if args else "")
        specs[name] = (ast, fields)
    return specs


def parse_elem(tok: str) -> Elem:
    if tok.startswith('"'):
        return Elem("token", tok)
    if tok.endswith(",*"):
        cat = tok[:-2]
        if cat not in LIST_CATS:
            raise ValueError(f"no list grammar for syntax category {cat!r}")
        return Elem("list", tok, cat)
    if tok in CATS:
        return Elem("cat", tok, tok)
    if tok in ATOM_TYPES:
        return Elem("atom", tok)
    raise ValueError(f"unsupported syntax token: {tok}")


def parse_syntax_rules() -> list[Production]:
    pattern = re.compile(r"^syntax \(name := ([^)]+)\) (.*) : (\w+)$")
    ctor_specs = parse_ctor_specs()
    out: list[Production] = []
    for line in SOURCE.read_text().splitlines():
        m = pattern.match(line.strip())
        if not m:
            continue
        name, body, target_cat = m.groups()
        if target_cat not in CATS:
            continue
        if name not in ctor_specs:
            raise KeyError(f"missing checked SyntaxCtor annotation for syntax rule {name}")
        ast, fields = ctor_specs[name]
        elems = [parse_elem(tok) for tok in tokenize(body)]
        field_elems = [elem for elem in elems if elem.kind in {"cat", "list", "atom"}]
        if len(field_elems) != len(fields):
            raise ValueError(
                f"{name}: syntax has {len(field_elems)} fields but AST spec has {len(fields)}"
            )
        out.append(
            Production(
                name=name,
                target_cat=target_cat,
                elems=elems,
                ast=ast,
                field_names=[field for field, _ in fields],
                field_types=[typ for _, typ in fields],
            )
        )
    return out


def field_elems(prod: Production) -> list[tuple[int, Elem, str, str]]:
    out: list[tuple[int, Elem, str, str]] = []
    field_idx = 0
    for i, elem in enumerate(prod.elems):
        if elem.kind not in {"cat", "list", "atom"}:
            continue
        out.append((i, elem, prod.field_names[field_idx], prod.field_types[field_idx]))
        field_idx += 1
    return out


def fields_before(prod: Production, index: int) -> list[tuple[str, str]]:
    return [(name, typ) for i, _elem, name, typ in field_elems(prod) if i < index]


def fields_after(prod: Production, index: int) -> list[tuple[str, str]]:
    return [(name, typ) for i, _elem, name, typ in field_elems(prod) if i > index]


def fields_from(prod: Production, index: int) -> list[tuple[str, str]]:
    return [(name, typ) for i, _elem, name, typ in field_elems(prod) if i >= index]


def field_name_at(prod: Production, index: int) -> str:
    for i, _elem, name, _typ in field_elems(prod):
        if i == index:
            return name
    raise KeyError((prod.name, index))


def partial_field_type(elem: Elem, complete_type: str) -> str:
    return elem.partial_type or complete_type


def state_base(prod: Production) -> str:
    for prefix in CATS:
        if prod.name.startswith(prefix):
            return lower(prod.name[len(prefix) :])
    return lower(prod.name)


def state_name(prod: Production, elem: Elem, field_name: str, index: int) -> str:
    if prod.name == "ctyBorrowShared":
        return "borrowSharedTargets"
    if prod.name == "ctyBorrowMut":
        return "borrowMutTargets"
    if prod.name == "ctermBorrowShared":
        return "borrowSharedOperand"
    if prod.name == "ctermBorrowMut":
        return "borrowMutOperand"
    if prod.name == "ctermLetMut" and field_name == "initialiser":
        return "letMutRhs"
    if (
        prod.target_cat == "cterm"
        and elem.kind == "cat"
        and elem.cat == "clval"
        and index == 0
        and prod.name in {"ctermAssign", "ctermMove"}
    ):
        return "lvalStart"
    if prod.target_cat == "cterm" and elem.kind == "cat" and elem.cat == "cterm" and index == 0:
        return "termPrefix"
    return f"{state_base(prod)}{cap(field_name)}"


def state_fields(
    prod: Production,
    index: int,
    elem: Elem,
    field_name: str,
    field_type: str,
) -> tuple[list[tuple[str, str]], tuple[tuple[str, str], ...]]:
    fields = fields_before(prod, index)
    rendered_field_name = field_name
    if prod.name == "ctermLetMut" and field_name == "initialiser":
        rendered_field_name = "term"
    if (
        prod.target_cat == "cterm"
        and elem.kind == "cat"
        and elem.cat == "clval"
        and index == 0
        and prod.name in {"ctermAssign", "ctermMove"}
    ):
        rendered_field_name = "lval"
    out = fields + [(rendered_field_name, partial_field_type(elem, field_type))]
    field_map = tuple((name, name) for name, _typ in fields) + ((field_name, rendered_field_name),)
    return out, field_map


def start_state_name(prod: Production) -> str:
    return f"{state_base(prod)}Start"


def token_text(raw: str) -> str:
    if raw.startswith('"') and raw.endswith('"'):
        return raw[1:-1]
    return raw


def token_name(raw: str) -> str:
    text = token_text(raw)
    names = {
        "&": "Amp",
        "&mut": "Ampmut",
        "*": "Star",
        "()": "Unit",
        ":=": "Assign",
        "==": "Eq",
        "{": "Lbrace",
        "}": "Rbrace",
    }
    if text in names:
        return names[text]
    pieces = re.findall(r"[A-Za-z0-9]+", text)
    return "".join(cap(piece) for piece in pieces) or "Token"


def token_prefix_state_name(raw: str) -> str:
    return f"token{token_name(raw)}Start"


def elem_label(elem: Elem) -> str:
    if elem.kind == "token":
        return token_text(elem.raw)
    if elem.kind == "cat":
        return {
            "cty": "ty",
            "clval": "lval",
            "cterm": "term",
        }[elem.cat]
    if elem.kind == "list":
        return {
            "clval": "lvals",
            "cterm": "terms",
        }[elem.cat]
    if elem.kind == "atom":
        return {
            "ident": "name",
            "num": "num",
            "term": "lifetime",
        }[elem.raw]
    raise ValueError(elem)


def elem_surface(elem: Elem) -> str:
    if elem.kind == "list":
        return {
            "clval": "lval,*",
            "cterm": "term,*",
        }[elem.cat]
    return elem_label(elem)


def partial_surface(elems: list[Elem]) -> str:
    parts = [elem_surface(elem) for elem in elems]
    return " ".join(parts + ["..."]) if parts else "..."


def field_base_name(elem: Elem) -> str:
    return elem_label(elem)


def unique_field_name(base: str, counts: dict[str, int]) -> str:
    seen = counts.get(base, 0) + 1
    counts[base] = seen
    return base if seen == 1 else f"{base}{seen}"


def prefix_key(prod: Production, prefix_len: int) -> tuple[tuple[str, str | None], ...]:
    return tuple((elem.kind, elem.cat if elem.cat is not None else elem.raw)
        for elem in prod.elems[:prefix_len])


def prefix_fields(prod: Production, prefix_len: int) -> tuple[list[tuple[str, str]], tuple[tuple[str, str], ...]]:
    fields: list[tuple[str, str]] = []
    field_map: list[tuple[str, str]] = []
    counts: dict[str, int] = {}
    for i, elem, original_name, typ in field_elems(prod):
        if i >= prefix_len:
            continue
        generic_name = unique_field_name(field_base_name(elem), counts)
        fields.append((generic_name, typ))
        field_map.append((original_name, generic_name))
    return fields, tuple(field_map)


def prefix_state_name(prod: Production, prefix_len: int, ambiguous: bool) -> str:
    prefix = prod.elems[:prefix_len]
    if prefix_len == 1 and prefix[0].kind == "token":
        return token_prefix_state_name(prefix[0].raw) if ambiguous else start_state_name(prod)
    if prefix_len == 1 and prefix[0].kind in {"cat", "list", "atom"}:
        return f"{field_base_name(prefix[0])}Start"
    return f"{state_base(prod)}Prefix{prefix_len}"


def prefix_is_partial_field_frontier(prod: Production, prefix_len: int) -> bool:
    last_index = prefix_len - 1
    return any(
        i == last_index and elem.partial_type is not None
        for i, elem, _name, _typ in field_elems(prod)
    )


def add_state(
    states: OrderedDict[str, list[tuple[str, str]]],
    name: str,
    fields: list[tuple[str, str]],
) -> None:
    old = states.get(name)
    if old is not None and old != fields:
        raise ValueError(f"state {name} has incompatible fields: {old} vs {fields}")
    states.setdefault(name, fields)


def derive_states(
    productions: list[Production],
) -> tuple[dict[str, OrderedDict[str, list[tuple[str, str]]]], dict[str, list[Rule]]]:
    states = {cat: OrderedDict() for cat in CATS}
    rules = {cat: [] for cat in CATS}
    first_token_prods: dict[str, dict[str, list[Production]]] = {cat: {} for cat in CATS}
    prefix_prods: dict[str, dict[tuple[tuple[str, str | None], ...], list[tuple[Production, int]]]] = {
        cat: {} for cat in CATS
    }
    for prod in productions:
        prod_fields = field_elems(prod)
        if prod_fields and prod.elems[0].kind == "token":
            first_token_prods[prod.target_cat].setdefault(prod.elems[0].raw, []).append(prod)
        for prefix_len in range(1, len(prod.elems) + 1):
            if prefix_len == 1 and prod.elems[0].kind == "token":
                continue
            if prefix_is_partial_field_frontier(prod, prefix_len):
                continue
            prefix_prods[prod.target_cat].setdefault(
                prefix_key(prod, prefix_len), []
            ).append((prod, prefix_len))
        for i, elem, fname, ftype in prod_fields:
            if elem.kind == "atom" and elem.raw == "term":
                continue
            sname = state_name(prod, elem, fname, i)
            fields, field_map = state_fields(prod, i, elem, fname, ftype)
            add_state(states[prod.target_cat], sname, fields)
            rules[prod.target_cat].append(Rule(prod, sname, fields, i, field_map=field_map))
    for cat, by_token in first_token_prods.items():
        for token, exact_prods in by_token.items():
            token_prefix = token_text(token)
            alternatives = [
                alt
                for other_token, prods in by_token.items()
                if token_text(other_token).startswith(token_prefix)
                for alt in prods
            ]
            ambiguous = len({alt.name for alt in exact_prods}) > 1 or (
                len({alt.name for alt in alternatives}) > len({alt.name for alt in exact_prods})
            )
            sname = token_prefix_state_name(token) if ambiguous else start_state_name(exact_prods[0])
            fields: list[tuple[str, str]] = []
            add_state(states[cat], sname, fields)
            for alt in alternatives if ambiguous else exact_prods:
                rules[cat].append(Rule(alt, sname, fields, None))
    for cat, by_prefix in prefix_prods.items():
        for _key, prods in by_prefix.items():
            if len({prod.name for prod, _prefix_len in prods}) < 2:
                continue
            first_prod, first_prefix_len = prods[0]
            fields, _field_map = prefix_fields(first_prod, first_prefix_len)
            sname = prefix_state_name(first_prod, first_prefix_len, True)
            add_state(states[cat], sname, fields)
            for prod, prefix_len in prods:
                prod_fields, field_map = prefix_fields(prod, prefix_len)
                if prod_fields != fields:
                    raise ValueError(
                        f"prefix state {sname} has incompatible fields: {fields} vs {prod_fields}"
                    )
                rules[cat].append(
                    Rule(prod, sname, fields, None, prefix_len, field_map)
                )

    # A bare lvalue is itself a complete term via move, so the same `lval ...`
    # frontier can also be completed as the left-hand side of equality.
    # This extra realization is not visible from the declarative grammar:
    # `ctermEq` starts with a `cterm`, while the parser shares its initial
    # lvalue frontier with move and assignment.
    if any(prod.name == "ctermEq" for prod in productions):
        lval_eq_prod = Production(
            name="ctermEq",
            target_cat="cterm",
            elems=[
                Elem("cat", "clval", "clval"),
                Elem("token", '"=="'),
                Elem("cat", "cterm", "cterm"),
            ],
            ast="SyntaxCtor.ctermEq_ctor (SyntaxCtor.ctermMove_ctor {lval}) {rhs}",
            field_names=["lval", "rhs"],
            field_types=["LVal", "Term"],
        )
        lval_fields = [("lval", "PartialLVal")]
        add_state(states["cterm"], "lvalStart", lval_fields)
        rules["cterm"].append(
            Rule(
                lval_eq_prod,
                "lvalStart",
                lval_fields,
                0,
                field_map=(("lval", "lval"),),
            )
        )

    return states, rules


def origin_comment(prod: Production) -> str:
    return prod.ast


def rule_partial_surface(rule: Rule) -> str:
    if rule.prefix_len is not None:
        return partial_surface(rule.production.elems[: rule.prefix_len])
    if rule.index is None:
        return partial_surface(rule.production.elems[:1])
    return partial_surface(rule.production.elems[: rule.index + 1])


def render_list_inductive(cat: str) -> list[str]:
    complete, partial, _rel = LIST_CATS[cat]
    item_type = CATS[cat][0]
    item_partial = CATS[cat][1]
    return [
        f"inductive {partial} where",
        "  | cutoff",
        f"  | done (xs : {complete})",
        f"  | elems (pre : {complete}) (tail : Option {item_partial})",
        "  deriving Repr",
    ]


def render_inductive(
    cat: str,
    states: OrderedDict[str, list[tuple[str, str]]],
    metadata: dict[str, dict[str, list[str]]],
) -> list[str]:
    complete, partial, _rel = CATS[cat]
    lines = [f"inductive {partial} where"]
    lines.append("  | cutoff")
    lines.append(f"  | done (x : {complete})")
    for name, fields in states.items():
        meta = metadata[name]
        for surface in meta["surfaces"]:
            lines.append(f"  -- partial syntax: `{surface}`")
        for origin in meta["origins"]:
            lines.append(f"  -- derived from: {origin}")
        args = "".join(f" ({fname} : {fty})" for fname, fty in fields)
        lines.append(f"  | {name}{args}")
    lines.append("  deriving Repr")
    return lines


def subst(template: str, values: dict[str, str]) -> str:
    out = template
    for key, value in values.items():
        out = out.replace("{" + key + "}", value)
    return out


def paren(s: str) -> str:
    if s.startswith(".") or " " not in s:
        return s
    return f"({s})"


def partial_app(partial: str, state_name: str, fields: list[tuple[str, str]]) -> str:
    args = " ".join(paren(name) for name, _ in fields)
    return f"{partial}.{state_name}" + (f" {args}" if args else "")


def render_rule(rule: Rule) -> list[str]:
    prod = rule.production
    complete, partial, rel = CATS[prod.target_cat]
    if rule.prefix_len is not None:
        names = {original: generic for original, generic in rule.field_map}
        binders = list(rule.fields)
        for name, typ in fields_from(prod, rule.prefix_len):
            binders.append((name, typ))
            names[name] = name
        partial_src = partial_app(partial, rule.state_name, rule.fields)
        complete_src = subst(prod.ast, names)
        binders_src = "".join(f" {{{name} : {typ}}}" for name, typ in binders)
        lines = [f"  | {prod.name}_{rule.state_name}{binders_src} :"]
        lines.append(f"      {rel} ({partial_src}) ({complete_src})")
        return lines

    if rule.index is None:
        names: dict[str, str] = {}
        binders = field_elems_after_start(prod)
        premises: list[str] = []
        partial_src = partial_app(partial, rule.state_name, rule.fields)
        complete_src = subst(prod.ast, {name: name for name, _ in binders})
        binders_src = "".join(f" {{{name} : {typ}}}" for name, typ in binders)
        lines = [f"  | {prod.name}_{rule.state_name}{binders_src} :"]
        lines.append(f"      {rel} ({partial_src}) ({complete_src})")
        return lines

    elem = prod.elems[rule.index]
    fname = field_name_at(prod, rule.index)
    rendered_names = {original: rendered for original, rendered in rule.field_map}
    partial_name = rendered_names.get(fname, fname)
    names = {
        original: rendered
        for original, rendered in rule.field_map
        if original != fname
    }
    binders = list(rule.fields)
    premises: list[str] = []

    if elem.kind == "cat":
        completed = f"{partial_name}'"
        binders.append((completed, CATS[elem.cat][0]))
        premises.append(f"{CATS[elem.cat][2]} {partial_name} {completed}")
        names[fname] = completed
    elif elem.kind == "list":
        completed = f"{partial_name}'"
        binders.append((completed, LIST_CATS[elem.cat][0]))
        premises.append(f"{LIST_CATS[elem.cat][2]} {partial_name} {completed}")
        names[fname] = completed
    elif elem.kind == "atom" and elem.raw in PARTIAL_ATOMS:
        completed = f"{partial_name}'"
        complete_type, _partial, atom_rel = PARTIAL_ATOMS[elem.raw]
        binders.append((completed, complete_type))
        premises.append(f"{atom_rel} {partial_name} {completed}")
        names[fname] = completed
    else:
        names[fname] = partial_name

    for name, typ in fields_after(prod, rule.index):
        binders.append((name, typ))
        names[name] = name

    binders_src = "".join(f" {{{name} : {typ}}}" for name, typ in binders)
    partial_src = partial_app(partial, rule.state_name, rule.fields)
    complete_src = subst(prod.ast, names)
    lines = [f"  | {prod.name}_{rule.state_name}{binders_src} :"]
    for premise in premises:
        lines.append(f"      {premise} →")
    lines.append(f"      {rel} ({partial_src}) ({complete_src})")
    return lines


def render_list_relation(cat: str) -> list[str]:
    complete, partial, rel = LIST_CATS[cat]
    item_complete, item_partial, item_rel = CATS[cat]
    return [
        f"inductive {rel} : {partial} → {complete} → Prop where",
        "  | done {xs} :",
        f"      {rel} ({partial}.done xs) xs",
        "  | cutoff {xs} :",
        f"      {rel} {partial}.cutoff xs",
        f"  | elemsDone {{pre suffix : {complete}}} :",
        f"      {rel} ({partial}.elems pre none) (pre ++ suffix)",
        f"  | elemsTail {{pre suffix : {complete}}} {{frontier : {item_partial}}}",
        f"      {{frontierCompletion : {item_complete}}} :",
        f"      {item_rel} frontier frontierCompletion →",
        f"      {rel} ({partial}.elems pre (some frontier))",
        "        (pre ++ frontierCompletion :: suffix)",
    ]


def render_relation(cat: str, rules: list[Rule]) -> list[str]:
    complete, partial, rel = CATS[cat]
    lines = [
        f"inductive {rel} : {partial} → {complete} → Prop where",
        "  | done {x} :",
        f"      {rel} ({partial}.done x) x",
        "  | cutoff {x} :",
        f"      {rel} {partial}.cutoff x",
    ]
    for rule in rules:
        lines.append(f"  -- partial syntax: `{rule_partial_surface(rule)}`")
        lines.append(f"  -- derived from: {origin_comment(rule.production)}")
        lines.extend(render_rule(rule))
    return lines


def field_elems_after_start(prod: Production) -> list[tuple[str, str]]:
    return [(name, typ) for _i, _elem, name, typ in field_elems(prod)]


def add_unique(xs: list[str], x: str) -> None:
    if x not in xs:
        xs.append(x)


def state_metadata(rules: dict[str, list[Rule]]) -> dict[str, dict[str, dict[str, list[str]]]]:
    out = {cat: {} for cat in CATS}
    for cat, cat_rules in rules.items():
        for rule in cat_rules:
            meta = out[cat].setdefault(rule.state_name, {"surfaces": [], "origins": []})
            add_unique(meta["surfaces"], rule_partial_surface(rule))
            add_unique(meta["origins"], origin_comment(rule.production))
    return out


def validate_generated_metadata(
    productions: list[Production],
    metadata: dict[str, dict[str, dict[str, list[str]]]],
    rules: dict[str, list[Rule]],
) -> None:
    for cat, states in metadata.items():
        surface_to_state: dict[str, str] = {}
        for state, meta in states.items():
            for surface in meta["surfaces"]:
                previous = surface_to_state.get(surface)
                if previous is not None and previous != state:
                    raise ValueError(
                        f"{cat}: partial syntax {surface!r} is generated by "
                        f"both {previous} and {state}"
                    )
                surface_to_state[surface] = state

    relation_origins = {
        cat: {(rule.state_name, origin_comment(rule.production)) for rule in cat_rules}
        for cat, cat_rules in rules.items()
    }
    for cat, states in metadata.items():
        for state, meta in states.items():
            for origin in meta["origins"]:
                if (state, origin) not in relation_origins[cat]:
                    raise ValueError(
                        f"{cat}: state {state} has derived-from comment {origin!r} "
                        "without a completion rule"
                    )

def render_generated() -> str:
    productions = parse_syntax_rules()
    used_list_cats = {
        elem.cat
        for prod in productions
        for elem in prod.elems
        if elem.kind == "list"
    }
    states, rules = derive_states(productions)
    metadata = state_metadata(rules)
    validate_generated_metadata(productions, metadata, rules)

    lines: list[str] = [
        "inductive PartialName where",
        "  | cutoff",
        "  | done (x : Name)",
        "  | prefix (x : Name)",
        "  deriving Repr",
        "",
        "mutual",
        "",
    ]
    for cat in LIST_CATS:
        if cat not in used_list_cats:
            continue
        lines.extend(render_list_inductive(cat))
        lines.append("")
    for cat in CATS:
        lines.extend(render_inductive(cat, states[cat], metadata[cat]))
        lines.append("")
    lines.extend(
        [
            "end",
            "",
            "abbrev PartialProgram := PartialTerm",
            "",
            "inductive CompletesName : PartialName → Name → Prop where",
            "  | done {x} :",
            "      CompletesName (PartialName.done x) x",
            "  | cutoff {x} :",
            "      CompletesName PartialName.cutoff x",
            "  | prefix {x y} :",
            "      CompletesName (PartialName.prefix x) y",
            "",
            "mutual",
            "",
        ]
    )
    for cat in LIST_CATS:
        if cat not in used_list_cats:
            continue
        lines.extend(render_list_relation(cat))
        lines.append("")
    for cat in CATS:
        lines.extend(render_relation(cat, rules[cat]))
        lines.append("")
    lines.append("end")
    return "\n".join(lines).rstrip() + "\n"


def main() -> None:
    template = TEMPLATE.read_text()
    if MARKER not in template:
        raise ValueError(f"missing marker {MARKER!r} in {TEMPLATE}")
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(template.replace(MARKER, render_generated()))


if __name__ == "__main__":
    main()
