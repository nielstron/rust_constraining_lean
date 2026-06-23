import LwRust.Extractor.CompleteProgram

/-!
Grammar-derived parser frontiers.

This file is a first, isolated version of the "partial program as parser
frontier" model.  It deliberately does not replace
`LwRust.Extractor.Generated.PartialProgram` yet; the existing extractor proofs
still use that representation.

The trusted part here is a small grammar semantics:

* `Derives G cat tokens tree` says that grammar `G` parses `tokens` as category
  `cat`, yielding a generic parse tree.
* `Item` is a dotted production, generated from a grammar rule and a dot
  position.
* `FrontierCompletes G cat prefix tree` says that the parser frontier after
  `prefix` can be completed to `tree`.

The key point is that continuations are derived from *all* grammar positions.
If `cterm` can be followed by `== cterm`, or if `clval` can be followed by
`:= cterm`, both are just dotted items generated from grammar productions.
-/

namespace ConservativeExtractor
namespace GrammarFrontier

inductive Sym (Cat Terminal : Type) where
  | token (terminal : Terminal)
  | cat (cat : Cat)
  deriving Repr, DecidableEq

structure Rule (Cat Terminal : Type) where
  name : String
  lhs : Cat
  rhs : List (Sym Cat Terminal)
  deriving Repr, DecidableEq

structure Grammar (Cat Terminal Tok : Type) where
  rules : List (Rule Cat Terminal)
  accepts : Terminal → Tok → Prop

inductive Tree (Tok : Type) where
  | token (tok : Tok)
  | node (ruleName : String) (children : List (Tree Tok))
  deriving Repr

namespace Tree

def tokens {Tok : Type} : Tree Tok → List Tok
  | .token tok => [tok]
  | .node _ children => children.flatMap tokens

end Tree

theorem tree_sizeOf_lt_sizeOf_append_cons {Tok : Type}
    (done future : List (Tree Tok)) (child : Tree Tok) :
    sizeOf child < sizeOf (done ++ child :: future) := by
  induction done with
  | nil =>
      simp
      omega
  | cons head done ih =>
      simp [List.cons_append]
      omega

mutual

inductive Derives {Cat Terminal Tok : Type} (G : Grammar Cat Terminal Tok) :
    Cat → List Tok → Tree Tok → Prop where
  | rule {cat : Cat} {tokens : List Tok} {children : List (Tree Tok)}
      {rule : Rule Cat Terminal} :
      rule ∈ G.rules →
      rule.lhs = cat →
      DerivesSeq G rule.rhs tokens children →
      Derives G cat tokens (.node rule.name children)

inductive DerivesSeq {Cat Terminal Tok : Type} (G : Grammar Cat Terminal Tok) :
    List (Sym Cat Terminal) → List Tok → List (Tree Tok) → Prop where
  | nil :
      DerivesSeq G [] [] []
  | token {terminal : Terminal} {tok : Tok}
      {rest : List (Sym Cat Terminal)}
      {tokens : List Tok} {children : List (Tree Tok)} :
      G.accepts terminal tok →
      DerivesSeq G rest tokens children →
      DerivesSeq G (.token terminal :: rest) (tok :: tokens)
        (.token tok :: children)
  | cat {cat : Cat} {rest : List (Sym Cat Terminal)}
      {catTokens restTokens : List Tok}
      {child : Tree Tok} {children : List (Tree Tok)} :
      Derives G cat catTokens child →
      DerivesSeq G rest restTokens children →
      DerivesSeq G (.cat cat :: rest) (catTokens ++ restTokens)
        (child :: children)

end

structure CheckableGrammar (Cat Terminal Tok : Type) extends
    Grammar Cat Terminal Tok where
  acceptsBool : Terminal → Tok → Bool
  acceptsBool_sound :
    ∀ {terminal tok}, acceptsBool terminal tok = Bool.true →
      accepts terminal tok
  acceptsBool_complete :
    ∀ {terminal tok}, accepts terminal tok →
      acceptsBool terminal tok = Bool.true

namespace CheckableGrammar

mutual

def checkTree {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok) :
    Cat → Tree Tok → Bool
  | _cat, .token _tok => Bool.false
  | cat, .node ruleName children =>
      G.rules.any fun rule =>
        rule.name == ruleName &&
        decide (rule.lhs = cat) &&
        checkSeq G rule.rhs children

def checkSeq {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok) :
    List (Sym Cat Terminal) → List (Tree Tok) → Bool
  | [], [] => Bool.true
  | .token terminal :: rest, .token tok :: children =>
      G.acceptsBool terminal tok && checkSeq G rest children
  | .cat cat :: rest, child :: children =>
      checkTree G cat child && checkSeq G rest children
  | _, _ => Bool.false

end

mutual

theorem checkTree_sound {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok) :
    ∀ {cat : Cat} {tree : Tree Tok},
      checkTree G cat tree = Bool.true →
      Derives G.toGrammar cat tree.tokens tree := by
  intro cat tree h
  cases tree with
  | token tok =>
      simp [checkTree] at h
  | node ruleName children =>
      simp [checkTree] at h
      obtain ⟨rule, hrule, hruleOk⟩ := h
      rcases hruleOk with ⟨⟨hruleName, hlhs⟩, hseq⟩
      have hchildren := checkSeq_sound G hseq
      have hderive := Derives.rule hrule hlhs hchildren
      simpa [Tree.tokens, hruleName] using hderive

theorem checkSeq_sound {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok) :
    ∀ {syms : List (Sym Cat Terminal)} {children : List (Tree Tok)},
      checkSeq G syms children = Bool.true →
      DerivesSeq G.toGrammar syms (children.flatMap Tree.tokens)
        children := by
  intro syms children h
  cases syms with
  | nil =>
      cases children with
      | nil =>
          exact DerivesSeq.nil
      | cons child children =>
          simp [checkSeq] at h
  | cons sym rest =>
      cases children with
      | nil =>
          cases sym <;> simp [checkSeq] at h
      | cons child children =>
          cases sym with
          | token terminal =>
              cases child with
              | token tok =>
                  simp [checkSeq] at h
                  simpa [Tree.tokens, List.flatMap_cons] using
                    DerivesSeq.token (G.acceptsBool_sound h.left)
                      (checkSeq_sound G h.right)
              | node ruleName grandchildren =>
                  simp [checkSeq] at h
          | cat cat =>
              simp [checkSeq] at h
              have hchild := checkTree_sound G h.left
              have hchildren := checkSeq_sound G h.right
              simpa [Tree.tokens, List.flatMap_cons] using
                DerivesSeq.cat hchild hchildren

end

structure RawCompletion (Tok : Type) where
  suffix : List Tok
  tree : Tree Tok
  deriving Repr

def RawCompletion.valid {Cat Terminal Tok : Type} [DecidableEq Cat]
    [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) (cat : Cat)
    (pref : List Tok) (completion : RawCompletion Tok) : Bool :=
  decide (completion.tree.tokens = pref ++ completion.suffix) &&
    checkTree G cat completion.tree

theorem RawCompletion.valid_sound {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) {cat : Cat}
    {pref : List Tok} {completion : RawCompletion Tok}
    (hvalid : completion.valid G cat pref = Bool.true) :
    Derives G.toGrammar cat (pref ++ completion.suffix)
      completion.tree := by
  simp [RawCompletion.valid] at hvalid
  rcases hvalid with ⟨htokens, htree⟩
  have hderive := checkTree_sound G htree
  simpa [htokens] using hderive

theorem checkedTree_derives {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok) {cat : Cat}
    {tree : Tree Tok}
    (hchecked : checkTree G cat tree = Bool.true) :
    Derives G.toGrammar cat tree.tokens tree :=
  checkTree_sound G hchecked

mutual

theorem checkTree_complete {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok) :
    ∀ {cat : Cat} {tokens : List Tok} {tree : Tree Tok},
      Derives G.toGrammar cat tokens tree →
      checkTree G cat tree = Bool.true := by
  intro cat tokens tree hderive
  cases hderive with
  | rule hrule hlhs hseq =>
      simp [checkTree]
      exact ⟨_, hrule, by
        simp [hlhs, checkSeq_complete G hseq]⟩

theorem checkSeq_complete {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok) :
    ∀ {syms : List (Sym Cat Terminal)} {tokens : List Tok}
      {children : List (Tree Tok)},
      DerivesSeq G.toGrammar syms tokens children →
      checkSeq G syms children = Bool.true := by
  intro syms tokens children hseq
  cases hseq with
  | nil =>
      rfl
  | token haccept hrest =>
      simp [checkSeq, G.acceptsBool_complete haccept,
        checkSeq_complete G hrest]
  | cat hcat hrest =>
      simp [checkSeq, checkTree_complete G hcat,
        checkSeq_complete G hrest]

end

structure Defaults {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok) where
  defaultToken : Terminal → Tok
  defaultToken_valid :
    ∀ terminal, G.acceptsBool terminal (defaultToken terminal) = Bool.true
  defaultTree : Cat → Tree Tok
  defaultTree_valid :
    ∀ cat, checkTree G cat (defaultTree cat) = Bool.true

namespace Defaults

def defaultSymTree {Cat Terminal Tok : Type} [DecidableEq Cat]
    {G : CheckableGrammar Cat Terminal Tok} (defaults : Defaults G) :
    Sym Cat Terminal → Tree Tok
  | .token terminal => .token (defaults.defaultToken terminal)
  | .cat cat => defaults.defaultTree cat

def defaultSeq {Cat Terminal Tok : Type} [DecidableEq Cat]
    {G : CheckableGrammar Cat Terminal Tok} (defaults : Defaults G) :
    List (Sym Cat Terminal) → List (Tree Tok)
  | [] => []
  | sym :: rest => defaults.defaultSymTree sym :: defaults.defaultSeq rest

theorem defaultSeq_checked {Cat Terminal Tok : Type} [DecidableEq Cat]
    {G : CheckableGrammar Cat Terminal Tok} (defaults : Defaults G) :
    ∀ syms,
      checkSeq G syms (defaults.defaultSeq syms) = Bool.true := by
  intro syms
  induction syms with
  | nil =>
      rfl
  | cons sym rest ih =>
      cases sym with
      | token terminal =>
          simp [defaultSeq, defaultSymTree, checkSeq,
            defaults.defaultToken_valid, ih]
      | cat cat =>
          simp [defaultSeq, defaultSymTree, checkSeq,
            defaults.defaultTree_valid, ih]

theorem defaultSeq_derives {Cat Terminal Tok : Type} [DecidableEq Cat]
    {G : CheckableGrammar Cat Terminal Tok} (defaults : Defaults G)
    (syms : List (Sym Cat Terminal)) :
    DerivesSeq G.toGrammar syms
      ((defaults.defaultSeq syms).flatMap Tree.tokens)
      (defaults.defaultSeq syms) :=
  checkSeq_sound G (defaults.defaultSeq_checked syms)

end Defaults

end CheckableGrammar

namespace DerivesSeq

theorem append {Cat Terminal Tok : Type} {G : Grammar Cat Terminal Tok}
    {left right : List (Sym Cat Terminal)}
    {leftTokens rightTokens : List Tok}
    {leftChildren rightChildren : List (Tree Tok)}
    (hleft : DerivesSeq G left leftTokens leftChildren)
    (hright : DerivesSeq G right rightTokens rightChildren) :
    DerivesSeq G (left ++ right) (leftTokens ++ rightTokens)
      (leftChildren ++ rightChildren) := by
  refine DerivesSeq.rec
    (motive_1 := fun _cat _tokens _tree _hderive => True)
    (motive_2 := fun left leftTokens leftChildren _hleft =>
      ∀ {right : List (Sym Cat Terminal)} {rightTokens : List Tok}
        {rightChildren : List (Tree Tok)},
        DerivesSeq G right rightTokens rightChildren →
        DerivesSeq G (left ++ right) (leftTokens ++ rightTokens)
          (leftChildren ++ rightChildren))
    ?rule ?nil ?token ?cat hleft hright
  · intro _cat _tokens _children _rule _hrule _hlhs _hseq _ih
    trivial
  · intro _right _rightTokens _rightChildren hright
    simpa using hright
  · intro _terminal _tok _rest _tokens _children haccept _hrest ih
      _right _rightTokens _rightChildren hright
    simpa using DerivesSeq.token haccept (ih hright)
  · intro _cat _rest _catTokens _restTokens _child _children hcat _hrest
      _ihCat ih _right _rightTokens _rightChildren hright
    simpa [List.append_assoc] using DerivesSeq.cat hcat (ih hright)

end DerivesSeq

mutual

theorem Derives.tokens_eq {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok} :
    ∀ {cat : Cat} {tokens : List Tok} {tree : Tree Tok},
      Derives G cat tokens tree →
      tree.tokens = tokens := by
  intro cat tokens tree hderive
  cases hderive with
  | rule _hrule _hlhs hseq =>
      simpa [Tree.tokens] using DerivesSeq.tokens_eq hseq

theorem DerivesSeq.tokens_eq {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok} :
    ∀ {syms : List (Sym Cat Terminal)} {tokens : List Tok}
      {children : List (Tree Tok)},
      DerivesSeq G syms tokens children →
      children.flatMap Tree.tokens = tokens := by
  intro syms tokens children hseq
  cases hseq with
  | nil =>
      rfl
  | token _haccept hrest =>
      simp [Tree.tokens, List.flatMap_cons, DerivesSeq.tokens_eq hrest]
  | cat hcat hrest =>
      simp [List.flatMap_cons, Derives.tokens_eq hcat,
        DerivesSeq.tokens_eq hrest]

end

structure Item (Cat Terminal : Type) where
  rule : Rule Cat Terminal
  dot : Nat
  deriving Repr, DecidableEq

namespace Item

def before {Cat Terminal : Type} (item : Item Cat Terminal) :
    List (Sym Cat Terminal) :=
  item.rule.rhs.take item.dot

def after {Cat Terminal : Type} (item : Item Cat Terminal) :
    List (Sym Cat Terminal) :=
  item.rule.rhs.drop item.dot

theorem before_append_after {Cat Terminal : Type} (item : Item Cat Terminal) :
    item.before ++ item.after = item.rule.rhs := by
  simp [before, after]

end Item

def itemsForRule {Cat Terminal : Type} (rule : Rule Cat Terminal) :
    List (Item Cat Terminal) :=
  (List.range (rule.rhs.length + 1)).map fun dot => { rule, dot }

def items {Cat Terminal Tok : Type} (G : Grammar Cat Terminal Tok) :
    List (Item Cat Terminal) :=
  List.flatMap itemsForRule G.rules

theorem rule_mem_of_mem_items {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok} {item : Item Cat Terminal}
    (hmem : item ∈ items G) :
    item.rule ∈ G.rules := by
  unfold items at hmem
  rw [List.mem_flatMap] at hmem
  obtain ⟨rule, hrule, hitem⟩ := hmem
  unfold itemsForRule at hitem
  rw [List.mem_map] at hitem
  obtain ⟨dot, _hdot, hitemEq⟩ := hitem
  cases hitemEq
  exact hrule

theorem item_mem_of_rule_split {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok} {rule : Rule Cat Terminal}
    {done todo : List (Sym Cat Terminal)}
    (hrule : rule ∈ G.rules)
    (hrhs : rule.rhs = done ++ todo) :
    ({ rule := rule, dot := done.length } : Item Cat Terminal) ∈
      items G := by
  unfold items
  rw [List.mem_flatMap]
  refine ⟨rule, hrule, ?_⟩
  unfold itemsForRule
  rw [List.mem_map]
  refine ⟨done.length, ?_, rfl⟩
  rw [List.mem_range]
  have hle : done.length ≤ rule.rhs.length := by
    rw [hrhs, List.length_append]
    exact Nat.le_add_right _ _
  exact Nat.lt_succ_of_le hle

theorem item_before_of_rule_split {Cat Terminal : Type}
    {rule : Rule Cat Terminal} {done todo : List (Sym Cat Terminal)}
    (hrhs : rule.rhs = done ++ todo) :
    Item.before ({ rule := rule, dot := done.length } : Item Cat Terminal) =
      done := by
  simp [Item.before, hrhs]

theorem item_after_of_rule_split {Cat Terminal : Type}
    {rule : Rule Cat Terminal} {done todo : List (Sym Cat Terminal)}
    (hrhs : rule.rhs = done ++ todo) :
    Item.after ({ rule := rule, dot := done.length } : Item Cat Terminal) =
      todo := by
  simp [Item.after, hrhs]

inductive BoundaryCompletesItem {Cat Terminal Tok : Type}
    (G : Grammar Cat Terminal Tok) (item : Item Cat Terminal)
    (pref : List Tok) : Tree Tok → Prop where
  | mk (suffix : List Tok) {doneChildren futureChildren : List (Tree Tok)} :
      DerivesSeq G item.before pref doneChildren →
      DerivesSeq G item.after suffix futureChildren →
      BoundaryCompletesItem G item pref
        (.node item.rule.name (doneChildren ++ futureChildren))

def PrefixCompletes {Cat Terminal Tok : Type} (G : Grammar Cat Terminal Tok)
    (cat : Cat) (pref : List Tok) (tree : Tree Tok) : Prop :=
  ∃ suffix, Derives G cat (pref ++ suffix) tree

/--
Parser-frontier completion for a sequence of grammar symbols.

`boundary` is the ordinary dotted-item case: the prefix has ended between two
symbols.  `cat` is the recursive case: the prefix has ended inside the next
child category, so the child itself is completed from its own prefix.
-/
inductive FrontierCompletesSeq {Cat Terminal Tok : Type}
    (G : Grammar Cat Terminal Tok) :
    List (Sym Cat Terminal) → List Tok → List (Tree Tok) → Prop where
  | boundary (suffix : List Tok) {done todo : List (Sym Cat Terminal)}
      {pref : List Tok}
      {doneChildren futureChildren : List (Tree Tok)} :
      DerivesSeq G done pref doneChildren →
      DerivesSeq G todo suffix futureChildren →
      FrontierCompletesSeq G (done ++ todo) pref
        (doneChildren ++ futureChildren)
  | cat (suffix : List Tok) {done todo : List (Sym Cat Terminal)} {cat : Cat}
      {doneTokens activePref : List Tok}
      {doneChildren futureChildren : List (Tree Tok)} {child : Tree Tok} :
      DerivesSeq G done doneTokens doneChildren →
      PrefixCompletes G cat activePref child →
      DerivesSeq G todo suffix futureChildren →
      FrontierCompletesSeq G (done ++ .cat cat :: todo)
        (doneTokens ++ activePref) (doneChildren ++ child :: futureChildren)

theorem append_eq_append_split {α : Type} :
    ∀ (left right pref suffix : List α),
      left ++ right = pref ++ suffix →
      (∃ leftSuffix, left = pref ++ leftSuffix) ∨
      (∃ prefSuffix, pref = left ++ prefSuffix ∧
        right = prefSuffix ++ suffix)
  | [], right, pref, suffix, h => by
      right
      exact ⟨pref, by simp, h⟩
  | left, _right, [], _suffix, _h => by
      left
      exact ⟨left, by simp⟩
  | x :: left, right, y :: pref, suffix, h => by
      injection h with hxy htail
      subst y
      cases append_eq_append_split left right pref suffix htail with
      | inl hleft =>
          obtain ⟨leftSuffix, hleft⟩ := hleft
          left
          exact ⟨leftSuffix, by simp [hleft]⟩
      | inr hright =>
          obtain ⟨prefSuffix, hpref, hright⟩ := hright
          right
          exact ⟨prefSuffix, by simp [hpref], hright⟩

theorem frontierCompletesSeq_append_future {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok}
    {left right : List (Sym Cat Terminal)}
    {pref : List Tok}
    {children : List (Tree Tok)}
    {rightTokens : List Tok} {rightChildren : List (Tree Tok)}
    (hfrontier : FrontierCompletesSeq G left pref children)
    (hright : DerivesSeq G right rightTokens rightChildren) :
    FrontierCompletesSeq G (left ++ right) pref
      (children ++ rightChildren) := by
  cases hfrontier with
  | boundary suffix hdone htodo =>
      simpa [List.append_assoc] using
        (FrontierCompletesSeq.boundary (G := G)
          (suffix := suffix ++ rightTokens) hdone
          (DerivesSeq.append htodo hright))
  | cat suffix hdone hchild htodo =>
      simpa [List.append_assoc] using
        (FrontierCompletesSeq.cat (G := G)
          (suffix := suffix ++ rightTokens) hdone hchild
          (DerivesSeq.append htodo hright))

theorem frontierCompletesSeq_prepend_done {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok}
    {left right : List (Sym Cat Terminal)}
    {leftTokens pref : List Tok}
    {leftChildren children : List (Tree Tok)}
    (hleft : DerivesSeq G left leftTokens leftChildren)
    (hfrontier : FrontierCompletesSeq G right pref children) :
    FrontierCompletesSeq G (left ++ right) (leftTokens ++ pref)
      (leftChildren ++ children) := by
  cases hfrontier with
  | boundary suffix hdone htodo =>
      simpa [List.append_assoc] using
        (FrontierCompletesSeq.boundary (G := G) (suffix := suffix)
          (done := left ++ _) (todo := _)
          (DerivesSeq.append hleft hdone) htodo)
  | cat suffix hdone hchild htodo =>
      simpa [List.append_assoc] using
        (FrontierCompletesSeq.cat (G := G) (suffix := suffix)
          (done := left ++ _) (todo := _)
          (DerivesSeq.append hleft hdone) hchild htodo)

theorem frontierCompletesSeq_complete_aux {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok}
    {syms : List (Sym Cat Terminal)} {tokens : List Tok}
    {children : List (Tree Tok)}
    (hseq : DerivesSeq G syms tokens children) :
    ∀ pref suffix, tokens = pref ++ suffix →
      FrontierCompletesSeq G syms pref children := by
  refine DerivesSeq.rec
    (motive_1 := fun _cat _tokens _tree _hderive => True)
    (motive_2 := fun syms tokens children _hseq =>
      ∀ pref suffix, tokens = pref ++ suffix →
        FrontierCompletesSeq G syms pref children)
    ?rule ?nil ?token ?cat hseq
  · intro _cat _tokens _children _rule _hrule _hlhs _hseq _ih
    trivial
  · intro pref suffix htokens
    cases pref with
    | nil =>
        simpa using
          (FrontierCompletesSeq.boundary (G := G)
            (suffix := ([] : List Tok))
            (DerivesSeq.nil (G := G)) (DerivesSeq.nil (G := G)))
    | cons tok pref =>
        simp at htokens
  · intro terminal tok rest tokens children haccept hrest ih
    intro pref suffix htokens
    cases pref with
    | nil =>
        simpa using
          (FrontierCompletesSeq.boundary (G := G)
            (suffix := _ :: _) (done := []) (todo := _ :: _)
            (DerivesSeq.nil (G := G))
            (DerivesSeq.token haccept hrest))
    | cons tok' pref =>
        injection htokens with htok htail
        subst tok'
        have hfrontier := ih pref suffix htail
        have htoken :
            DerivesSeq G [Sym.token terminal] [tok] [Tree.token tok] :=
          DerivesSeq.token haccept (DerivesSeq.nil (G := G))
        simpa using
          (frontierCompletesSeq_prepend_done (G := G) htoken hfrontier)
  · intro cat rest catTokens restTokens child children hcat hrest _ihCat ih
    intro pref suffix htokens
    cases append_eq_append_split catTokens restTokens pref suffix htokens with
    | inl hinside =>
        obtain ⟨childSuffix, hcatTokens⟩ := hinside
        refine FrontierCompletesSeq.cat (G := G) (suffix := restTokens)
          (done := []) (todo := rest) (DerivesSeq.nil (G := G)) ?_ hrest
        exact ⟨childSuffix, by simpa [hcatTokens] using hcat⟩
    | inr hafter =>
        obtain ⟨restPref, hpref, hrestTokens⟩ := hafter
        have hfrontier := ih restPref suffix hrestTokens
        have hdone :
            DerivesSeq G [Sym.cat cat] catTokens [child] :=
          by
            simpa using
              (DerivesSeq.cat hcat (DerivesSeq.nil (G := G)))
        have hfrontier' :=
          frontierCompletesSeq_prepend_done (G := G) hdone hfrontier
        simpa [hpref, List.append_assoc] using hfrontier'

theorem frontierCompletesSeq_complete {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok}
    {syms : List (Sym Cat Terminal)} {pref suffix : List Tok}
    {children : List (Tree Tok)}
    (hseq : DerivesSeq G syms (pref ++ suffix) children) :
    FrontierCompletesSeq G syms pref children :=
  frontierCompletesSeq_complete_aux hseq pref suffix rfl

theorem frontierCompletesSeq_sound {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok}
    {syms : List (Sym Cat Terminal)} {pref : List Tok}
    {children : List (Tree Tok)}
    (hfrontier : FrontierCompletesSeq G syms pref children) :
    ∃ suffix, DerivesSeq G syms (pref ++ suffix) children := by
  cases hfrontier with
  | boundary suffix hdone htodo =>
      exact ⟨suffix, DerivesSeq.append hdone htodo⟩
  | cat suffix hdone hchild htodo =>
      obtain ⟨childSuffix, hchild'⟩ := hchild
      refine ⟨childSuffix ++ suffix, ?_⟩
      have htail := DerivesSeq.cat hchild' htodo
      have hseq := DerivesSeq.append hdone htail
      simpa [List.append_assoc] using hseq

/--
Parser-frontier completion for one grammar category.

The `rule` case chooses a grammar production for the category and delegates to
`FrontierCompletesSeq`, which represents all frontier positions inside that
production.
-/
inductive FrontierCompletes {Cat Terminal Tok : Type}
    (G : Grammar Cat Terminal Tok) :
    Cat → List Tok → Tree Tok → Prop where
  | rule {cat : Cat} {pref : List Tok} {children : List (Tree Tok)}
      {rule : Rule Cat Terminal} :
      rule ∈ G.rules →
      rule.lhs = cat →
      FrontierCompletesSeq G rule.rhs pref children →
      FrontierCompletes G cat pref (.node rule.name children)

theorem frontierCompletes_sound {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok}
    {cat : Cat} {pref : List Tok} {tree : Tree Tok}
    (hfrontier : FrontierCompletes G cat pref tree) :
    PrefixCompletes G cat pref tree := by
  cases hfrontier with
  | rule hrule hlhs hseq =>
      obtain ⟨suffix, hseq'⟩ := frontierCompletesSeq_sound hseq
      exact ⟨suffix, Derives.rule hrule hlhs hseq'⟩

theorem frontierCompletes_complete {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok}
    {cat : Cat} {pref : List Tok} {tree : Tree Tok}
    (hcomplete : PrefixCompletes G cat pref tree) :
    FrontierCompletes G cat pref tree := by
  obtain ⟨suffix, hderive⟩ := hcomplete
  cases hderive with
  | rule hrule hlhs hseq =>
      exact FrontierCompletes.rule hrule hlhs
        (frontierCompletesSeq_complete hseq)

theorem frontierCompletes_iff_prefixCompletes {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok}
    {cat : Cat} {pref : List Tok} {tree : Tree Tok} :
    FrontierCompletes G cat pref tree ↔ PrefixCompletes G cat pref tree :=
  ⟨frontierCompletes_sound, frontierCompletes_complete⟩

theorem frontierCompletes_of_boundaryItem {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok} {item : Item Cat Terminal}
    {pref : List Tok}
    {tree : Tree Tok}
    (hitem : item.rule ∈ G.rules)
    (hcomplete : BoundaryCompletesItem G item pref tree) :
    FrontierCompletes G item.rule.lhs pref tree := by
  cases hcomplete with
  | mk suffix hbefore hafter =>
      refine FrontierCompletes.rule hitem rfl ?_
      have hseq : FrontierCompletesSeq G (item.before ++ item.after) pref
          (_ ++ _) :=
        FrontierCompletesSeq.boundary suffix hbefore hafter
      rw [Item.before_append_after item] at hseq
      exact hseq

theorem frontierCompletes_of_generatedBoundaryItem {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok} {item : Item Cat Terminal}
    {pref : List Tok} {tree : Tree Tok}
    (hitem : item ∈ items G)
    (hcomplete : BoundaryCompletesItem G item pref tree) :
    FrontierCompletes G item.rule.lhs pref tree :=
  frontierCompletes_of_boundaryItem (rule_mem_of_mem_items hitem)
    hcomplete

namespace CheckableGrammar
namespace Defaults

def completeBoundaryRaw {Cat Terminal Tok : Type} [DecidableEq Cat]
    {G : CheckableGrammar Cat Terminal Tok} (defaults : Defaults G)
    (item : Item Cat Terminal) (doneChildren : List (Tree Tok)) :
    RawCompletion Tok :=
  { suffix := (defaults.defaultSeq item.after).flatMap Tree.tokens
    tree := .node item.rule.name
      (doneChildren ++ defaults.defaultSeq item.after) }

theorem completeBoundaryRaw_valid {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    {G : CheckableGrammar Cat Terminal Tok} (defaults : Defaults G)
    {item : Item Cat Terminal} (hitem : item.rule ∈ G.rules)
    {pref : List Tok} {doneChildren : List (Tree Tok)}
    (hdone : checkSeq G item.before doneChildren = Bool.true)
    (hpref : pref = doneChildren.flatMap Tree.tokens) :
    (defaults.completeBoundaryRaw item doneChildren).valid G
      item.rule.lhs pref = Bool.true := by
  subst pref
  let futureChildren := defaults.defaultSeq item.after
  have hbefore :
      DerivesSeq G.toGrammar item.before
        (doneChildren.flatMap Tree.tokens) doneChildren :=
    checkSeq_sound G hdone
  have hafter :
      DerivesSeq G.toGrammar item.after
        (futureChildren.flatMap Tree.tokens) futureChildren := by
    simpa [futureChildren] using defaults.defaultSeq_derives item.after
  have hseq0 :
      DerivesSeq G.toGrammar (item.before ++ item.after)
        ((doneChildren.flatMap Tree.tokens) ++
          futureChildren.flatMap Tree.tokens)
        (doneChildren ++ futureChildren) :=
    DerivesSeq.append hbefore hafter
  have hseq :
      DerivesSeq G.toGrammar item.rule.rhs
        ((doneChildren.flatMap Tree.tokens) ++
          futureChildren.flatMap Tree.tokens)
        (doneChildren ++ futureChildren) := by
    simpa [Item.before_append_after item] using hseq0
  have hderive :
      Derives G.toGrammar item.rule.lhs
        ((doneChildren.flatMap Tree.tokens) ++
          futureChildren.flatMap Tree.tokens)
        (.node item.rule.name (doneChildren ++ futureChildren)) :=
    Derives.rule hitem rfl hseq
  have hchecked :
      checkTree G item.rule.lhs
        (.node item.rule.name (doneChildren ++ futureChildren)) =
          Bool.true :=
    checkTree_complete G hderive
  simp [completeBoundaryRaw, RawCompletion.valid, futureChildren,
    Tree.tokens, List.flatMap_append, hchecked]

end Defaults
end CheckableGrammar

structure ValidCompletion {Cat Terminal Tok : Type}
    (G : Grammar Cat Terminal Tok)
    (cat : Cat) (pref : List Tok) where
  suffix : List Tok
  tree : Tree Tok
  derives : Derives G cat (pref ++ suffix) tree

namespace ValidCompletion

def completedTokens {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok}
    {cat : Cat} {pref : List Tok}
    (completion : ValidCompletion G cat pref) : List Tok :=
  pref ++ completion.suffix

theorem completedTokens_derives {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok}
    {cat : Cat} {pref : List Tok}
    (completion : ValidCompletion G cat pref) :
    Derives G cat completion.completedTokens completion.tree := by
  simpa [completedTokens] using completion.derives

end ValidCompletion

namespace CheckableGrammar

def RawCompletion.toValidCompletion {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) {cat : Cat}
    {pref : List Tok} (completion : RawCompletion Tok)
    (hvalid : completion.valid G cat pref = Bool.true) :
    ValidCompletion G.toGrammar cat pref :=
  { suffix := completion.suffix
    tree := completion.tree
    derives := completion.valid_sound G hvalid }

def RawCompletion.checked? {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) (cat : Cat)
    (pref : List Tok) (completion : RawCompletion Tok) :
    Option (ValidCompletion G.toGrammar cat pref) :=
  if hvalid : completion.valid G cat pref = Bool.true then
    some (completion.toValidCompletion G hvalid)
  else
    none

theorem RawCompletion.checked?_sound {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) {cat : Cat}
    {pref : List Tok} {raw : RawCompletion Tok}
    {completion : ValidCompletion G.toGrammar cat pref}
    (_hchecked : raw.checked? G cat pref = some completion) :
    Derives G.toGrammar cat completion.completedTokens completion.tree := by
  exact completion.completedTokens_derives

structure CheckedBoundaryState {Cat Terminal Tok : Type}
    [DecidableEq Cat] (G : CheckableGrammar Cat Terminal Tok) where
  item : Item Cat Terminal
  item_mem : item ∈ items G.toGrammar
  doneChildren : List (Tree Tok)
  checkedBefore : checkSeq G item.before doneChildren = Bool.true

namespace CheckedBoundaryState

def pref {Cat Terminal Tok : Type} [DecidableEq Cat]
    {G : CheckableGrammar Cat Terminal Tok}
    (state : CheckedBoundaryState G) : List Tok :=
  state.doneChildren.flatMap Tree.tokens

def rawCompletion {Cat Terminal Tok : Type} [DecidableEq Cat]
    {G : CheckableGrammar Cat Terminal Tok}
    (state : CheckedBoundaryState G) (defaults : Defaults G) :
    RawCompletion Tok :=
  defaults.completeBoundaryRaw state.item state.doneChildren

theorem rawCompletion_valid {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    {G : CheckableGrammar Cat Terminal Tok}
    (state : CheckedBoundaryState G) (defaults : Defaults G) :
    (state.rawCompletion defaults).valid G state.item.rule.lhs
      state.pref = Bool.true := by
  unfold rawCompletion pref
  exact Defaults.completeBoundaryRaw_valid defaults
    (by simpa using rule_mem_of_mem_items state.item_mem)
    state.checkedBefore rfl

def completion {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    {G : CheckableGrammar Cat Terminal Tok}
    (state : CheckedBoundaryState G) (defaults : Defaults G) :
    ValidCompletion G.toGrammar state.item.rule.lhs state.pref :=
  (state.rawCompletion defaults).toValidCompletion G
    (state.rawCompletion_valid defaults)

def completedTokens {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    {G : CheckableGrammar Cat Terminal Tok}
    (state : CheckedBoundaryState G) (defaults : Defaults G) :
    List Tok :=
  (state.completion defaults).completedTokens

theorem completedTokens_derives {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    {G : CheckableGrammar Cat Terminal Tok}
    (state : CheckedBoundaryState G) (defaults : Defaults G) :
    Derives G.toGrammar state.item.rule.lhs
      (state.completedTokens defaults)
      (state.completion defaults).tree :=
  (state.completion defaults).completedTokens_derives

end CheckedBoundaryState

inductive CheckedFrontierState {Cat Terminal Tok : Type}
    [DecidableEq Cat] (G : CheckableGrammar Cat Terminal Tok) :
    Cat → Type where
  | boundary (item : Item Cat Terminal)
      (item_mem : item ∈ items G.toGrammar)
      (doneChildren : List (Tree Tok))
      (checkedBefore : checkSeq G item.before doneChildren = Bool.true) :
      CheckedFrontierState G item.rule.lhs
  | descend (item : Item Cat Terminal)
      (item_mem : item ∈ items G.toGrammar)
      (activeCat : Cat) (todo : List (Sym Cat Terminal))
      (after_eq : item.after = .cat activeCat :: todo)
      (doneChildren : List (Tree Tok))
      (checkedBefore : checkSeq G item.before doneChildren = Bool.true)
      (child : CheckedFrontierState G activeCat) :
      CheckedFrontierState G item.rule.lhs

namespace CheckedFrontierState

def pref {Cat Terminal Tok : Type} [DecidableEq Cat]
    {G : CheckableGrammar Cat Terminal Tok} :
    {cat : Cat} → CheckedFrontierState G cat → List Tok
  | _, .boundary _ _ doneChildren _ =>
      doneChildren.flatMap Tree.tokens
  | _, .descend _ _ _ _ _ doneChildren _ child =>
      doneChildren.flatMap Tree.tokens ++ pref child

def rawCompletion {Cat Terminal Tok : Type} [DecidableEq Cat]
    {G : CheckableGrammar Cat Terminal Tok}
    (defaults : Defaults G) :
    {cat : Cat} → CheckedFrontierState G cat → RawCompletion Tok
  | _, .boundary item _ doneChildren _ =>
      defaults.completeBoundaryRaw item doneChildren
  | _, .descend item _ _ todo _ doneChildren _ child =>
      let childRaw := rawCompletion defaults child
      { suffix :=
          childRaw.suffix ++
            (defaults.defaultSeq todo).flatMap Tree.tokens
        tree :=
          .node item.rule.name
            (doneChildren ++ childRaw.tree :: defaults.defaultSeq todo) }

theorem rawCompletion_valid {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    {G : CheckableGrammar Cat Terminal Tok}
    (defaults : Defaults G) :
    ∀ {cat : Cat} (state : CheckedFrontierState G cat),
      (rawCompletion defaults state).valid G cat (pref state) =
        Bool.true := by
  intro cat state
  induction state with
  | boundary item item_mem doneChildren checkedBefore =>
      unfold rawCompletion pref
      exact Defaults.completeBoundaryRaw_valid defaults
        (by simpa using rule_mem_of_mem_items item_mem)
        checkedBefore rfl
  | descend item item_mem activeCat todo after_eq doneChildren checkedBefore
      child ih =>
      unfold rawCompletion pref
      let childRaw := rawCompletion defaults child
      let futureChildren := defaults.defaultSeq todo
      have hbefore :
          DerivesSeq G.toGrammar item.before
            (doneChildren.flatMap Tree.tokens) doneChildren :=
        checkSeq_sound G checkedBefore
      have hchild :
          Derives G.toGrammar activeCat
            (pref child ++ childRaw.suffix) childRaw.tree := by
        have hvalid :
            childRaw.valid G activeCat (pref child) = Bool.true := by
          simpa [childRaw] using ih
        exact RawCompletion.valid_sound G hvalid
      have hfuture :
          DerivesSeq G.toGrammar todo
            (futureChildren.flatMap Tree.tokens) futureChildren := by
        simpa [futureChildren] using defaults.defaultSeq_derives todo
      have htail :
          DerivesSeq G.toGrammar (.cat activeCat :: todo)
            ((pref child ++ childRaw.suffix) ++
              futureChildren.flatMap Tree.tokens)
            (childRaw.tree :: futureChildren) :=
        DerivesSeq.cat hchild hfuture
      have hseq0 :
          DerivesSeq G.toGrammar (item.before ++ .cat activeCat :: todo)
            ((doneChildren.flatMap Tree.tokens) ++
              ((pref child ++ childRaw.suffix) ++
                futureChildren.flatMap Tree.tokens))
            (doneChildren ++ childRaw.tree :: futureChildren) :=
        DerivesSeq.append hbefore htail
      have hseq :
          DerivesSeq G.toGrammar item.rule.rhs
            ((doneChildren.flatMap Tree.tokens ++ pref child) ++
              (childRaw.suffix ++ futureChildren.flatMap Tree.tokens))
            (doneChildren ++ childRaw.tree :: futureChildren) := by
        have hsplit :
            item.before ++ .cat activeCat :: todo = item.rule.rhs := by
          rw [← after_eq]
          exact Item.before_append_after item
        rw [← hsplit]
        simpa [List.append_assoc] using hseq0
      have hderive :
          Derives G.toGrammar item.rule.lhs
            ((doneChildren.flatMap Tree.tokens ++ pref child) ++
              (childRaw.suffix ++ futureChildren.flatMap Tree.tokens))
            (Tree.node item.rule.name
              (doneChildren ++ childRaw.tree :: futureChildren)) :=
        Derives.rule (by simpa using rule_mem_of_mem_items item_mem) rfl hseq
      have hchecked :
          checkTree G item.rule.lhs
            (Tree.node item.rule.name
              (doneChildren ++ childRaw.tree :: futureChildren)) =
            Bool.true :=
        checkTree_complete G hderive
      have hchildTokens :
          childRaw.tree.tokens = pref child ++ childRaw.suffix :=
        Derives.tokens_eq hchild
      have htokens :
          (Tree.node item.rule.name
            (doneChildren ++ childRaw.tree :: futureChildren)).tokens =
          ((doneChildren.flatMap Tree.tokens ++ pref child) ++
            (childRaw.suffix ++ futureChildren.flatMap Tree.tokens)) :=
        Derives.tokens_eq hderive
      simp [RawCompletion.valid, childRaw, futureChildren, htokens, hchecked,
        List.append_assoc]

def completion {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    {G : CheckableGrammar Cat Terminal Tok}
    (defaults : Defaults G) {cat : Cat}
    (state : CheckedFrontierState G cat) :
    ValidCompletion G.toGrammar cat state.pref :=
  (rawCompletion defaults state).toValidCompletion G
    (rawCompletion_valid defaults state)

theorem completedTokens_derives {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    {G : CheckableGrammar Cat Terminal Tok}
    (defaults : Defaults G) {cat : Cat}
    (state : CheckedFrontierState G cat) :
    Derives G.toGrammar cat
      (completion defaults state).completedTokens
      (completion defaults state).tree :=
  (completion defaults state).completedTokens_derives

end CheckedFrontierState

/--
A checked frontier state is not just a prefix: it also describes where that
prefix sits inside a full parse tree.

`boundary` means the prefix ended between grammar symbols, so the remaining
children are parsed by the dotted item's `after` symbols.  `descend` means the
prefix ended inside the active child, so the child state recursively completes
to the child tree and the dotted item's remaining `todo` symbols complete the
rest of the parent.
-/
def CheckedFrontierStateCompletes {Cat Terminal Tok : Type}
    [DecidableEq Cat] (G : CheckableGrammar Cat Terminal Tok) :
    {cat : Cat} → CheckedFrontierState G cat → Tree Tok → Prop
  | _, .boundary item _ doneChildren _, tree =>
      ∃ suffix futureChildren,
        tree = .node item.rule.name (doneChildren ++ futureChildren) ∧
        DerivesSeq G.toGrammar item.after suffix futureChildren
  | _, .descend item _ _ todo _ doneChildren _ childState, tree =>
      ∃ childTree suffix futureChildren,
        tree = .node item.rule.name
          (doneChildren ++ childTree :: futureChildren) ∧
        CheckedFrontierStateCompletes G childState childTree ∧
        DerivesSeq G.toGrammar todo suffix futureChildren

namespace CheckedFrontierStateCompletes

theorem boundary_inv {Cat Terminal Tok : Type} [DecidableEq Cat]
    {G : CheckableGrammar Cat Terminal Tok}
    {item : Item Cat Terminal}
    {item_mem : item ∈ items G.toGrammar}
    {doneChildren : List (Tree Tok)}
    {checkedBefore :
      checkSeq G item.before doneChildren = Bool.true}
    {tree : Tree Tok}
    (hcomplete :
      CheckedFrontierStateCompletes G
        (CheckedFrontierState.boundary item item_mem doneChildren
          checkedBefore)
        tree) :
    ∃ suffix futureChildren,
      tree = .node item.rule.name (doneChildren ++ futureChildren) ∧
      DerivesSeq G.toGrammar item.after suffix futureChildren :=
  hcomplete

theorem descend_inv {Cat Terminal Tok : Type} [DecidableEq Cat]
    {G : CheckableGrammar Cat Terminal Tok}
    {item : Item Cat Terminal}
    {item_mem : item ∈ items G.toGrammar}
    {activeCat : Cat} {todo : List (Sym Cat Terminal)}
    {after_eq : item.after = .cat activeCat :: todo}
    {doneChildren : List (Tree Tok)}
    {checkedBefore :
      checkSeq G item.before doneChildren = Bool.true}
    {childState : CheckedFrontierState G activeCat}
    {tree : Tree Tok}
    (hcomplete :
      CheckedFrontierStateCompletes G
        (CheckedFrontierState.descend item item_mem activeCat todo
          after_eq doneChildren checkedBefore childState)
        tree) :
    ∃ childTree suffix futureChildren,
      tree = .node item.rule.name
        (doneChildren ++ childTree :: futureChildren) ∧
      CheckedFrontierStateCompletes G childState childTree ∧
      DerivesSeq G.toGrammar todo suffix futureChildren :=
  hcomplete

theorem prefixCompletes {Cat Terminal Tok : Type} [DecidableEq Cat]
    {G : CheckableGrammar Cat Terminal Tok} :
    ∀ {cat : Cat} {state : CheckedFrontierState G cat} {tree : Tree Tok},
      CheckedFrontierStateCompletes G state tree →
        PrefixCompletes G.toGrammar cat state.pref tree := by
  intro cat state tree hcomplete
  induction state generalizing tree with
  | boundary item item_mem doneChildren checkedBefore =>
      obtain ⟨suffix, futureChildren, htree, hfuture⟩ := hcomplete
      subst tree
      refine ⟨suffix, ?_⟩
      have hbefore :
          DerivesSeq G.toGrammar item.before
            (doneChildren.flatMap Tree.tokens) doneChildren :=
        checkSeq_sound G checkedBefore
      have hseq0 :
          DerivesSeq G.toGrammar (item.before ++ item.after)
            ((doneChildren.flatMap Tree.tokens) ++ suffix)
            (doneChildren ++ futureChildren) :=
        DerivesSeq.append hbefore hfuture
      have hseq :
          DerivesSeq G.toGrammar item.rule.rhs
            ((doneChildren.flatMap Tree.tokens) ++ suffix)
            (doneChildren ++ futureChildren) := by
        simpa [Item.before_append_after item] using hseq0
      simpa [CheckedFrontierState.pref] using
        Derives.rule (by simpa using rule_mem_of_mem_items item_mem) rfl hseq
  | descend item item_mem activeCat todo after_eq doneChildren checkedBefore
      childState ih =>
      obtain ⟨childTree, suffix, futureChildren, htree, hchild,
        hfuture⟩ := hcomplete
      subst tree
      obtain ⟨childSuffix, hchildDerives⟩ := ih
        (tree := childTree) hchild
      refine ⟨childSuffix ++ suffix, ?_⟩
      have hbefore :
          DerivesSeq G.toGrammar item.before
            (doneChildren.flatMap Tree.tokens) doneChildren :=
        checkSeq_sound G checkedBefore
      have htail :
          DerivesSeq G.toGrammar (.cat activeCat :: todo)
            ((childState.pref ++ childSuffix) ++ suffix)
            (childTree :: futureChildren) :=
        DerivesSeq.cat hchildDerives hfuture
      have hseq0 :
          DerivesSeq G.toGrammar
            (item.before ++ .cat activeCat :: todo)
            ((doneChildren.flatMap Tree.tokens) ++
              ((childState.pref ++ childSuffix) ++ suffix))
            (doneChildren ++ childTree :: futureChildren) :=
        DerivesSeq.append hbefore htail
      have hsplit :
          item.before ++ .cat activeCat :: todo = item.rule.rhs := by
        rw [← after_eq]
        exact Item.before_append_after item
      have hseq :
          DerivesSeq G.toGrammar item.rule.rhs
            ((doneChildren.flatMap Tree.tokens ++ childState.pref) ++
              (childSuffix ++ suffix))
            (doneChildren ++ childTree :: futureChildren) := by
        rw [← hsplit]
        simpa [List.append_assoc] using hseq0
      simpa [CheckedFrontierState.pref, List.append_assoc] using
        Derives.rule (by simpa using rule_mem_of_mem_items item_mem) rfl hseq

end CheckedFrontierStateCompletes

theorem checkedFrontierState_of_boundarySplit {Cat Terminal Tok : Type}
    [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok)
    {rule : Rule Cat Terminal} {done todo : List (Sym Cat Terminal)}
    {pref : List Tok} {doneChildren : List (Tree Tok)}
    (hrule : rule ∈ G.rules)
    (hrhs : rule.rhs = done ++ todo)
    (hdone : DerivesSeq G.toGrammar done pref doneChildren) :
    ∃ state : CheckedFrontierState G rule.lhs,
      state.pref = pref := by
  let item : Item Cat Terminal := { rule := rule, dot := done.length }
  have hitem : item ∈ items G.toGrammar :=
    item_mem_of_rule_split (G := G.toGrammar) hrule hrhs
  have hbefore : item.before = done := by
    simpa [item] using
      item_before_of_rule_split (rule := rule) (done := done)
        (todo := todo) hrhs
  have hchecked :
      checkSeq G item.before doneChildren = Bool.true := by
    rw [hbefore]
    exact checkSeq_complete G hdone
  refine ⟨CheckedFrontierState.boundary item hitem doneChildren hchecked,
    ?_⟩
  simpa [CheckedFrontierState.pref] using DerivesSeq.tokens_eq hdone

theorem checkedFrontierState_of_descendSplit {Cat Terminal Tok : Type}
    [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok)
    {rule : Rule Cat Terminal} {done todo : List (Sym Cat Terminal)}
    {activeCat : Cat} {doneTokens activePref : List Tok}
    {doneChildren : List (Tree Tok)}
    (hrule : rule ∈ G.rules)
    (hrhs : rule.rhs = done ++ .cat activeCat :: todo)
    (hdone : DerivesSeq G.toGrammar done doneTokens doneChildren)
    (childState : CheckedFrontierState G activeCat)
    (hchildPref : childState.pref = activePref) :
    ∃ state : CheckedFrontierState G rule.lhs,
      state.pref = doneTokens ++ activePref := by
  let item : Item Cat Terminal := { rule := rule, dot := done.length }
  have hitem : item ∈ items G.toGrammar :=
    item_mem_of_rule_split (G := G.toGrammar) hrule hrhs
  have hbefore : item.before = done := by
    simpa [item] using
      item_before_of_rule_split (rule := rule) (done := done)
        (todo := .cat activeCat :: todo) hrhs
  have hafter : item.after = .cat activeCat :: todo := by
    simpa [item] using
      item_after_of_rule_split (rule := rule) (done := done)
        (todo := .cat activeCat :: todo) hrhs
  have hchecked :
      checkSeq G item.before doneChildren = Bool.true := by
    rw [hbefore]
    exact checkSeq_complete G hdone
  refine ⟨CheckedFrontierState.descend item hitem activeCat todo hafter
    doneChildren hchecked childState, ?_⟩
  have hdoneTokens : doneChildren.flatMap Tree.tokens = doneTokens :=
    DerivesSeq.tokens_eq hdone
  simp [CheckedFrontierState.pref, hdoneTokens, hchildPref]

theorem checkedFrontierState_of_frontierCompletesSeqWithAux
    {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok)
    (hchildComplete :
      ∀ {activeCat : Cat} {activePref : List Tok} {child : Tree Tok},
        PrefixCompletes G.toGrammar activeCat activePref child →
          ∃ state : CheckedFrontierState G activeCat,
            state.pref = activePref)
    {rule : Rule Cat Terminal} {syms : List (Sym Cat Terminal)}
    {pref : List Tok}
    {children : List (Tree Tok)}
    (hrule : rule ∈ G.rules)
    (hrhs : rule.rhs = syms)
    (hseq : FrontierCompletesSeq G.toGrammar syms pref children) :
    ∃ state : CheckedFrontierState G rule.lhs,
      state.pref = pref := by
  cases hseq with
  | boundary suffix hdone htodo =>
      exact checkedFrontierState_of_boundarySplit G hrule hrhs hdone
  | cat suffix hdone hchild htodo =>
      obtain ⟨childState, hchildPref⟩ := hchildComplete hchild
      exact checkedFrontierState_of_descendSplit G hrule hrhs hdone
        childState hchildPref

theorem checkedFrontierState_of_frontierCompletesSeqWith
    {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok)
    (hchildComplete :
      ∀ {activeCat : Cat} {activePref : List Tok} {child : Tree Tok},
        PrefixCompletes G.toGrammar activeCat activePref child →
          ∃ state : CheckedFrontierState G activeCat,
            state.pref = activePref)
    {rule : Rule Cat Terminal} {pref : List Tok}
    {children : List (Tree Tok)}
    (hrule : rule ∈ G.rules)
    (hseq : FrontierCompletesSeq G.toGrammar rule.rhs pref children) :
    ∃ state : CheckedFrontierState G rule.lhs,
      state.pref = pref :=
  checkedFrontierState_of_frontierCompletesSeqWithAux G hchildComplete
    hrule rfl hseq

theorem checkedFrontierState_of_frontierCompletesWith
    {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok)
    (hchildComplete :
      ∀ {activeCat : Cat} {activePref : List Tok} {child : Tree Tok},
        PrefixCompletes G.toGrammar activeCat activePref child →
          ∃ state : CheckedFrontierState G activeCat,
            state.pref = activePref)
    {cat : Cat} {pref : List Tok} {tree : Tree Tok}
    (hfrontier : FrontierCompletes G.toGrammar cat pref tree) :
    ∃ state : CheckedFrontierState G cat,
      state.pref = pref := by
  cases hfrontier with
  | rule hrule hlhs hseq =>
      subst cat
      exact checkedFrontierState_of_frontierCompletesSeqWith G
        hchildComplete hrule hseq

mutual

def checkedFrontierStateOfPrefixCompletes
    {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok) :
    ∀ {cat : Cat} {pref : List Tok} {tree : Tree Tok},
      PrefixCompletes G.toGrammar cat pref tree →
        ∃ state : CheckedFrontierState G cat,
          state.pref = pref
  | _cat, _pref, _tree, hcomplete => by
      have hfrontier := frontierCompletes_complete hcomplete
      cases hfrontier with
      | rule hrule hlhs hseq =>
          subst _cat
          exact checkedFrontierStateOfFrontierCompletesSeq G
            hrule rfl hseq
termination_by _cat _pref tree _hcomplete => (sizeOf tree, 1)

def checkedFrontierStateOfFrontierCompletesSeq
    {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok) :
    ∀ {rule : Rule Cat Terminal} {syms : List (Sym Cat Terminal)}
      {pref : List Tok} {children : List (Tree Tok)},
      rule ∈ G.rules →
      rule.rhs = syms →
      FrontierCompletesSeq G.toGrammar syms pref children →
        ∃ state : CheckedFrontierState G rule.lhs,
          state.pref = pref
  | _rule, _syms, _pref, _children, hrule, hrhs, hseq => by
      cases hseq with
      | boundary suffix hdone htodo =>
          exact checkedFrontierState_of_boundarySplit G hrule hrhs hdone
      | cat suffix hdone hchild htodo =>
          obtain ⟨childState, hchildPref⟩ :=
            checkedFrontierStateOfPrefixCompletes G hchild
          exact checkedFrontierState_of_descendSplit G hrule hrhs hdone
            childState hchildPref
termination_by _rule _syms _pref children _hrule _hrhs _hseq =>
  (sizeOf children, 0)
decreasing_by
  simp_wf
  apply Prod.Lex.left
  subst _children
  exact tree_sizeOf_lt_sizeOf_append_cons _ _ _

end

theorem checkedFrontierState_of_prefixCompletes
    {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok)
    {cat : Cat} {pref : List Tok} {tree : Tree Tok}
    (hcomplete : PrefixCompletes G.toGrammar cat pref tree) :
    ∃ state : CheckedFrontierState G cat,
      state.pref = pref :=
  checkedFrontierStateOfPrefixCompletes G hcomplete

mutual

def checkedFrontierStateOfPrefixCompletesWithCompletion
    {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok) :
    ∀ {cat : Cat} {pref : List Tok} {tree : Tree Tok},
      PrefixCompletes G.toGrammar cat pref tree →
        ∃ state : CheckedFrontierState G cat,
          state.pref = pref ∧
          CheckedFrontierStateCompletes G state tree
  | _cat, _pref, _tree, hcomplete => by
      have hfrontier := frontierCompletes_complete hcomplete
      cases hfrontier with
      | rule hrule hlhs hseq =>
          subst _cat
          exact checkedFrontierStateOfFrontierCompletesSeqWithCompletion G
            hrule rfl hseq
termination_by _cat _pref tree _hcomplete => (sizeOf tree, 1)

def checkedFrontierStateOfFrontierCompletesSeqWithCompletion
    {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok) :
    ∀ {rule : Rule Cat Terminal} {syms : List (Sym Cat Terminal)}
      {pref : List Tok} {children : List (Tree Tok)},
      rule ∈ G.rules →
      rule.rhs = syms →
      FrontierCompletesSeq G.toGrammar syms pref children →
        ∃ state : CheckedFrontierState G rule.lhs,
          state.pref = pref ∧
          CheckedFrontierStateCompletes G state (.node rule.name children)
  | rule, _syms, _pref, _children, hrule, hrhs, hseq => by
      cases hseq with
      | boundary suffix hdone htodo =>
          rename_i done todo doneChildren futureChildren
          let item : Item Cat Terminal := { rule := rule, dot := done.length }
          have hitem : item ∈ items G.toGrammar :=
            item_mem_of_rule_split (G := G.toGrammar) hrule hrhs
          have hbefore : item.before = done := by
            simpa [item] using
              item_before_of_rule_split (rule := rule) (done := done)
                (todo := todo) hrhs
          have hafter : item.after = todo := by
            simpa [item] using
              item_after_of_rule_split (rule := rule) (done := done)
                (todo := todo) hrhs
          have hchecked :
              checkSeq G item.before doneChildren = Bool.true := by
            rw [hbefore]
            exact checkSeq_complete G hdone
          let state : CheckedFrontierState G rule.lhs :=
            CheckedFrontierState.boundary item hitem doneChildren hchecked
          refine ⟨state, ?_, ?_⟩
          · simpa [state, CheckedFrontierState.pref] using
              DerivesSeq.tokens_eq hdone
          · simp [state, CheckedFrontierStateCompletes]
            exact ⟨suffix, futureChildren, by simp [item],
              by simpa [hafter] using htodo⟩
      | cat suffix hdone hchild htodo =>
          rename_i done todo activeCat doneTokens activePref
            doneChildren futureChildren child
          obtain ⟨childState, hchildPref, hchildComplete⟩ :=
            checkedFrontierStateOfPrefixCompletesWithCompletion G hchild
          let item : Item Cat Terminal := { rule := rule, dot := done.length }
          have hitem : item ∈ items G.toGrammar :=
            item_mem_of_rule_split (G := G.toGrammar) hrule hrhs
          have hbefore : item.before = done := by
            simpa [item] using
              item_before_of_rule_split (rule := rule) (done := done)
                (todo := .cat activeCat :: todo) hrhs
          have hafter : item.after = .cat activeCat :: todo := by
            simpa [item] using
              item_after_of_rule_split (rule := rule) (done := done)
                (todo := .cat activeCat :: todo) hrhs
          have hchecked :
              checkSeq G item.before doneChildren = Bool.true := by
            rw [hbefore]
            exact checkSeq_complete G hdone
          let state : CheckedFrontierState G rule.lhs :=
            CheckedFrontierState.descend item hitem activeCat todo hafter
              doneChildren
              hchecked childState
          refine ⟨state, ?_, ?_⟩
          · have hdoneTokens : doneChildren.flatMap Tree.tokens = doneTokens :=
              DerivesSeq.tokens_eq hdone
            simp [state, CheckedFrontierState.pref, hdoneTokens, hchildPref]
          · simp [state, CheckedFrontierStateCompletes]
            exact ⟨child, suffix, futureChildren, by simp [item],
              hchildComplete, by simpa using htodo⟩
termination_by _rule _syms _pref children _hrule _hrhs _hseq =>
  (sizeOf children, 0)
decreasing_by
  simp_wf
  apply Prod.Lex.left
  subst _children
  exact tree_sizeOf_lt_sizeOf_append_cons _ _ _

end

theorem checkedFrontierState_of_prefixCompletes_with_completion
    {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok)
    {cat : Cat} {pref : List Tok} {tree : Tree Tok}
    (hcomplete : PrefixCompletes G.toGrammar cat pref tree) :
    ∃ state : CheckedFrontierState G cat,
      state.pref = pref ∧
      CheckedFrontierStateCompletes G state tree :=
  checkedFrontierStateOfPrefixCompletesWithCompletion G hcomplete

theorem checkedFrontierState_of_frontierCompletes
    {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok)
    {cat : Cat} {pref : List Tok} {tree : Tree Tok}
    (hfrontier : FrontierCompletes G.toGrammar cat pref tree) :
    ∃ state : CheckedFrontierState G cat,
      state.pref = pref :=
  checkedFrontierState_of_prefixCompletes G
    (frontierCompletes_sound hfrontier)

theorem checkedFrontierState_of_boundaryItem {Cat Terminal Tok : Type}
    [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok)
    {item : Item Cat Terminal} {pref : List Tok} {tree : Tree Tok}
    (hitem : item ∈ items G.toGrammar)
    (hcomplete : BoundaryCompletesItem G.toGrammar item pref tree) :
    ∃ state : CheckedFrontierState G item.rule.lhs,
      state.pref = pref := by
  cases hcomplete with
  | mk suffix hbefore hafter =>
      refine ⟨CheckedFrontierState.boundary item hitem _
        (checkSeq_complete G hbefore), ?_⟩
      simpa [CheckedFrontierState.pref] using
        DerivesSeq.tokens_eq hbefore

structure ParsedFrontierState {Cat Terminal Tok : Type}
    [DecidableEq Cat] (G : CheckableGrammar Cat Terminal Tok)
    (cat : Cat) (pref : List Tok) where
  state : CheckedFrontierState G cat
  pref_eq : state.pref = pref

structure CheckedFrontierParser {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) (defaults : Defaults G)
    (cat : Cat) where
  parseStates :
    (pref : List Tok) → List (ParsedFrontierState G cat pref)
  parseStates_if_completable :
    ∀ pref, (∃ tree, PrefixCompletes G.toGrammar cat pref tree) →
      ∃ state, state ∈ parseStates pref

namespace CheckedFrontierParser

def completeRaw? {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    {G : CheckableGrammar Cat Terminal Tok} {defaults : Defaults G}
    {cat : Cat} (parser : CheckedFrontierParser G defaults cat)
    (pref : List Tok) : Option (RawCompletion Tok) :=
  match parser.parseStates pref with
  | [] => none
  | parsed :: _ =>
      some (CheckedFrontierState.rawCompletion defaults parsed.state)

theorem completeRaw?_sound {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    {G : CheckableGrammar Cat Terminal Tok} {defaults : Defaults G}
    {cat : Cat} (parser : CheckedFrontierParser G defaults cat)
    {pref : List Tok} {raw : RawCompletion Tok}
    (hraw : parser.completeRaw? pref = some raw) :
    raw.valid G cat pref = Bool.true := by
  unfold completeRaw? at hraw
  cases hstates : parser.parseStates pref with
  | nil =>
      simp [hstates] at hraw
  | cons state states =>
      simp [hstates] at hraw
      subst raw
      have hvalid :=
        CheckedFrontierState.rawCompletion_valid defaults state.state
      simpa [state.pref_eq] using hvalid

end CheckedFrontierParser

structure RawCompleteParser {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) (cat : Cat) where
  completeRaw : (pref : List Tok) → Option (RawCompletion Tok)
  completeRaw_if_completable :
    ∀ pref, (∃ tree, PrefixCompletes G.toGrammar cat pref tree) →
      ∃ raw,
        completeRaw pref = some raw ∧
        raw.valid G cat pref = Bool.true

namespace RawCompleteParser

def complete? {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    {G : CheckableGrammar Cat Terminal Tok} {cat : Cat}
    (parser : RawCompleteParser G cat) (pref : List Tok) :
    Option (ValidCompletion G.toGrammar cat pref) :=
  match parser.completeRaw pref with
  | none => none
  | some raw => raw.checked? G cat pref

theorem complete?_sound {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    {G : CheckableGrammar Cat Terminal Tok} {cat : Cat}
    (parser : RawCompleteParser G cat) {pref : List Tok}
    {completion : ValidCompletion G.toGrammar cat pref}
    (hcomplete : parser.complete? pref = some completion) :
    Derives G.toGrammar cat completion.completedTokens completion.tree := by
  unfold complete? at hcomplete
  cases hraw : parser.completeRaw pref with
  | none =>
      simp [hraw] at hcomplete
  | some raw =>
      simp [hraw] at hcomplete
      exact RawCompletion.checked?_sound G hcomplete

end RawCompleteParser

namespace CheckedFrontierParser

def toRawCompleteParser {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    {G : CheckableGrammar Cat Terminal Tok} {defaults : Defaults G}
    {cat : Cat} (parser : CheckedFrontierParser G defaults cat) :
    RawCompleteParser G cat where
  completeRaw pref := parser.completeRaw? pref
  completeRaw_if_completable := by
    intro pref hprefix
    obtain ⟨state, hstate⟩ :=
      parser.parseStates_if_completable pref hprefix
    cases hstates : parser.parseStates pref with
    | nil =>
        simp [hstates] at hstate
    | cons head tail =>
        refine ⟨CheckedFrontierState.rawCompletion defaults head.state,
          ?_, ?_⟩
        · simp [completeRaw?, hstates]
        · have hvalid :=
            CheckedFrontierState.rawCompletion_valid defaults head.state
          simpa [head.pref_eq] using hvalid

end CheckedFrontierParser

end CheckableGrammar

/--
An executable partial parser/completer interface.

`complete pref = some result` is already a soundness certificate: `result`
contains the suffix and a derivation of `pref ++ result.suffix`.  The
`complete_if_completable` field is the separate totality/completeness
obligation for the parser implementation.
-/
structure CompleteParser {Cat Terminal Tok : Type}
    (G : Grammar Cat Terminal Tok)
    (cat : Cat) where
  complete : (pref : List Tok) → Option (ValidCompletion G cat pref)
  complete_if_completable :
    ∀ pref, (∃ tree, PrefixCompletes G cat pref tree) →
      ∃ result, complete pref = some result

namespace CompleteParser

def completedTokens? {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok} {cat : Cat}
    (parser : CompleteParser G cat) (pref : List Tok) :
    Option (List Tok) :=
  match parser.complete pref with
  | none => none
  | some result => some result.completedTokens

theorem sound {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok} {cat : Cat}
    (parser : CompleteParser G cat) {pref : List Tok}
    {result : ValidCompletion G cat pref}
    (_hresult : parser.complete pref = some result) :
    Derives G cat result.completedTokens result.tree := by
  exact result.completedTokens_derives

theorem produces_completion_string {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok}
    {cat : Cat} (parser : CompleteParser G cat) {pref : List Tok}
    {result : ValidCompletion G cat pref}
    (_hresult : parser.complete pref = some result) :
    PrefixCompletes G cat pref result.tree := by
  exact ⟨result.suffix, result.derives⟩

theorem completedTokens?_sound {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok}
    {cat : Cat} (parser : CompleteParser G cat) {pref tokens : List Tok}
    (hresult : parser.completedTokens? pref = some tokens) :
    ∃ suffix tree, tokens = pref ++ suffix ∧ Derives G cat tokens tree := by
  unfold completedTokens? at hresult
  cases hcomplete : parser.complete pref with
  | none =>
      simp [hcomplete] at hresult
  | some result =>
      simp [hcomplete] at hresult
      subst tokens
      exact ⟨result.suffix, result.tree, rfl,
        result.completedTokens_derives⟩

end CompleteParser

namespace CheckableGrammar
namespace RawCompleteParser

def toCompleteParser {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    {G : CheckableGrammar Cat Terminal Tok} {cat : Cat}
    (parser : RawCompleteParser G cat) :
    CompleteParser G.toGrammar cat where
  complete pref := parser.complete? pref
  complete_if_completable := by
    intro pref hprefix
    obtain ⟨raw, hraw, hvalid⟩ :=
      parser.completeRaw_if_completable pref hprefix
    refine ⟨raw.toValidCompletion G hvalid, ?_⟩
    unfold complete?
    simp [hraw, RawCompletion.checked?, hvalid]

noncomputable def completeRawBySpec? {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) (cat : Cat)
    (pref : List Tok) : Option (RawCompletion Tok) := by
  classical
  exact
    if h : ∃ raw : RawCompletion Tok,
        raw.valid G cat pref = Bool.true then
      some (Classical.choose h)
    else
      none

noncomputable def bySpec {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) (cat : Cat) :
    RawCompleteParser G cat where
  completeRaw pref := completeRawBySpec? G cat pref
  completeRaw_if_completable := by
    intro pref hprefix
    classical
    obtain ⟨tree, suffix, hderive⟩ := hprefix
    let raw : RawCompletion Tok := { suffix := suffix, tree := tree }
    have hrawValid : raw.valid G cat pref = Bool.true := by
      have htokens : tree.tokens = pref ++ suffix :=
        Derives.tokens_eq hderive
      have hchecked : checkTree G cat tree = Bool.true :=
        checkTree_complete G hderive
      simp [RawCompletion.valid, raw, htokens, hchecked]
    have hexists :
        ∃ raw : RawCompletion Tok,
          raw.valid G cat pref = Bool.true :=
      ⟨raw, hrawValid⟩
    exact ⟨Classical.choose hexists, by
      unfold completeRawBySpec?
      simp [hexists], Classical.choose_spec hexists⟩

end RawCompleteParser
end CheckableGrammar

noncomputable def completionBySpec? {Cat Terminal Tok : Type}
    (G : Grammar Cat Terminal Tok) (cat : Cat) (pref : List Tok) :
    Option (ValidCompletion G cat pref) := by
  classical
  exact
    if h : ∃ result : ValidCompletion G cat pref, True then
      some (Classical.choose h)
    else
      none

noncomputable def completeParserBySpec {Cat Terminal Tok : Type}
    (G : Grammar Cat Terminal Tok) (cat : Cat) :
    CompleteParser G cat where
  complete pref := completionBySpec? G cat pref
  complete_if_completable := by
    intro pref hprefix
    classical
    have hvalid : ∃ result : ValidCompletion G cat pref, True := by
      obtain ⟨tree, suffix, hderive⟩ := hprefix
      exact ⟨{ suffix := suffix, tree := tree, derives := hderive },
        trivial⟩
    exact ⟨Classical.choose hvalid, by
      unfold completionBySpec?
      simp [hvalid]⟩

noncomputable def completionOfFrontier {Cat Terminal Tok : Type}
    {G : Grammar Cat Terminal Tok}
    {cat : Cat} {pref : List Tok} {tree : Tree Tok}
    (hfrontier : FrontierCompletes G cat pref tree) :
    ValidCompletion G cat pref :=
  let hcomplete := frontierCompletes_sound hfrontier
  { suffix := Classical.choose hcomplete
    tree := tree
    derives := Classical.choose_spec hcomplete }

/-!
An FW-Rust-shaped grammar fragment.

This fragment is intentionally tiny: it only demonstrates that the same
grammar-derived frontier can complete a prefix as a finished term, as an
equality lhs, and as an assignment lhs.  The important part is that the two
continuations are generated from grammar positions, not named by hand as
`termPrefix`/`eqRhs`-style constructors.
-/

namespace Example

inductive Cat where
  | cterm
  | clval
  deriving Repr, DecidableEq

inductive Tok where
  | ident (name : Name)
  | move
  | eqEq
  | assign
  deriving Repr, DecidableEq

open Sym

def clvalVar : Rule Cat Tok :=
  { name := "clvalVar", lhs := .clval, rhs := [.token (.ident "x")] }

def ctermMove : Rule Cat Tok :=
  { name := "ctermMove", lhs := .cterm, rhs := [.token .move, .cat .clval] }

def ctermEq : Rule Cat Tok :=
  { name := "ctermEq", lhs := .cterm,
    rhs := [.cat .cterm, .token .eqEq, .cat .cterm] }

def ctermAssignFromTerm : Rule Cat Tok :=
  { name := "ctermAssignFromTerm", lhs := .cterm,
    rhs := [.cat .cterm, .token .assign, .cat .cterm] }

def grammar : Grammar Cat Tok Tok :=
  { rules := [clvalVar, ctermMove, ctermEq, ctermAssignFromTerm]
    accepts := fun terminal tok => terminal = tok }

def xTok : Tok := .ident "x"

def prefixMoveX : List Tok :=
  [.move, xTok]

def clvalXTree : Tree Tok :=
  .node "clvalVar" [.token xTok]

def moveXTree : Tree Tok :=
  .node "ctermMove" [.token .move, clvalXTree]

def moveXEqMoveXTree : Tree Tok :=
  .node "ctermEq" [moveXTree, .token .eqEq, moveXTree]

def moveXAssignMoveXTree : Tree Tok :=
  .node "ctermAssignFromTerm" [moveXTree, .token .assign, moveXTree]

def itemCtermMoveDone : Item Cat Tok :=
  { rule := ctermMove, dot := 2 }

def itemCtermEqAfterLhs : Item Cat Tok :=
  { rule := ctermEq, dot := 1 }

def itemCtermAssignAfterLhs : Item Cat Tok :=
  { rule := ctermAssignFromTerm, dot := 1 }

theorem clvalX_derives :
    Derives grammar .clval [xTok] clvalXTree := by
  change Derives grammar .clval [xTok]
    (.node "clvalVar" [.token xTok])
  refine Derives.rule (rule := clvalVar) ?_ rfl ?_
  · simp [grammar, clvalVar]
  · simp [xTok, clvalVar]
    exact DerivesSeq.token rfl DerivesSeq.nil

theorem moveX_derives :
    Derives grammar .cterm prefixMoveX moveXTree := by
  change Derives grammar .cterm prefixMoveX
    (.node "ctermMove" [.token .move, clvalXTree])
  refine Derives.rule (rule := ctermMove) ?_ rfl ?_
  · simp [grammar, ctermMove]
  · simp [prefixMoveX, ctermMove]
    exact DerivesSeq.token rfl
      (DerivesSeq.cat clvalX_derives DerivesSeq.nil)

theorem moveXEqMoveX_derives :
    Derives grammar .cterm (prefixMoveX ++ ([Tok.eqEq] ++ prefixMoveX))
      moveXEqMoveXTree := by
  change Derives grammar .cterm (prefixMoveX ++ ([Tok.eqEq] ++ prefixMoveX))
    (.node "ctermEq" [moveXTree, .token .eqEq, moveXTree])
  refine Derives.rule (rule := ctermEq) ?_ rfl ?_
  · simp [grammar, ctermEq]
  · simp [ctermEq]
    exact DerivesSeq.cat moveX_derives
      (DerivesSeq.token rfl (DerivesSeq.cat moveX_derives DerivesSeq.nil))

def moveXEqCompletion : ValidCompletion grammar .cterm prefixMoveX :=
  { suffix := [Tok.eqEq] ++ prefixMoveX
    tree := moveXEqMoveXTree
    derives := moveXEqMoveX_derives }

theorem moveXEqCompletion_completedTokens :
    moveXEqCompletion.completedTokens =
      prefixMoveX ++ ([Tok.eqEq] ++ prefixMoveX) := rfl

theorem itemCtermMoveDone_completes :
    BoundaryCompletesItem grammar itemCtermMoveDone prefixMoveX moveXTree := by
  rw [show moveXTree =
      Tree.node itemCtermMoveDone.rule.name
        ([Tree.token Tok.move, clvalXTree] ++ []) by
    simp [moveXTree, itemCtermMoveDone, ctermMove]]
  have hbefore :
      DerivesSeq grammar itemCtermMoveDone.before prefixMoveX
        [Tree.token Tok.move, clvalXTree] := by
    simp [itemCtermMoveDone, Item.before, ctermMove, prefixMoveX]
    exact DerivesSeq.token rfl
      (DerivesSeq.cat clvalX_derives DerivesSeq.nil)
  have hafter :
      DerivesSeq grammar itemCtermMoveDone.after [] [] := by
    simpa [itemCtermMoveDone, Item.after, ctermMove] using
      (DerivesSeq.nil (G := grammar))
  exact BoundaryCompletesItem.mk [] hbefore hafter

theorem itemCtermEqAfterLhs_completes :
    BoundaryCompletesItem grammar itemCtermEqAfterLhs prefixMoveX
      moveXEqMoveXTree := by
  rw [show moveXEqMoveXTree =
      Tree.node itemCtermEqAfterLhs.rule.name
        ([moveXTree] ++ [Tree.token Tok.eqEq, moveXTree]) by
    simp [moveXEqMoveXTree, itemCtermEqAfterLhs, ctermEq]]
  have hbefore :
      DerivesSeq grammar itemCtermEqAfterLhs.before prefixMoveX
        [moveXTree] := by
    simp [itemCtermEqAfterLhs, Item.before, ctermEq, prefixMoveX]
    exact DerivesSeq.cat moveX_derives DerivesSeq.nil
  have hafter :
      DerivesSeq grammar itemCtermEqAfterLhs.after
        ([Tok.eqEq] ++ prefixMoveX) [Tree.token Tok.eqEq, moveXTree] := by
    simp [itemCtermEqAfterLhs, Item.after, ctermEq]
    exact DerivesSeq.token rfl
      (DerivesSeq.cat moveX_derives DerivesSeq.nil)
  exact BoundaryCompletesItem.mk ([Tok.eqEq] ++ prefixMoveX) hbefore hafter

theorem itemCtermAssignAfterLhs_completes :
    BoundaryCompletesItem grammar itemCtermAssignAfterLhs prefixMoveX
      moveXAssignMoveXTree := by
  rw [show moveXAssignMoveXTree =
      Tree.node itemCtermAssignAfterLhs.rule.name
        ([moveXTree] ++ [Tree.token Tok.assign, moveXTree]) by
    simp [moveXAssignMoveXTree, itemCtermAssignAfterLhs, ctermAssignFromTerm]]
  have hbefore :
      DerivesSeq grammar itemCtermAssignAfterLhs.before prefixMoveX
        [moveXTree] := by
    simp [itemCtermAssignAfterLhs, Item.before, ctermAssignFromTerm,
      prefixMoveX]
    exact DerivesSeq.cat moveX_derives DerivesSeq.nil
  have hafter :
      DerivesSeq grammar itemCtermAssignAfterLhs.after
        ([Tok.assign] ++ prefixMoveX) [Tree.token Tok.assign, moveXTree] := by
    simp [itemCtermAssignAfterLhs, Item.after, ctermAssignFromTerm]
    exact DerivesSeq.token rfl
      (DerivesSeq.cat moveX_derives DerivesSeq.nil)
  exact BoundaryCompletesItem.mk ([Tok.assign] ++ prefixMoveX) hbefore hafter

theorem same_prefix_completes_as_done_eq_and_assignment :
    FrontierCompletes grammar .cterm prefixMoveX moveXTree ∧
    FrontierCompletes grammar .cterm prefixMoveX moveXEqMoveXTree ∧
    FrontierCompletes grammar .cterm prefixMoveX moveXAssignMoveXTree := by
  refine ⟨?_, ?_, ?_⟩
  · exact frontierCompletes_of_boundaryItem
      (by simp [grammar, itemCtermMoveDone, ctermMove])
      itemCtermMoveDone_completes
  · exact frontierCompletes_of_boundaryItem
      (by simp [grammar, itemCtermEqAfterLhs, ctermEq])
      itemCtermEqAfterLhs_completes
  · exact frontierCompletes_of_boundaryItem
      (by simp [grammar, itemCtermAssignAfterLhs, ctermAssignFromTerm])
      itemCtermAssignAfterLhs_completes

end Example

end GrammarFrontier
end ConservativeExtractor
