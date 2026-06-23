import LwRust.Extractor.Frontier

/-!
Executable parser-frontier enumeration.

The parser is fuel-indexed but total in the limit:

* `parseCatFuel_sound` / `parseSeqFuel_sound` show that returned parse trees
  are real grammar derivations.
* `parseCatFuel_complete` / `parseSeqFuel_complete` show that every grammar
  derivation is eventually returned for enough fuel.
* `frontierStatesFuel_complete_checked_exact` shows that every checked
  grammar frontier state is eventually returned exactly.

The trusted base is therefore the small grammar checker in `Frontier.lean`.
The executable enumeration can be audited as ordinary search over grammar
rules, token splits, and checked dotted items.
-/

namespace ConservativeExtractor
namespace GrammarFrontier
namespace CheckableGrammar

def splits {α : Type} : List α → List (List α × List α)
  | [] => [([], [])]
  | x :: xs =>
      ([], x :: xs) ::
        (splits xs).map fun split => (x :: split.1, split.2)

theorem splits_mem_append {α : Type} (left right : List α) :
    (left, right) ∈ splits (left ++ right) := by
  induction left with
  | nil =>
      cases right <;> simp [splits]
  | cons x left ih =>
      simp [splits, ih]

theorem append_eq_of_mem_splits {α : Type} :
    ∀ {tokens left right : List α},
      (left, right) ∈ splits tokens → left ++ right = tokens
  | [], left, right, h => by
      simp [splits] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  | x :: xs, [], right, h => by
      simp [splits] at h
      subst right
      rfl
  | x :: xs, y :: left, right, h => by
      simp [splits] at h
      rcases h with ⟨hsplit, hxy⟩
      cases hxy
      simpa using congrArg (fun ys => x :: ys)
        (append_eq_of_mem_splits hsplit)

mutual

def parseCatFuel {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok) :
    Nat → Cat → List Tok → List (Tree Tok)
  | 0, _cat, _tokens => []
  | fuel + 1, cat, tokens =>
      G.rules.flatMap fun rule =>
        if rule.lhs = cat then
          (parseSeqFuel G fuel rule.rhs tokens).map fun children =>
            .node rule.name children
        else
          []
termination_by fuel _ _ => (fuel, 0)

def parseSeqFuel {Cat Terminal Tok : Type} [DecidableEq Cat]
    (G : CheckableGrammar Cat Terminal Tok) :
    Nat → List (Sym Cat Terminal) → List Tok → List (List (Tree Tok))
  | _fuel, [], [] => [[]]
  | _fuel, [], _tok :: _tokens => []
  | _fuel, .token _terminal :: _rest, [] => []
  | fuel, .token terminal :: rest, tok :: tokens =>
      if G.acceptsBool terminal tok then
        (parseSeqFuel G fuel rest tokens).map fun children =>
          .token tok :: children
      else
        []
  | fuel, .cat cat :: rest, tokens =>
      (splits tokens).flatMap fun split =>
        (parseCatFuel G fuel cat split.1).flatMap fun child =>
          (parseSeqFuel G fuel rest split.2).map fun children =>
            child :: children
termination_by fuel syms _ => (fuel, syms.length + 1)

end

mutual

theorem parseCatFuel_sound {Cat Terminal Tok : Type}
    [DecidableEq Cat] (G : CheckableGrammar Cat Terminal Tok) :
    ∀ {fuel cat tokens tree},
      tree ∈ parseCatFuel G fuel cat tokens →
      Derives G.toGrammar cat tokens tree := by
  intro fuel cat tokens tree hmem
  cases fuel with
  | zero =>
      simp [parseCatFuel] at hmem
  | succ fuel =>
      rw [parseCatFuel, List.mem_flatMap] at hmem
      obtain ⟨rule, hrule, htree⟩ := hmem
      by_cases hlhs : rule.lhs = cat
      · simp [hlhs] at htree
        obtain ⟨children, hchildren, htreeEq⟩ := htree
        subst tree
        exact Derives.rule hrule hlhs
          (parseSeqFuel_sound G hchildren)
      · simp [hlhs] at htree

theorem parseSeqFuel_sound {Cat Terminal Tok : Type}
    [DecidableEq Cat] (G : CheckableGrammar Cat Terminal Tok) :
    ∀ {fuel syms tokens children},
      children ∈ parseSeqFuel G fuel syms tokens →
      DerivesSeq G.toGrammar syms tokens children := by
  intro fuel syms tokens children hmem
  cases syms with
  | nil =>
      cases tokens with
      | nil =>
          simp [parseSeqFuel] at hmem
          subst children
          exact DerivesSeq.nil
      | cons tok tokens =>
          simp [parseSeqFuel] at hmem
  | cons sym rest =>
      cases sym with
      | token terminal =>
          cases tokens with
          | nil =>
              simp [parseSeqFuel] at hmem
          | cons tok tokens =>
              by_cases haccept :
                  G.acceptsBool terminal tok = Bool.true
              · simp [parseSeqFuel, haccept] at hmem
                obtain ⟨restChildren, hrest, hchildren⟩ :=
                  hmem
                subst children
                exact DerivesSeq.token (G.acceptsBool_sound haccept)
                  (parseSeqFuel_sound G hrest)
              · simp [parseSeqFuel, haccept] at hmem
      | cat cat =>
          rw [parseSeqFuel, List.mem_flatMap] at hmem
          obtain ⟨split, hsplit, hmem⟩ := hmem
          rw [List.mem_flatMap] at hmem
          obtain ⟨child, hchild, hmem⟩ := hmem
          obtain ⟨restChildren, hrest, hchildren⟩ :=
            List.mem_map.mp hmem
          subst children
          have htokens := append_eq_of_mem_splits hsplit
          rw [← htokens]
          exact DerivesSeq.cat
            (parseCatFuel_sound G hchild)
            (parseSeqFuel_sound G hrest)

end

mutual

theorem parseCatFuel_complete {Cat Terminal Tok : Type}
    [DecidableEq Cat] (G : CheckableGrammar Cat Terminal Tok) :
    ∀ {cat tokens tree},
      Derives G.toGrammar cat tokens tree →
      ∃ minFuel,
        ∀ fuel, minFuel ≤ fuel →
          tree ∈ parseCatFuel G fuel cat tokens := by
  intro cat tokens tree hderive
  cases hderive with
  | rule hrule hlhs hseq =>
      obtain ⟨minSeqFuel, hseqComplete⟩ :=
        parseSeqFuel_complete G hseq
      refine ⟨minSeqFuel + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero =>
          exact False.elim (Nat.not_succ_le_zero _ hfuel)
      | succ fuel =>
          have hseqFuel : minSeqFuel ≤ fuel :=
            Nat.succ_le_succ_iff.mp hfuel
          rw [parseCatFuel, List.mem_flatMap]
          refine ⟨_, hrule, ?_⟩
          simp [hlhs]
          exact hseqComplete fuel hseqFuel

theorem parseSeqFuel_complete {Cat Terminal Tok : Type}
    [DecidableEq Cat] (G : CheckableGrammar Cat Terminal Tok) :
    ∀ {syms tokens children},
      DerivesSeq G.toGrammar syms tokens children →
      ∃ minFuel,
        ∀ fuel, minFuel ≤ fuel →
          children ∈ parseSeqFuel G fuel syms tokens := by
  intro syms tokens children hseq
  cases hseq with
  | nil =>
      refine ⟨0, ?_⟩
      intro fuel _hfuel
      simp [parseSeqFuel]
  | token haccept hrest =>
      obtain ⟨minRestFuel, hrestComplete⟩ :=
        parseSeqFuel_complete G hrest
      refine ⟨minRestFuel, ?_⟩
      intro fuel hfuel
      simp [parseSeqFuel, G.acceptsBool_complete haccept]
      exact hrestComplete fuel hfuel
  | cat hcat hrest =>
      obtain ⟨minCatFuel, hcatComplete⟩ :=
        parseCatFuel_complete G hcat
      obtain ⟨minRestFuel, hrestComplete⟩ :=
        parseSeqFuel_complete G hrest
      refine ⟨max minCatFuel minRestFuel, ?_⟩
      intro fuel hfuel
      have hcatFuel : minCatFuel ≤ fuel :=
        Nat.le_trans (Nat.le_max_left _ _) hfuel
      have hrestFuel : minRestFuel ≤ fuel :=
        Nat.le_trans (Nat.le_max_right _ _) hfuel
      rw [parseSeqFuel, List.mem_flatMap]
      refine ⟨(_, _), splits_mem_append _ _, ?_⟩
      rw [List.mem_flatMap]
      refine ⟨_, hcatComplete fuel hcatFuel, ?_⟩
      exact List.mem_map.mpr
        ⟨_, hrestComplete fuel hrestFuel, rfl⟩

end

def boundaryState? {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok)
    (cat : Cat) (pref : List Tok)
    (itemWithMem : { item : Item Cat Terminal // item ∈ items G.toGrammar })
    (doneChildren : List (Tree Tok)) :
    Option (ParsedFrontierState G cat pref) :=
  let item := itemWithMem.val
  if hcat : item.rule.lhs = cat then
    if hchecked : checkSeq G item.before doneChildren = Bool.true then
      if hpref : doneChildren.flatMap Tree.tokens = pref then
        some (by
          subst cat
          exact
            { state :=
                CheckedFrontierState.boundary item itemWithMem.property
                  doneChildren hchecked
              pref_eq := by
                simpa [CheckedFrontierState.pref] using hpref })
      else
        none
    else
      none
  else
    none

def descendState? {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Terminal] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok)
    (cat : Cat) (pref : List Tok)
    (itemWithMem : { item : Item Cat Terminal // item ∈ items G.toGrammar })
    (activeCat : Cat) (todo : List (Sym Cat Terminal))
    (doneChildren : List (Tree Tok))
    (activePref : List Tok)
    (child : ParsedFrontierState G activeCat activePref) :
    Option (ParsedFrontierState G cat pref) :=
  let item := itemWithMem.val
  if hcat : item.rule.lhs = cat then
    if hafter : item.after = .cat activeCat :: todo then
      if hchecked : checkSeq G item.before doneChildren = Bool.true then
        if hpref :
            doneChildren.flatMap Tree.tokens ++ child.state.pref = pref then
          some (by
            subst cat
            exact
              { state :=
                  CheckedFrontierState.descend item itemWithMem.property
                    activeCat todo hafter doneChildren hchecked child.state
                pref_eq := by
                  simpa [CheckedFrontierState.pref] using hpref })
        else
          none
      else
        none
    else
      none
  else
    none

def frontierStatesFuel {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Terminal] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) :
    (fuel : Nat) → (cat : Cat) → (pref : List Tok) →
      List (ParsedFrontierState G cat pref)
  | fuel, cat, pref =>
      let boundaryStates :=
        (items G.toGrammar).attach.flatMap fun itemWithMem =>
          (parseSeqFuel G fuel itemWithMem.val.before pref).filterMap fun
              doneChildren =>
            boundaryState? G cat pref itemWithMem doneChildren
      match fuel with
      | 0 => boundaryStates
      | fuel' + 1 =>
          let descendStates :=
            (items G.toGrammar).attach.flatMap fun itemWithMem =>
              match itemWithMem.val.after with
              | .cat activeCat :: todo =>
                  (splits pref).flatMap fun split =>
                    (parseSeqFuel G fuel' itemWithMem.val.before
                        split.1).flatMap fun doneChildren =>
                      (frontierStatesFuel G fuel' activeCat split.2).filterMap
                        fun child =>
                          descendState? G cat pref itemWithMem activeCat todo
                            doneChildren split.2 child
              | _ => []
          boundaryStates ++ descendStates

theorem frontierStatesFuel_complete_checked_exact {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Terminal] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) :
    ∀ {cat : Cat} (state : CheckedFrontierState G cat),
      ∃ minFuel,
        ∀ fuel, minFuel ≤ fuel →
          ∃ parsed,
            parsed.state = state ∧
            parsed ∈ frontierStatesFuel G fuel cat state.pref := by
  intro cat state
  induction state with
  | boundary item item_mem doneChildren checkedBefore =>
      have hbefore :
          DerivesSeq G.toGrammar item.before
            (doneChildren.flatMap Tree.tokens) doneChildren :=
        checkSeq_sound G checkedBefore
      obtain ⟨minBeforeFuel, hbeforeComplete⟩ :=
        parseSeqFuel_complete G hbefore
      refine ⟨minBeforeFuel, ?_⟩
      intro fuel hfuel
      let parsed :
          ParsedFrontierState G item.rule.lhs
            (doneChildren.flatMap Tree.tokens) :=
        { state :=
            CheckedFrontierState.boundary item item_mem doneChildren
              checkedBefore
          pref_eq := rfl }
      have hsome :
          boundaryState? G item.rule.lhs
            (doneChildren.flatMap Tree.tokens) ⟨item, item_mem⟩
            doneChildren = some parsed := by
        simp [boundaryState?, parsed, checkedBefore]
      have hboundary :
          parsed ∈
            (items G.toGrammar).attach.flatMap fun itemWithMem =>
              (parseSeqFuel G fuel itemWithMem.val.before
                (doneChildren.flatMap Tree.tokens)).filterMap fun
                  doneChildren' =>
                boundaryState? G item.rule.lhs
                  (doneChildren.flatMap Tree.tokens) itemWithMem
                  doneChildren' := by
        rw [List.mem_flatMap]
        refine ⟨⟨item, item_mem⟩,
          List.mem_attach (items G.toGrammar) ⟨item, item_mem⟩, ?_⟩
        rw [List.mem_filterMap]
        exact ⟨doneChildren, hbeforeComplete fuel hfuel, hsome⟩
      cases fuel with
      | zero =>
          exact ⟨parsed, rfl, by
            change parsed ∈
              (items G.toGrammar).attach.flatMap fun itemWithMem =>
                (parseSeqFuel G 0 itemWithMem.val.before
                  (doneChildren.flatMap Tree.tokens)).filterMap fun
                    doneChildren' =>
                  boundaryState? G item.rule.lhs
                    (doneChildren.flatMap Tree.tokens) itemWithMem
                    doneChildren'
            exact hboundary⟩
      | succ fuel' =>
          exact ⟨parsed, rfl, by
            change parsed ∈
              ((items G.toGrammar).attach.flatMap fun itemWithMem =>
                (parseSeqFuel G (fuel' + 1) itemWithMem.val.before
                  (doneChildren.flatMap Tree.tokens)).filterMap fun
                    doneChildren' =>
                  boundaryState? G item.rule.lhs
                    (doneChildren.flatMap Tree.tokens) itemWithMem
                    doneChildren') ++ _
            exact List.mem_append_left _ hboundary⟩
  | descend item item_mem activeCat todo after_eq doneChildren checkedBefore
      child ih =>
      have hbefore :
          DerivesSeq G.toGrammar item.before
            (doneChildren.flatMap Tree.tokens) doneChildren :=
        checkSeq_sound G checkedBefore
      obtain ⟨minBeforeFuel, hbeforeComplete⟩ :=
        parseSeqFuel_complete G hbefore
      obtain ⟨minChildFuel, hchildComplete⟩ := ih
      refine ⟨max minBeforeFuel minChildFuel + 1, ?_⟩
      intro fuel hfuel
      cases fuel with
      | zero =>
          exact False.elim (Nat.not_succ_le_zero _ hfuel)
      | succ fuel' =>
          have hfuel' : max minBeforeFuel minChildFuel ≤ fuel' :=
            Nat.succ_le_succ_iff.mp hfuel
          have hbeforeFuel : minBeforeFuel ≤ fuel' :=
            Nat.le_trans (Nat.le_max_left _ _) hfuel'
          have hchildFuel : minChildFuel ≤ fuel' :=
            Nat.le_trans (Nat.le_max_right _ _) hfuel'
          obtain ⟨childParsed, hchildParsedState, hchildParsed⟩ :=
            hchildComplete fuel' hchildFuel
          let pref := doneChildren.flatMap Tree.tokens ++ child.pref
          let parsed : ParsedFrontierState G item.rule.lhs pref :=
            { state :=
                CheckedFrontierState.descend item item_mem activeCat todo
                  after_eq doneChildren checkedBefore childParsed.state
              pref_eq := by
                simp [pref, CheckedFrontierState.pref, childParsed.pref_eq] }
          have hsome :
              descendState? G item.rule.lhs pref ⟨item, item_mem⟩
                activeCat todo doneChildren child.pref childParsed =
                  some parsed := by
            simp [descendState?, parsed, pref, after_eq,
              checkedBefore, childParsed.pref_eq]
          have hdescend :
              parsed ∈
                (items G.toGrammar).attach.flatMap fun itemWithMem =>
                  match itemWithMem.val.after with
                  | .cat activeCat' :: todo' =>
                      (splits pref).flatMap fun split =>
                        (parseSeqFuel G fuel' itemWithMem.val.before
                          split.1).flatMap fun doneChildren' =>
                            (frontierStatesFuel G fuel' activeCat'
                              split.2).filterMap fun child' =>
                                descendState? G item.rule.lhs pref
                                  itemWithMem activeCat' todo'
                                  doneChildren' split.2 child'
                  | _ => [] := by
            rw [List.mem_flatMap]
            refine ⟨⟨item, item_mem⟩,
              List.mem_attach (items G.toGrammar) ⟨item, item_mem⟩, ?_⟩
            rw [after_eq]
            rw [List.mem_flatMap]
            refine ⟨(doneChildren.flatMap Tree.tokens, child.pref),
              by simpa [pref] using
                splits_mem_append (doneChildren.flatMap Tree.tokens)
                  child.pref, ?_⟩
            rw [List.mem_flatMap]
            refine ⟨doneChildren, hbeforeComplete fuel' hbeforeFuel, ?_⟩
            rw [List.mem_filterMap]
            exact ⟨childParsed, hchildParsed, hsome⟩
          exact ⟨parsed, by
            simp [parsed, hchildParsedState], by
            change parsed ∈ _ ++
              ((items G.toGrammar).attach.flatMap fun itemWithMem =>
                match itemWithMem.val.after with
                | .cat activeCat' :: todo' =>
                    (splits pref).flatMap fun split =>
                      (parseSeqFuel G fuel' itemWithMem.val.before
                        split.1).flatMap fun doneChildren' =>
                          (frontierStatesFuel G fuel' activeCat'
                            split.2).filterMap fun child' =>
                              descendState? G item.rule.lhs pref
                                itemWithMem activeCat' todo'
                                doneChildren' split.2 child'
                | _ => [])
            exact List.mem_append_right _ hdescend⟩

theorem frontierStatesFuel_complete_checked {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Terminal] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) :
    ∀ {cat : Cat} (state : CheckedFrontierState G cat),
      ∃ minFuel,
        ∀ fuel, minFuel ≤ fuel →
          ∃ parsed,
            parsed ∈ frontierStatesFuel G fuel cat state.pref := by
  intro cat state
  obtain ⟨minFuel, hfound⟩ :=
    frontierStatesFuel_complete_checked_exact G state
  exact ⟨minFuel, by
    intro fuel hle
    obtain ⟨parsed, _hstate, hmem⟩ := hfound fuel hle
    exact ⟨parsed, hmem⟩⟩

def completeRawFuel? {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Terminal] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) (defaults : Defaults G)
    (fuel : Nat) (cat : Cat) (pref : List Tok) :
    Option (RawCompletion Tok) :=
  match frontierStatesFuel G fuel cat pref with
  | [] => none
  | parsed :: _ => some (parsed.state.rawCompletion defaults)

theorem completeRawFuel?_sound {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Terminal] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) (defaults : Defaults G)
    {fuel : Nat} {cat : Cat} {pref : List Tok}
    {raw : RawCompletion Tok}
    (hraw : completeRawFuel? G defaults fuel cat pref = some raw) :
    raw.valid G cat pref = Bool.true := by
  unfold completeRawFuel? at hraw
  cases hstates : frontierStatesFuel G fuel cat pref with
  | nil =>
      simp [hstates] at hraw
  | cons parsed rest =>
      simp [hstates] at hraw
      subst raw
      have hvalid := parsed.state.rawCompletion_valid defaults
      simpa [parsed.pref_eq] using hvalid

def completeTokensFuel? {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Terminal] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) (defaults : Defaults G)
    (fuel : Nat) (cat : Cat) (pref : List Tok) : Option (List Tok) :=
  match completeRawFuel? G defaults fuel cat pref with
  | none => none
  | some raw => some (pref ++ raw.suffix)

theorem completeTokensFuel?_sound {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Terminal] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) (defaults : Defaults G)
    {fuel : Nat} {cat : Cat} {pref tokens : List Tok}
    (htokens :
      completeTokensFuel? G defaults fuel cat pref = some tokens) :
    ∃ suffix tree,
      tokens = pref ++ suffix ∧
      Derives G.toGrammar cat tokens tree := by
  unfold completeTokensFuel? at htokens
  cases hraw : completeRawFuel? G defaults fuel cat pref with
  | none =>
      simp [hraw] at htokens
  | some raw =>
      simp [hraw] at htokens
      subst tokens
      have hvalid := completeRawFuel?_sound G defaults hraw
      exact ⟨raw.suffix, raw.tree, rfl,
        RawCompletion.valid_sound G hvalid⟩

theorem completeRawFuel?_complete_of_checked {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Terminal] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) (defaults : Defaults G)
    {cat : Cat} {pref : List Tok}
    (state : CheckedFrontierState G cat)
    (hpref : state.pref = pref) :
    ∃ fuel raw,
      completeRawFuel? G defaults fuel cat pref = some raw ∧
      raw.valid G cat pref = Bool.true := by
  subst pref
  obtain ⟨minFuel, hcomplete⟩ :=
    frontierStatesFuel_complete_checked G state
  obtain ⟨parsed, hparsed⟩ := hcomplete minFuel (Nat.le_refl _)
  cases hstates : frontierStatesFuel G minFuel cat state.pref with
  | nil =>
      simp [hstates] at hparsed
  | cons head tail =>
      refine ⟨minFuel, head.state.rawCompletion defaults, ?_, ?_⟩
      · unfold completeRawFuel?
        simp [hstates]
      · have hvalid := head.state.rawCompletion_valid defaults
        simpa [head.pref_eq] using hvalid

theorem completeTokensFuel?_complete_of_checked {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Terminal] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) (defaults : Defaults G)
    {cat : Cat} {pref : List Tok}
    (state : CheckedFrontierState G cat)
    (hpref : state.pref = pref) :
    ∃ fuel tokens,
      completeTokensFuel? G defaults fuel cat pref = some tokens ∧
      ∃ suffix tree,
        tokens = pref ++ suffix ∧
        Derives G.toGrammar cat tokens tree := by
  obtain ⟨fuel, raw, hraw, hvalid⟩ :=
    completeRawFuel?_complete_of_checked G defaults state hpref
  refine ⟨fuel, pref ++ raw.suffix, ?_, ?_⟩
  · simp [completeTokensFuel?, hraw]
  · exact ⟨raw.suffix, raw.tree, rfl,
      RawCompletion.valid_sound G hvalid⟩

theorem completeRawFuel?_complete_of_prefixCompletes {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Terminal] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) (defaults : Defaults G)
    {cat : Cat} {pref : List Tok} {tree : Tree Tok}
    (hcomplete : PrefixCompletes G.toGrammar cat pref tree) :
    ∃ fuel raw,
      completeRawFuel? G defaults fuel cat pref = some raw ∧
      raw.valid G cat pref = Bool.true := by
  obtain ⟨state, hpref⟩ :=
    checkedFrontierState_of_prefixCompletes G hcomplete
  exact completeRawFuel?_complete_of_checked G defaults state hpref

theorem completeTokensFuel?_complete_of_prefixCompletes {Cat Terminal Tok : Type}
    [DecidableEq Cat] [DecidableEq Terminal] [DecidableEq Tok]
    (G : CheckableGrammar Cat Terminal Tok) (defaults : Defaults G)
    {cat : Cat} {pref : List Tok} {tree : Tree Tok}
    (hcomplete : PrefixCompletes G.toGrammar cat pref tree) :
    ∃ fuel tokens,
      completeTokensFuel? G defaults fuel cat pref = some tokens ∧
      ∃ suffix tree',
        tokens = pref ++ suffix ∧
        Derives G.toGrammar cat tokens tree' := by
  obtain ⟨state, hpref⟩ :=
    checkedFrontierState_of_prefixCompletes G hcomplete
  exact completeTokensFuel?_complete_of_checked G defaults state hpref

end CheckableGrammar
end GrammarFrontier
end ConservativeExtractor
