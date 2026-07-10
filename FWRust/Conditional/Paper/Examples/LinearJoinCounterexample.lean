import FWRust.Conditional.Paper.Typing
import FWRust.Conditional.Paper.InductiveSemantics

namespace FWRust.Conditional.Paper.LinearJoinCounterexample

open Core

theorem borrow_subset_local {mutable : Bool}
    {leftTargets rightTargets : List LVal} :
    PartialTyStrengthens (.ty (.borrow mutable leftTargets))
      (.ty (.borrow mutable rightTargets)) →
    leftTargets.Subset rightTargets := by
  intro h
  cases h with
  | reflex => exact fun _ hmem => hmem
  | borrow hsubset _ => exact hsubset

theorem ty_to_undef_inv_local {left right : Ty} :
    PartialTyStrengthens (.ty left) (.undef right) →
    PartialTyStrengthens (.ty left) (.ty right) := by
  intro h
  cases h with
  | intoUndef hinner => exact hinner

theorem var_inv_local {env : Env} {x : Name}
    {ty : PartialTy} {lifetime : Lifetime} :
    LValTyping env (.var x) ty lifetime →
    ∃ slot, env.slotAt x = some slot ∧ slot.ty = ty ∧
      slot.lifetime = lifetime := by
  intro h
  cases h with
  | var hslot => exact ⟨_, hslot, rfl, rfl⟩

def intSlot : EnvSlot :=
  { ty := .ty .int, lifetime := Lifetime.root }

def rLive : EnvSlot :=
  { ty := .ty (.borrow true [.var "a"]), lifetime := Lifetime.root }

def rDead : EnvSlot :=
  { ty := .undef (.borrow true [.var "a"]), lifetime := Lifetime.root }

def sLive : EnvSlot :=
  { ty := .ty (.borrow true [.var "b"]), lifetime := Lifetime.root }

def sDead : EnvSlot :=
  { ty := .undef (.borrow true [.var "b"]), lifetime := Lifetime.root }

def pR : EnvSlot :=
  { ty := .ty (.borrow true [.var "r"]), lifetime := Lifetime.root }

def pQ : EnvSlot :=
  { ty := .ty (.borrow true [.var "q"]), lifetime := Lifetime.root }

def pJoin : EnvSlot :=
  { ty := .ty (.borrow true [.var "q", .var "r"]),
    lifetime := Lifetime.root }

def qS : EnvSlot :=
  { ty := .ty (.borrow true [.var "s"]), lifetime := Lifetime.root }

def qP : EnvSlot :=
  { ty := .ty (.borrow true [.var "p"]), lifetime := Lifetime.root }

def qJoin : EnvSlot :=
  { ty := .ty (.borrow true [.var "s", .var "p"]),
    lifetime := Lifetime.root }

def baseEnv : Env :=
  Env.update
    (Env.update
      (Env.update
        (Env.update
          (Env.update (Env.update Env.empty "a" intSlot) "b" intSlot)
          "r" rLive)
        "s" sLive)
      "p" pR)
    "q" qS

def trueEnv : Env :=
  (baseEnv.update "p" pQ).update "r" rDead

def falseEnv : Env :=
  (baseEnv.update "q" qP).update "s" sDead

def joinEnv : Env :=
  Env.update
    (Env.update
      (Env.update (Env.update baseEnv "p" pJoin) "q" qJoin)
      "r" rDead)
    "s" sDead

theorem borrowJoinAppend {mutable : Bool} {xs ys : List LVal}
    (hxs : xs ≠ []) (hys : ys ≠ []) :
    PartialTyJoin (.ty (.borrow mutable xs)) (.ty (.borrow mutable ys))
      (.ty (.borrow mutable (xs ++ ys))) := by
  constructor
  · intro candidate hcandidate
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
    rcases hcandidate with rfl | rfl
    · exact PartialTyStrengthens.borrow
        (by intro z hz; simp [hz]) (by intro _; simp [hxs])
    · exact PartialTyStrengthens.borrow
        (by intro z hz; simp [hz]) (by intro _; simp [hys])
  · intro upper hupper
    have hx := hupper (.ty (.borrow mutable xs)) (by simp)
    have hy := hupper (.ty (.borrow mutable ys)) (by simp)
    cases hx with
    | reflex =>
        exact PartialTyStrengthens.borrow (by
            intro z hz
            rcases List.mem_append.mp hz with hz | hz
            · exact hz
            · exact borrow_subset_local hy hz)
          (by intro _; simp [hxs])
    | borrow hsubsetX hnonemptyX =>
        exact PartialTyStrengthens.borrow (by
            intro z hz
            rcases List.mem_append.mp hz with hz | hz
            · exact hsubsetX hz
            · exact borrow_subset_local hy hz)
          (by intro hright; simp [hnonemptyX hright])
    | intoUndef hx' =>
        cases hy with
        | intoUndef hy' =>
          cases hx' with
          | reflex =>
            exact PartialTyStrengthens.intoUndef
              (PartialTyStrengthens.borrow (by
                  intro z hz
                  rcases List.mem_append.mp hz with hz | hz
                  · exact hz
                  · exact borrow_subset_local hy' hz)
                (by intro _; simp [hxs]))
          | borrow hsubsetX hnonemptyX =>
            exact PartialTyStrengthens.intoUndef
              (PartialTyStrengthens.borrow (by
                  intro z hz
                  rcases List.mem_append.mp hz with hz | hz
                  · exact hsubsetX hz
                  · exact borrow_subset_local hy' hz)
                (by intro hright; simp [hnonemptyX hright]))

theorem liveDeadJoin (ty : Ty) :
    PartialTyJoin (.ty ty) (.undef ty) (.undef ty) := by
  constructor
  · intro candidate hcandidate
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
    rcases hcandidate with rfl | rfl
    · exact PartialTyStrengthens.intoUndef PartialTyStrengthens.reflex
    · exact PartialTyStrengthens.reflex
  · intro upper hupper
    exact hupper (.undef ty) (by simp)

theorem true_le_join : EnvStrengthens trueEnv joinEnv := by
  intro x
  by_cases hp : x = "p"
  · subst hp
    simp [trueEnv, joinEnv, baseEnv, pQ, pJoin, Env.update]
    exact PartialTyStrengthens.borrow (by
      intro z hz
      simp at hz
      subst z
      simp) (by intro _; simp)
  · by_cases hq : x = "q"
    · subst hq
      simp [trueEnv, joinEnv, baseEnv, qS, qJoin, Env.update]
      exact PartialTyStrengthens.borrow (by
        intro z hz
        simp at hz
        subst z
        simp) (by intro _; simp)
    · by_cases hr : x = "r"
      · subst hr
        simp [trueEnv, joinEnv, rDead, Env.update]
      · by_cases hs : x = "s"
        · subst hs
          simp [trueEnv, joinEnv, baseEnv, sLive, sDead, Env.update]
          exact PartialTyStrengthens.intoUndef PartialTyStrengthens.reflex
        · cases hbase : baseEnv.slotAt x <;>
            simp [trueEnv, joinEnv, Env.update, hp, hq, hr, hs, hbase]

theorem false_le_join : EnvStrengthens falseEnv joinEnv := by
  intro x
  by_cases hp : x = "p"
  · subst hp
    simp [falseEnv, joinEnv, baseEnv, pR, pJoin, Env.update]
    exact PartialTyStrengthens.borrow (by
      intro z hz
      simp at hz
      subst z
      simp) (by intro _; simp)
  · by_cases hq : x = "q"
    · subst hq
      simp [falseEnv, joinEnv, qP, qJoin, Env.update]
      exact PartialTyStrengthens.borrow (by
        intro z hz
        simp at hz
        subst z
        simp) (by intro _; simp)
    · by_cases hr : x = "r"
      · subst hr
        simp [falseEnv, joinEnv, baseEnv, rLive, rDead, Env.update]
        exact PartialTyStrengthens.intoUndef PartialTyStrengthens.reflex
      · by_cases hs : x = "s"
        · subst hs
          simp [falseEnv, joinEnv, sDead, Env.update]
        · cases hbase : baseEnv.slotAt x <;>
            simp [falseEnv, joinEnv, Env.update, hp, hq, hr, hs, hbase]

theorem join_least {upper : Env}
    (ht : EnvStrengthens trueEnv upper)
    (hf : EnvStrengthens falseEnv upper) :
    EnvStrengthens joinEnv upper := by
  intro x
  by_cases hp : x = "p"
  · subst hp
    have htp := ht "p"
    have hfp := hf "p"
    cases hu : upper.slotAt "p" with
    | none => simp [trueEnv, baseEnv, Env.update, hu] at htp
    | some upperSlot =>
      simp [trueEnv, falseEnv, joinEnv, baseEnv, pQ, pR, pJoin,
        Env.update, hu] at htp hfp ⊢
      exact ⟨htp.1, (borrowJoinAppend (xs := [.var "q"])
        (ys := [.var "r"]) (by simp) (by simp)).2 (by
          intro candidate hcandidate
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
          rcases hcandidate with rfl | rfl
          · exact htp.2
          · exact hfp.2)⟩
  · by_cases hq : x = "q"
    · subst hq
      have htq := ht "q"
      have hfq := hf "q"
      cases hu : upper.slotAt "q" with
      | none => simp [trueEnv, baseEnv, Env.update, hu] at htq
      | some upperSlot =>
        simp [trueEnv, falseEnv, joinEnv, baseEnv, qS, qP, qJoin,
          Env.update, hu] at htq hfq ⊢
        exact ⟨htq.1, (borrowJoinAppend (xs := [.var "s"])
          (ys := [.var "p"]) (by simp) (by simp)).2 (by
            intro candidate hcandidate
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
            rcases hcandidate with rfl | rfl
            · exact htq.2
            · exact hfq.2)⟩
    · by_cases hr : x = "r"
      · subst hr
        have htr := ht "r"
        have hfr := hf "r"
        cases hu : upper.slotAt "r" with
        | none => simp [trueEnv, Env.update, hu] at htr
        | some upperSlot =>
          simp [trueEnv, falseEnv, joinEnv, baseEnv, rLive, rDead,
            Env.update, hu] at htr hfr ⊢
          exact ⟨htr.1, (liveDeadJoin (.borrow true [.var "a"])).2 (by
            intro candidate hcandidate
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
            rcases hcandidate with rfl | rfl
            · exact hfr.2
            · exact htr.2)⟩
      · by_cases hs : x = "s"
        · subst hs
          have hts := ht "s"
          have hfs := hf "s"
          cases hu : upper.slotAt "s" with
          | none =>
            simp [trueEnv, baseEnv, sLive, Env.update, hu] at hts
          | some upperSlot =>
            simp [trueEnv, falseEnv, joinEnv, baseEnv, sLive, sDead,
              Env.update, hu] at hts hfs ⊢
            exact ⟨hfs.1, (liveDeadJoin (.borrow true [.var "b"])).2 (by
              intro candidate hcandidate
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
              rcases hcandidate with rfl | rfl
              · exact hts.2
              · exact hfs.2)⟩
        · have htx := ht x
          simpa [trueEnv, joinEnv, Env.update, hp, hq, hr, hs] using htx

theorem envJoin : EnvJoin trueEnv falseEnv joinEnv := by
  constructor
  · intro candidate hcandidate
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
    rcases hcandidate with rfl | rfl
    · exact true_le_join
    · exact false_le_join
  · intro upper hupper
    exact join_least (hupper trueEnv (by simp)) (hupper falseEnv (by simp))

theorem p_lookup : joinEnv.slotAt "p" = some pJoin := by
  simp [joinEnv, pJoin, Env.update]

theorem q_lookup : joinEnv.slotAt "q" = some qJoin := by
  simp [joinEnv, qJoin, Env.update]

theorem not_linearizable : ¬ Linearizable joinEnv := by
  rintro ⟨φ, hφ⟩
  have hpq : φ "q" < φ "p" :=
    hφ "p" pJoin p_lookup "q" (by
      simp [pJoin, PartialTy.vars, Ty.vars, LVal.base])
  have hqp : φ "p" < φ "q" :=
    hφ "q" qJoin q_lookup "p" (by
      simp [qJoin, PartialTy.vars, Ty.vars, LVal.base])
  omega

theorem liveUndefBorrowJoin {mutable : Bool} (xs ys : List LVal)
    (hxs : xs ≠ []) (hys : ys ≠ []) :
    PartialTyJoin (.ty (.borrow mutable xs)) (.undef (.borrow mutable ys))
      (.undef (.borrow mutable (xs ++ ys))) := by
  constructor
  · intro candidate hcandidate
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcandidate
    rcases hcandidate with rfl | rfl
    · exact PartialTyStrengthens.intoUndef
        (PartialTyStrengthens.borrow
          (by intro z hz; simp [hz]) (by intro _; simp [hxs]))
    · exact PartialTyStrengthens.undefLeft
        (PartialTyStrengthens.borrow
          (by intro z hz; simp [hz]) (by intro _; simp [hys]))
  · intro upper hupper
    have hx := hupper (.ty (.borrow mutable xs)) (by simp)
    have hy := hupper (.undef (.borrow mutable ys)) (by simp)
    cases hy with
    | reflex =>
        exact PartialTyStrengthens.undefLeft
          (PartialTyStrengthens.borrow (by
              intro z hz
              rcases List.mem_append.mp hz with hz | hz
              · exact borrow_subset_local
                  (ty_to_undef_inv_local hx) hz
              · exact hz)
            (by intro _; simp [hxs]))
    | undefLeft hy' =>
        have hx' := ty_to_undef_inv_local hx
        cases hx' with
        | reflex =>
          exact PartialTyStrengthens.undefLeft
            (PartialTyStrengthens.borrow (by
                intro z hz
                rcases List.mem_append.mp hz with hz | hz
                · exact hz
                · exact borrow_subset_local hy' hz)
              (by intro _; simp [hxs]))
        | borrow hsubsetX hnonemptyX =>
          exact PartialTyStrengthens.undefLeft
            (PartialTyStrengthens.borrow (by
                intro z hz
                rcases List.mem_append.mp hz with hz | hz
                · exact hsubsetX hz
                · exact borrow_subset_local hy' hz)
              (by intro hright; simp [hnonemptyX hright]))

theorem undefLiveBorrowJoin {mutable : Bool} (xs ys : List LVal)
    (hxs : xs ≠ []) (hys : ys ≠ []) :
    PartialTyJoin (.undef (.borrow mutable xs)) (.ty (.borrow mutable ys))
      (.undef (.borrow mutable (ys ++ xs))) := by
  have h := liveUndefBorrowJoin (mutable := mutable) ys xs hys hxs
  constructor
  · intro candidate hcandidate
    exact h.1 (by simpa [Set.pair_comm] using hcandidate)
  · intro upper hupper
    exact h.2 (by
      intro candidate hcandidate
      exact hupper candidate (by simpa [Set.pair_comm] using hcandidate))

theorem join_q_lval :
    LValTyping joinEnv (.var "q") qJoin.ty qJoin.lifetime :=
  LValTyping.var q_lookup

theorem join_r_lval :
    LValTyping joinEnv (.var "r") rDead.ty rDead.lifetime := by
  exact LValTyping.var (by simp [joinEnv, rDead, Env.update])

theorem join_s_lval :
    LValTyping joinEnv (.var "s") sDead.ty sDead.lifetime := by
  exact LValTyping.var (by simp [joinEnv, sDead, Env.update])

theorem join_p_lval :
    LValTyping joinEnv (.var "p") pJoin.ty pJoin.lifetime :=
  LValTyping.var p_lookup

theorem r_lookup : joinEnv.slotAt "r" = some rDead := by
  simp [joinEnv, rDead, Env.update]

theorem s_lookup : joinEnv.slotAt "s" = some sDead := by
  simp [joinEnv, sDead, Env.update]

theorem a_lookup : joinEnv.slotAt "a" = some intSlot := by
  simp [joinEnv, baseEnv, intSlot, Env.update]

theorem b_lookup : joinEnv.slotAt "b" = some intSlot := by
  simp [joinEnv, baseEnv, intSlot, Env.update]

theorem join_no_deref {lv : LVal} {pt : PartialTy} {lifetime : Lifetime} :
    LValTyping joinEnv lv pt lifetime → ∃ x, lv = .var x := by
  intro htyping
  induction lv generalizing pt lifetime with
  | var x => exact ⟨x, rfl⟩
  | deref source ih =>
      cases htyping with
      | box hsource =>
          rcases ih hsource with ⟨x, rfl⟩
          rcases var_inv_local hsource with ⟨slot, hslot, hty, _⟩
          by_cases hp : x = "p"
          · subst hp
            rw [p_lookup] at hslot
            cases Option.some.inj hslot
            simp [pJoin] at hty
          · by_cases hq : x = "q"
            · subst hq
              rw [q_lookup] at hslot
              cases Option.some.inj hslot
              simp [qJoin] at hty
            · by_cases hr : x = "r"
              · subst hr
                rw [r_lookup] at hslot
                cases Option.some.inj hslot
                simp [rDead] at hty
              · by_cases hs : x = "s"
                · subst hs
                  rw [s_lookup] at hslot
                  cases Option.some.inj hslot
                  simp [sDead] at hty
                · by_cases ha : x = "a"
                  · subst ha
                    rw [a_lookup] at hslot
                    cases Option.some.inj hslot
                    simp [intSlot] at hty
                  · by_cases hb : x = "b"
                    · subst hb
                      rw [b_lookup] at hslot
                      cases Option.some.inj hslot
                      simp [intSlot] at hty
                    · have : joinEnv.slotAt x = none := by
                        simp [joinEnv, baseEnv, Env.update, hp, hq, hr, hs,
                          ha, hb, Env.empty]
                      rw [hslot] at this
                      cases this
      | boxFull hsource =>
          rcases ih hsource with ⟨x, rfl⟩
          rcases var_inv_local hsource with ⟨slot, hslot, hty, _⟩
          by_cases hp : x = "p"
          · subst hp
            rw [p_lookup] at hslot
            cases Option.some.inj hslot
            simp [pJoin] at hty
          · by_cases hq : x = "q"
            · subst hq
              rw [q_lookup] at hslot
              cases Option.some.inj hslot
              simp [qJoin] at hty
            · by_cases hr : x = "r"
              · subst hr
                rw [r_lookup] at hslot
                cases Option.some.inj hslot
                simp [rDead] at hty
              · by_cases hs : x = "s"
                · subst hs
                  rw [s_lookup] at hslot
                  cases Option.some.inj hslot
                  simp [sDead] at hty
                · by_cases ha : x = "a"
                  · subst ha
                    rw [a_lookup] at hslot
                    cases Option.some.inj hslot
                    simp [intSlot] at hty
                  · by_cases hb : x = "b"
                    · subst hb
                      rw [b_lookup] at hslot
                      cases Option.some.inj hslot
                      simp [intSlot] at hty
                    · have : joinEnv.slotAt x = none := by
                        simp [joinEnv, baseEnv, Env.update, hp, hq, hr, hs,
                          ha, hb, Env.empty]
                      rw [hslot] at this
                      cases this
      | borrow hsource htargets =>
          rcases ih hsource with ⟨x, rfl⟩
          rcases var_inv_local hsource with ⟨slot, hslot, hty, _⟩
          by_cases hp : x = "p"
          · subst hp
            rw [p_lookup] at hslot
            cases Option.some.inj hslot
            simp [pJoin] at hty
            rcases hty with ⟨rfl, htargetsEq⟩
            cases htargetsEq
            cases htargets with
            | cons _ hrest _ _ =>
              cases hrest with
              | singleton hr =>
                rcases var_inv_local hr with ⟨rslot, hrs, hrty, _⟩
                rw [r_lookup] at hrs
                cases Option.some.inj hrs
                simp [rDead] at hrty
              | cons _ htail _ _ => cases htail
          · by_cases hq : x = "q"
            · subst hq
              rw [q_lookup] at hslot
              cases Option.some.inj hslot
              simp [qJoin] at hty
              rcases hty with ⟨rfl, htargetsEq⟩
              cases htargetsEq
              cases htargets with
              | cons hs _ _ _ =>
                rcases var_inv_local hs with ⟨sslot, hss, hsty, _⟩
                rw [s_lookup] at hss
                cases Option.some.inj hss
                simp [sDead] at hsty
            · by_cases hr : x = "r"
              · subst hr
                rw [r_lookup] at hslot
                cases Option.some.inj hslot
                simp [rDead] at hty
              · by_cases hs : x = "s"
                · subst hs
                  rw [s_lookup] at hslot
                  cases Option.some.inj hslot
                  simp [sDead] at hty
                · by_cases ha : x = "a"
                  · subst ha
                    rw [a_lookup] at hslot
                    cases Option.some.inj hslot
                    simp [intSlot] at hty
                  · by_cases hb : x = "b"
                    · subst hb
                      rw [b_lookup] at hslot
                      cases Option.some.inj hslot
                      simp [intSlot] at hty
                    · have : joinEnv.slotAt x = none := by
                        simp [joinEnv, baseEnv, Env.update, hp, hq, hr, hs,
                          ha, hb, Env.empty]
                      rw [hslot] at this
                      cases this

theorem coherent : Coherent joinEnv := by
  intro lv mutable targets borrowLifetime htyping
  rcases join_no_deref htyping with ⟨x, rfl⟩
  rcases var_inv_local htyping with ⟨slot, hslot, hty, _hlife⟩
  by_cases hp : x = "p"
  · subst hp
    rw [p_lookup] at hslot
    cases Option.some.inj hslot
    simp [pJoin] at hty
    rcases hty with ⟨rfl, htargetsEq⟩
    cases htargetsEq
    refine ⟨.undef (.borrow true
      ([.var "s", .var "p"] ++ [.var "a"])), Lifetime.root, ?_⟩
    exact LValTargetsMaybeTyping.cons join_q_lval
      (LValTargetsMaybeTyping.singleton join_r_lval)
      (liveUndefBorrowJoin [.var "s", .var "p"] [.var "a"]
        (by simp) (by simp))
      (LifetimeIntersection.self Lifetime.root)
  · by_cases hq : x = "q"
    · subst hq
      rw [q_lookup] at hslot
      cases Option.some.inj hslot
      simp [qJoin] at hty
      rcases hty with ⟨rfl, htargetsEq⟩
      cases htargetsEq
      refine ⟨.undef (.borrow true
        ([.var "q", .var "r"] ++ [.var "b"])), Lifetime.root, ?_⟩
      exact LValTargetsMaybeTyping.cons join_s_lval
        (LValTargetsMaybeTyping.singleton join_p_lval)
        (undefLiveBorrowJoin [.var "b"] [.var "q", .var "r"]
          (by simp) (by simp))
        (LifetimeIntersection.self Lifetime.root)
    · by_cases hr : x = "r"
      · subst hr
        rw [r_lookup] at hslot
        cases Option.some.inj hslot
        simp [rDead] at hty
      · by_cases hs : x = "s"
        · subst hs
          rw [s_lookup] at hslot
          cases Option.some.inj hslot
          simp [sDead] at hty
        · by_cases ha : x = "a"
          · subst ha
            rw [a_lookup] at hslot
            cases Option.some.inj hslot
            simp [intSlot] at hty
          · by_cases hb : x = "b"
            · subst hb
              rw [b_lookup] at hslot
              cases Option.some.inj hslot
              simp [intSlot] at hty
            · have : joinEnv.slotAt x = none := by
                simp [joinEnv, baseEnv, Env.update, hp, hq, hr, hs,
                  ha, hb, Env.empty]
              rw [hslot] at this
              cases this

/-!
This is deliberately an arbitrary-static-state independence witness, not a
claim that `joinEnv` is reachable from an empty source program.  Once T-If's
global `Linearizable` premise is removed, a conditional whose condition and
branches are all constants types in this coherent cyclic environment.  Its
concrete execution chooses the true branch and reaches unit without touching
the store.
-/

def cyclicStaticIf : Term :=
  .ite (.val (.bool true)) (.val .unit) (.val .unit)

theorem join_self : EnvJoin joinEnv joinEnv joinEnv := by
  simp [EnvJoin]

theorem cyclicStaticIf_typing :
    TermTyping joinEnv StoreTyping.empty Lifetime.root cyclicStaticIf .unit
      joinEnv := by
  exact TermTyping.ite
    (TermTyping.const ValueTyping.bool)
    (TermTyping.const ValueTyping.unit)
    (TermTyping.const ValueTyping.unit)
    (PartialTyJoin.self (.ty .unit))
    join_self

theorem cyclicStaticIf_executes (store : ProgramStore) :
    MultiStep store Lifetime.root cyclicStaticIf store (.val .unit) := by
  exact MultiStep.trans Step.iteTrue MultiStep.refl

/-! Supporting coherence classifications for the two acyclic component
environments.  These are not claimed to form a source-reachable branch pair;
the regression above is intentionally only an arbitrary-state independence
witness. -/

def trueMidEnv : Env := baseEnv.update "p" pQ

def falseMidEnv : Env := baseEnv.update "q" qP

theorem trueMid_p : trueMidEnv.slotAt "p" = some pQ := by
  simp [trueMidEnv, pQ, Env.update]

theorem trueMid_q : trueMidEnv.slotAt "q" = some qS := by
  simp [trueMidEnv, baseEnv, qS, Env.update]

theorem trueMid_r : trueMidEnv.slotAt "r" = some rLive := by
  simp [trueMidEnv, baseEnv, rLive, Env.update]

theorem trueMid_s : trueMidEnv.slotAt "s" = some sLive := by
  simp [trueMidEnv, baseEnv, sLive, Env.update]

theorem trueMid_a : trueMidEnv.slotAt "a" = some intSlot := by
  simp [trueMidEnv, baseEnv, intSlot, Env.update]

theorem trueMid_b : trueMidEnv.slotAt "b" = some intSlot := by
  simp [trueMidEnv, baseEnv, intSlot, Env.update]

theorem trueMid_lval_facts {lv : LVal} {pt : PartialTy}
    {lifetime : Lifetime} :
    LValTyping trueMidEnv lv pt lifetime →
    lifetime = Lifetime.root ∧
      (pt = .ty .int ∨
       pt = .ty (.borrow true [.var "q"]) ∨
       pt = .ty (.borrow true [.var "s"]) ∨
       pt = .ty (.borrow true [.var "b"]) ∨
       pt = .ty (.borrow true [.var "a"])) := by
  intro htyping
  induction lv generalizing pt lifetime with
  | var x =>
      rcases var_inv_local htyping with ⟨slot, hslot, hty, hlife⟩
      by_cases hp : x = "p"
      · subst hp
        rw [trueMid_p] at hslot
        cases Option.some.inj hslot
        exact ⟨by simpa [pQ] using hlife.symm,
          Or.inr (Or.inl (by simpa [pQ] using hty.symm))⟩
      · by_cases hq : x = "q"
        · subst hq
          rw [trueMid_q] at hslot
          cases Option.some.inj hslot
          exact ⟨by simpa [qS] using hlife.symm,
            Or.inr (Or.inr (Or.inl (by simpa [qS] using hty.symm)))⟩
        · by_cases hr : x = "r"
          · subst hr
            rw [trueMid_r] at hslot
            cases Option.some.inj hslot
            exact ⟨by simpa [rLive] using hlife.symm,
              Or.inr (Or.inr (Or.inr (Or.inr
                (by simpa [rLive] using hty.symm))))⟩
          · by_cases hs : x = "s"
            · subst hs
              rw [trueMid_s] at hslot
              cases Option.some.inj hslot
              exact ⟨by simpa [sLive] using hlife.symm,
                Or.inr (Or.inr (Or.inr (Or.inl
                  (by simpa [sLive] using hty.symm))))⟩
            · by_cases ha : x = "a"
              · subst ha
                rw [trueMid_a] at hslot
                cases Option.some.inj hslot
                exact ⟨by simpa [intSlot] using hlife.symm,
                  Or.inl (by simpa [intSlot] using hty.symm)⟩
              · by_cases hb : x = "b"
                · subst hb
                  rw [trueMid_b] at hslot
                  cases Option.some.inj hslot
                  exact ⟨by simpa [intSlot] using hlife.symm,
                    Or.inl (by simpa [intSlot] using hty.symm)⟩
                · have hnone : trueMidEnv.slotAt x = none := by
                    simp [trueMidEnv, baseEnv, Env.update, Env.empty,
                      hp, hq, hr, hs, ha, hb]
                  rw [hslot] at hnone
                  cases hnone
  | deref source ih =>
      cases htyping with
      | box hsource =>
          rcases (ih hsource).2 with h | h | h | h | h <;> cases h
      | boxFull hsource =>
          rcases (ih hsource).2 with h | h | h | h | h <;> cases h
      | borrow hsource htargets =>
          rcases ih hsource with ⟨_hlife, h⟩
          rcases h with h | h | h | h | h
          · cases h
          · simp at h
            rcases h with ⟨rfl, rfl⟩
            cases htargets with
            | singleton htarget =>
              rcases var_inv_local htarget with ⟨slot, hslot, hty, hlife⟩
              rw [trueMid_q] at hslot
              cases Option.some.inj hslot
              exact ⟨by simpa [qS] using hlife.symm,
                Or.inr (Or.inr (Or.inl (by simpa [qS] using hty.symm)))⟩
            | cons _ hrest _ _ => cases hrest
          · simp at h
            rcases h with ⟨rfl, rfl⟩
            cases htargets with
            | singleton htarget =>
              rcases var_inv_local htarget with ⟨slot, hslot, hty, hlife⟩
              rw [trueMid_s] at hslot
              cases Option.some.inj hslot
              exact ⟨by simpa [sLive] using hlife.symm,
                Or.inr (Or.inr (Or.inr (Or.inl
                  (by simpa [sLive] using hty.symm))))⟩
            | cons _ hrest _ _ => cases hrest
          · simp at h
            rcases h with ⟨rfl, rfl⟩
            cases htargets with
            | singleton htarget =>
              rcases var_inv_local htarget with ⟨slot, hslot, hty, hlife⟩
              rw [trueMid_b] at hslot
              cases Option.some.inj hslot
              exact ⟨by simpa [intSlot] using hlife.symm,
                Or.inl (by simpa [intSlot] using hty.symm)⟩
            | cons _ hrest _ _ => cases hrest
          · simp at h
            rcases h with ⟨rfl, rfl⟩
            cases htargets with
            | singleton htarget =>
              rcases var_inv_local htarget with ⟨slot, hslot, hty, hlife⟩
              rw [trueMid_a] at hslot
              cases Option.some.inj hslot
              exact ⟨by simpa [intSlot] using hlife.symm,
                Or.inl (by simpa [intSlot] using hty.symm)⟩
            | cons _ hrest _ _ => cases hrest

theorem trueMid_coherent : Coherent trueMidEnv := by
  intro lv mutable targets borrowLifetime htyping
  rcases (trueMid_lval_facts htyping).2 with h | h | h | h | h
  · cases h
  · cases h
    exact ⟨.ty (.borrow true [.var "s"]), Lifetime.root,
      LValTargetsMaybeTyping.singleton (LValTyping.var trueMid_q)⟩
  · cases h
    exact ⟨.ty (.borrow true [.var "b"]), Lifetime.root,
      LValTargetsMaybeTyping.singleton (LValTyping.var trueMid_s)⟩
  · cases h
    exact ⟨.ty .int, Lifetime.root,
      LValTargetsMaybeTyping.singleton (LValTyping.var trueMid_b)⟩
  · cases h
    exact ⟨.ty .int, Lifetime.root,
      LValTargetsMaybeTyping.singleton (LValTyping.var trueMid_a)⟩

theorem falseMid_p : falseMidEnv.slotAt "p" = some pR := by
  simp [falseMidEnv, baseEnv, pR, Env.update]

theorem falseMid_q : falseMidEnv.slotAt "q" = some qP := by
  simp [falseMidEnv, qP, Env.update]

theorem falseMid_r : falseMidEnv.slotAt "r" = some rLive := by
  simp [falseMidEnv, baseEnv, rLive, Env.update]

theorem falseMid_s : falseMidEnv.slotAt "s" = some sLive := by
  simp [falseMidEnv, baseEnv, sLive, Env.update]

theorem falseMid_a : falseMidEnv.slotAt "a" = some intSlot := by
  simp [falseMidEnv, baseEnv, intSlot, Env.update]

theorem falseMid_b : falseMidEnv.slotAt "b" = some intSlot := by
  simp [falseMidEnv, baseEnv, intSlot, Env.update]

theorem falseMid_lval_facts {lv : LVal} {pt : PartialTy}
    {lifetime : Lifetime} :
    LValTyping falseMidEnv lv pt lifetime →
    lifetime = Lifetime.root ∧
      (pt = .ty .int ∨
       pt = .ty (.borrow true [.var "p"]) ∨
       pt = .ty (.borrow true [.var "r"]) ∨
       pt = .ty (.borrow true [.var "a"]) ∨
       pt = .ty (.borrow true [.var "b"])) := by
  intro htyping
  induction lv generalizing pt lifetime with
  | var x =>
      rcases var_inv_local htyping with ⟨slot, hslot, hty, hlife⟩
      by_cases hp : x = "p"
      · subst hp
        rw [falseMid_p] at hslot
        cases Option.some.inj hslot
        exact ⟨by simpa [pR] using hlife.symm,
          Or.inr (Or.inr (Or.inl (by simpa [pR] using hty.symm)))⟩
      · by_cases hq : x = "q"
        · subst hq
          rw [falseMid_q] at hslot
          cases Option.some.inj hslot
          exact ⟨by simpa [qP] using hlife.symm,
            Or.inr (Or.inl (by simpa [qP] using hty.symm))⟩
        · by_cases hr : x = "r"
          · subst hr
            rw [falseMid_r] at hslot
            cases Option.some.inj hslot
            exact ⟨by simpa [rLive] using hlife.symm,
              Or.inr (Or.inr (Or.inr (Or.inl
                (by simpa [rLive] using hty.symm))))⟩
          · by_cases hs : x = "s"
            · subst hs
              rw [falseMid_s] at hslot
              cases Option.some.inj hslot
              exact ⟨by simpa [sLive] using hlife.symm,
                Or.inr (Or.inr (Or.inr (Or.inr
                  (by simpa [sLive] using hty.symm))))⟩
            · by_cases ha : x = "a"
              · subst ha
                rw [falseMid_a] at hslot
                cases Option.some.inj hslot
                exact ⟨by simpa [intSlot] using hlife.symm,
                  Or.inl (by simpa [intSlot] using hty.symm)⟩
              · by_cases hb : x = "b"
                · subst hb
                  rw [falseMid_b] at hslot
                  cases Option.some.inj hslot
                  exact ⟨by simpa [intSlot] using hlife.symm,
                    Or.inl (by simpa [intSlot] using hty.symm)⟩
                · have hnone : falseMidEnv.slotAt x = none := by
                    simp [falseMidEnv, baseEnv, Env.update, Env.empty,
                      hp, hq, hr, hs, ha, hb]
                  rw [hslot] at hnone
                  cases hnone
  | deref source ih =>
      cases htyping with
      | box hsource =>
          rcases (ih hsource).2 with h | h | h | h | h <;> cases h
      | boxFull hsource =>
          rcases (ih hsource).2 with h | h | h | h | h <;> cases h
      | borrow hsource htargets =>
          rcases ih hsource with ⟨_hlife, h⟩
          rcases h with h | h | h | h | h
          · cases h
          · simp at h
            rcases h with ⟨rfl, rfl⟩
            cases htargets with
            | singleton htarget =>
              rcases var_inv_local htarget with ⟨slot, hslot, hty, hlife⟩
              rw [falseMid_p] at hslot
              cases Option.some.inj hslot
              exact ⟨by simpa [pR] using hlife.symm,
                Or.inr (Or.inr (Or.inl (by simpa [pR] using hty.symm)))⟩
            | cons _ hrest _ _ => cases hrest
          · simp at h
            rcases h with ⟨rfl, rfl⟩
            cases htargets with
            | singleton htarget =>
              rcases var_inv_local htarget with ⟨slot, hslot, hty, hlife⟩
              rw [falseMid_r] at hslot
              cases Option.some.inj hslot
              exact ⟨by simpa [rLive] using hlife.symm,
                Or.inr (Or.inr (Or.inr (Or.inl
                  (by simpa [rLive] using hty.symm))))⟩
            | cons _ hrest _ _ => cases hrest
          · simp at h
            rcases h with ⟨rfl, rfl⟩
            cases htargets with
            | singleton htarget =>
              rcases var_inv_local htarget with ⟨slot, hslot, hty, hlife⟩
              rw [falseMid_a] at hslot
              cases Option.some.inj hslot
              exact ⟨by simpa [intSlot] using hlife.symm,
                Or.inl (by simpa [intSlot] using hty.symm)⟩
            | cons _ hrest _ _ => cases hrest
          · simp at h
            rcases h with ⟨rfl, rfl⟩
            cases htargets with
            | singleton htarget =>
              rcases var_inv_local htarget with ⟨slot, hslot, hty, hlife⟩
              rw [falseMid_b] at hslot
              cases Option.some.inj hslot
              exact ⟨by simpa [intSlot] using hlife.symm,
                Or.inl (by simpa [intSlot] using hty.symm)⟩
            | cons _ hrest _ _ => cases hrest

theorem falseMid_coherent : Coherent falseMidEnv := by
  intro lv mutable targets borrowLifetime htyping
  rcases (falseMid_lval_facts htyping).2 with h | h | h | h | h
  · cases h
  · cases h
    exact ⟨.ty (.borrow true [.var "r"]), Lifetime.root,
      LValTargetsMaybeTyping.singleton (LValTyping.var falseMid_p)⟩
  · cases h
    exact ⟨.ty (.borrow true [.var "a"]), Lifetime.root,
      LValTargetsMaybeTyping.singleton (LValTyping.var falseMid_r)⟩
  · cases h
    exact ⟨.ty .int, Lifetime.root,
      LValTargetsMaybeTyping.singleton (LValTyping.var falseMid_a)⟩
  · cases h
    exact ⟨.ty .int, Lifetime.root,
      LValTargetsMaybeTyping.singleton (LValTyping.var falseMid_b)⟩

end FWRust.Conditional.Paper.LinearJoinCounterexample
