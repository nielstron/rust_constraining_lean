import FWRust.Sealor.PartialProgram

/-!
Regression checks for the paper-facing partial-realization relation.
-/

namespace ConservativeSealor
namespace Generated

example : CompletesName (.prefix "ab") "abcd" :=
  .prefix (by native_decide)

example : ¬ CompletesName (.prefix "ab") "zz" := by
  intro h
  cases h with
  | «prefix» hp =>
      have hfalse : "ab".isPrefixOf "zz" = false := by native_decide
      rw [hfalse] at hp
      contradiction

/-- A decoded integer token can realize a value obtained by appending digits. -/
example : CompletesInt "1" 12 :=
  ⟨"2", 12, by native_decide, by native_decide, rfl⟩

example : CompletesInt "0x" 16 :=
  ⟨"10", 16, by native_decide, by native_decide, rfl⟩

example : CompletesInt "0b1" 3 :=
  ⟨"1", 3, by native_decide, by native_decide, rfl⟩

example : CompletesInt "0o" 61 :=
  ⟨"75", 61, by native_decide, by native_decide, rfl⟩

example : CompletesInt "1_" 1000 :=
  ⟨"000", 1000, by native_decide, by native_decide, rfl⟩

/-- Lean's raw `num` lexer accepts an underscore immediately after zero. -/
example : CompletesInt "0_" 1 :=
  ⟨"1", 1, by native_decide, by native_decide, rfl⟩

/-- The complete facade uses Lean's unsigned `num` token, not a signed token. -/
example : ¬ CompletesInt "-" (-1) := by
  rintro ⟨_suffix, _completed, _htoken, _hparse, hvalue⟩
  cases hvalue

/-- An unclosed list always realizes the trailing hole as at least one term. -/
example {xs : List Term} : CompletesTerms PartialTerms.cutoff xs → xs ≠ [] := by
  intro h
  cases h
  simp

example {pre xs : List Term} :
    CompletesTerms (PartialTerms.elems pre none) xs →
      ∃ frontier suffix, xs = pre ++ frontier :: suffix := by
  intro h
  cases h with
  | elemsDone => exact ⟨_, _, rfl⟩

/-- Keyword-only parser states have the paper's unrestricted-hole semantics. -/
example (completion : Term) : CompletesTerm .blockStart completion :=
  .ctermBlock_blockStart

example (completion : Term) : CompletesTerm .letMutStart completion :=
  .ctermLetMut_letMutStart

example (completion : Term) : CompletesTerm .boxStart completion :=
  .ctermBox_boxStart

example (completion : Term) : CompletesTerm .tokenAmpStart completion :=
  .ctermBorrowShared_tokenAmpStart

example (completion : Term) : CompletesTerm .copyStart completion :=
  .ctermCopy_copyStart

end Generated
end ConservativeSealor
