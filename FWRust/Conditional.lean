import FWRust.Conditional.Paper
import FWRust.Conditional.Sealor

/-!
# FW Rust with conditionals

The Section 6.1 control-flow extension, including Boolean values, equality,
conditionals, type/environment joins, progress, preservation, and total
empty-initial type/runtime safety for the explicitly missing- and loop-free
fragment.  Native loops have nontermination-friendly safety statements.

`FWRust.Conditional.Sealor` adds an isolated conservative frontier sealor;
the reduced core sealor remains unchanged.

See `CONDITIONALS.md` for the minimized `T-If` interface and proof map.
-/
