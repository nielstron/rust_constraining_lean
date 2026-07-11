import FWRust.Conditional.Sealor.PartialProgram
import FWRust.Conditional.Sealor.NestedBlocks
import FWRust.Conditional.Sealor.Examples

/-!
# Sealor for FW Rust with conditionals

An isolated partial grammar and conservative frontier sealor for the
conditional calculus.  Incomplete branches are completed with the typed,
diverging `missing` term and justified by the divergence-aware conditional
typing rules.
-/
