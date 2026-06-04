import LwRust.Core.Syntax

/-!
Control-flow extension.

Java source: `FeatherweightRust/src/featherweightrust/extensions/ControlFlow.java`.
Only `if`/`else` is present in the Java implementation; the opcode constants
for `if`, `while`, and `do while` are not implemented there either.
-/

namespace LwRust
namespace Extensions
namespace ControlFlow

def ifEq := Core.ifEq
def ifNe := Core.ifNe

-- The Java file reserves opcodes for `if`, `while`, and `do while`, but does
-- not implement syntax, typing, or semantics classes for them. The implemented
-- extension surface is therefore just `IfElse`, represented by core `ifEq` and
-- `ifNe` terms.

end ControlFlow
end Extensions
end LwRust
