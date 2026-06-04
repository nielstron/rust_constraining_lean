import LwRust.CompleteProgram

/-!
Control-flow extension.

Java source: `FeatherweightRust/src/featherweightrust/extensions/ControlFlow.java`.
Only `if`/`else` is present in the Java implementation; the opcode constants
for `if`, `while`, and `do while` are not implemented there either.
-/

namespace LwRust
namespace Extensions
namespace ControlFlow

def ifEq := CompleteProgram.ifEq
def ifNe := CompleteProgram.ifNe

-- TODO: The Java file reserves opcodes for `if`, `while`, and `do while`, but
-- does not implement typing or semantics for them. They are therefore not
-- translated beyond this note.

end ControlFlow
end Extensions
end LwRust
