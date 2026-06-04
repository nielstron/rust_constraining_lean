import LwRust.Core.Syntax

/-!
Tuple extension.

Java source: `FeatherweightRust/src/featherweightrust/extensions/Tuples.java`.
The executable translation is integrated through `Core.PathElem.index`,
`Core.Ty.tuple`, `Core.Value.tuple`, and `Core.Term.tuple`; this module provides
the extension-facing names.
-/

namespace LwRust
namespace Extensions
namespace Tuples

open Core

def tuple := Core.tuple
def field := Core.field

end Tuples
end Extensions
end LwRust
