import LwRust.Paper.BorrowChecker

namespace LwRust
namespace Paper

open Core

def oneSidedBorrowJoinProgram : Term :=
  .block [0] [
    .letMut "cond" (.val (.bool true)),
    .letMut "a" (.val (.int 0)),
    .letMut "c" (.val (.int 0)),
    .letMut "d" (.val (.int 0)),
    .letMut "x" (.borrow true (.var "c")),
    .letMut "y" (.borrow true (.var "d")),
    .ite
      (.copy (.var "cond"))
      (.block [0, 0] [
        .assign (.var "x") (.borrow true (.var "a"))
      ])
      (.block [0, 0] [
        .assign (.var "y") (.borrow true (.var "a"))
      ]),
    .assign (.deref (.var "x")) (.val (.int 0)),
    .assign (.deref (.var "y")) (.val (.int 1))
  ]

#eval borrowCheck? 256 oneSidedBorrowJoinProgram
#eval borrowCheckFailed? 256 oneSidedBorrowJoinProgram
#eval checkProgram? 256 oneSidedBorrowJoinProgram

example : borrowCheckFailureWitness 256 oneSidedBorrowJoinProgram := by
  borrow_check

end Paper
end LwRust
