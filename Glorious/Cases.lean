module

/-!
# Test programs

Each case is a program, its input, and what it must print followed by its
value. The same cases are run on the Core machine, the Lean bytecode machine
and the Rust VM. They are the files of `tests/`, read when the compiler is
built (`include_str`, as the library's texts are), each case after a line
`#### case` (and on it what kind of case it is, where a file has several):
the lines `#### ` that follow say what it is for, then the
program, then `#### input` and its numbers where it is given any, and after
`#### expect` what it must print followed by its value.
-/

public section

namespace Glorious

structure Case where
  src : String
  input : List Int
  expect : String
  /-- What follows `#### case` on its line. -/
  kind : String := ""

/-- The cases a file of `tests/` writes. -/
def readCases (text : String) : List Case := Id.run do
  let lines := ((text.splitOn "\n").dropLast).toArray
  let at_ := fun (i : Nat) => lines.getD i ""
  let header := fun (l : String) => l.startsWith "#### input" || l == "#### expect"
  let mut out : Array Case := #[]
  let mut i := 0
  while i < lines.size do
    let kind := ((at_ i).drop 10).toString
    i := i + 1
    while i < lines.size && (at_ i).startsWith "#### " && !header (at_ i) do i := i + 1
    let mut src : Array String := #[]
    while i < lines.size && !header (at_ i) do
      src := src.push (at_ i)
      i := i + 1
    let mut input : List Int := []
    if (at_ i).startsWith "#### input" then
      input := (((at_ i).drop 10).toString.splitOn " ").filterMap (·.toInt?)
      i := i + 1
    i := i + 1
    let mut expect : Array String := #[]
    while i < lines.size && !(at_ i).startsWith "#### case" do
      expect := expect.push (at_ i)
      i := i + 1
    out := out.push ⟨"\n".intercalate src.toList, input, "\n".intercalate expect.toList, kind⟩
  return out.toList

def cases : List Case := readCases (include_str "../tests/cases.cases")

/-- Programs that call foreign functions and read and write memory at an
address. The proved machines give these no meaning, so they are run on the
Rust VM alone. -/
def foreignCases : List Case := readCases (include_str "../tests/foreign.cases")

/-- Programs that take the Lean machines too long: compiled as any other, and
run on the Rust VM and the other back ends alone. -/
def longCases : List Case := readCases (include_str "../tests/long.cases")

/-- Programs each with one question asked of it (`Checks.found`): what the
case says after `#### case` is its number and the question. -/
def checkCases : List Case := readCases (include_str "../tests/checks.cases")

end Glorious
