import Lean.Elab.Command

-- TODO improve type checking / inference on `via` functions
-- TODO improve error messages (i.e., don't mention `beqAndRepr` or `predAndRepr`)

namespace AssertCmd

open Lean
open Meta
open Lean.Elab
open Lean.Elab.Term
open Lean.Elab.Command

private def addAndCompile (value : Expr) (name : Name) : TermElabM Unit := do
  let type ← inferType value
  let decl := Declaration.defnDecl {
    name := name, levelParams := [], type := type,
    value := value, hints := ReducibilityHints.opaque,
    safety := DefinitionSafety.unsafe
  }
  Term.ensureNoUnassignedMVars decl
  Lean.addAndCompile decl


syntax (name := assert) "#assert " term:max " == " term:max : command
syntax (name := assertVia) "#assert " term:max " == " term:max " via " term:max : command

private def beqAndRepr {α} [BEq α] [Repr α] (actual expected : α) : (Bool × String × String) :=
  if actual == expected
  then (true, reprStr actual, reprStr expected)
  else (false, reprStr actual, reprStr expected)

private def predAndRepr {α} [Repr α] (pred : α → α → Bool) (actual expected : α) : (Bool × String × String) :=
  if pred actual expected
  then (true, reprStr actual, reprStr expected)
  else (false, reprStr actual, reprStr expected)

private unsafe def elabAssertAux (tk actual expected : Syntax) (pred : Option Syntax) : CommandElabM Unit := do
  let elabComp (actual expected : Syntax) (rNm : Name) : CommandElabM (Bool × String × String) := runTermElabM (some rNm) fun _ => do
    let env ← getEnv
    let a ← Term.elabTerm actual none
    let e ← Term.elabTerm expected none
    Term.synthesizeSyntheticMVarsNoPostponing
    let valType ← withRef expected (do ensureHasType (some (← inferType a)) e)
    let r ← match pred with 
            | none => mkAppM ``beqAndRepr #[a, e]
            | some p => do
              let p ← Term.elabTerm p none
              mkAppM ``predAndRepr #[p, a, e]
    try addAndCompile r rNm; evalConst (Bool × String × String) rNm finally setEnv env
  let (res, aStr, eStr) ← elabComp actual expected `_assertion
  let maybeViaStr : String :=
    match pred with
    | none => ""
    | some p => " via " ++ (Syntax.reprint p).getD "«unknown»"
  if res 
  then logInfoAt tk ("✅ " ++ aStr ++ " == " ++ eStr ++ maybeViaStr : String)
  else do
    logErrorAt tk ("❌ terms not equal" ++ maybeViaStr : String)
    logErrorAt tk ("  actual: " ++ aStr : String)
    logErrorAt tk ("expected: " ++ eStr : String)

@[commandElab assert, commandElab assertVia]
unsafe def elabAssert : CommandElab
  | `(#assert%$tk $actual == $expected via $pred) => elabAssertAux tk actual expected (some pred)
  | `(#assert%$tk $actual == $expected) => elabAssertAux tk actual expected none 
  | _ => throwUnsupportedSyntax



-- #assert 1 == 1
-- #assert 1 == '1'
-- #assert 1 == 2
-- #assert 1 == 2
-- #assert 1 == 1 via Nat.beq
-- #assert 1 == 2 via (λ x y => Nat.beq x y)

end AssertCmd
