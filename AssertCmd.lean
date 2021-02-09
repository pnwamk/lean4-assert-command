import Lean.Elab.Command

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

declare_syntax_cat comparator
syntax " == " : comparator
syntax " ~= " : comparator

syntax (name := assert) "#assert " term:max " == " term : command
syntax (name := assertVia) "#assert " term:max comparator term " via " term : command

private def beqAndRepr {α} [BEq α] [Repr α] (actual expected : α) : (Bool × String × String) :=
  if actual == expected
  then (true, reprStr actual, reprStr expected)
  else (false, reprStr actual, reprStr expected)

private def predAndRepr {α β} [Repr α] [Repr β] (pred : α → β → Bool) (actual : α) (expected : β) : (Bool × String × String) :=
  if pred actual expected
  then (true, reprStr actual, reprStr expected)
  else (false, reprStr actual, reprStr expected)

private unsafe def elabAssertAux (tk actual expected : Syntax) (isHEq : Bool) (pred : Option Syntax) : CommandElabM Unit := do
  let elabComp (actual expected : Syntax) (rNm : Name) : CommandElabM (Bool × String × String) := runTermElabM (some rNm) fun _ => do
    let env ← getEnv
    let a ← Term.elabTerm actual none
    let e ← Term.elabTerm expected none
    Term.synthesizeSyntheticMVarsNoPostponing
    let lhsType ← inferType a
    let r ← match pred with 
            | none => do
              let _ ← withRef expected (do ensureHasType (some lhsType) e)
              -- TODO use trySynthInstance for BEq and Repr constraint for lhsType so beqAndRepr does not appear in error messages
              mkAppM ``beqAndRepr #[a, e]
            | some predFnStx => do
              let rhsType ← if isHEq
                            then inferType e
                            else do
                              let _ ← withRef expected (do ensureHasType (some lhsType) e)
                              pure lhsType
              -- TODO use trySynthInstance for Repr constraint for lhsType and rhsType so predAndRepr does not appear in error messages
              let expectedFnType := mkForall Name.anonymous BinderInfo.default lhsType (mkForall Name.anonymous BinderInfo.default rhsType (mkConst `Bool))
              let p ← Term.elabTerm predFnStx (some expectedFnType)
              Term.synthesizeSyntheticMVarsNoPostponing
              let _ ← withRef predFnStx (do ensureHasType (some expectedFnType) p)
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
  | `(#assert%$tk $actual ~= $expected via $pred) => elabAssertAux tk actual expected true (some pred)
  | `(#assert%$tk $actual == $expected via $pred) => elabAssertAux tk actual expected false (some pred)
  | `(#assert%$tk $actual == $expected) => elabAssertAux tk actual expected false none
  | _ => throwUnsupportedSyntax



-- #assert 1 == 1
-- #assert 1 == '1'
-- #assert 1 == 2
-- #assert 1 == 1 via Nat.beq
-- #assert "ABC" == "abc" via (λ x y => x.map Char.toLower == y)
-- #assert "1" == 2 via (λ (x : String) (y : Nat) => true)
-- #assert "1" == (-2) via (λ (x : String) (y : Int) => true)
-- #assert "1" ~= (-2) via (λ (x : String) (y : Int) => true)
-- #assert "1" == 2 via (λ (x : String) (y : Int) => true)

end AssertCmd
