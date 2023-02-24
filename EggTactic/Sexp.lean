import EggTactic.Util
import Lean

open Lean

/-- -/
inductive Sexp
  | atom : String → Sexp
  | list : List Sexp → Sexp
  deriving BEq, Inhabited, Repr

def Sexp.fromString : String → Sexp
  | s => Sexp.atom s

instance : Coe String Sexp where
  coe s := Sexp.fromString s

def Sexp.fromList : List Sexp → Sexp
  | xs => Sexp.list xs

instance : Coe (List Sexp) Sexp where
  coe := Sexp.fromList

partial def Sexp.toString : Sexp → String
  | .atom s  => s
  | .list xs => "(" ++ " ".intercalate (xs.map Sexp.toString) ++ ")"

instance : ToString Sexp := ⟨Sexp.toString⟩

def Sexp.toList? : Sexp → Option (List Sexp)
  | .atom _  => none
  | .list xs => some xs

def Sexp.toAtom! : Sexp → String
  | .atom s  => s
  | .list xs => panic! s!"expected atom, found list at {List.toString xs}"

inductive SexpTok
  | sexp : Sexp →  SexpTok
  | opening : String.Pos → SexpTok
  deriving BEq, Inhabited, Repr

structure SexpState where
  it : String.Iterator
  stack : List SexpTok := []
  sexps : List Sexp := []
  depth : Nat := 0
  deriving BEq, Repr

def SexpState.fromString (s : String) : SexpState where
  it := s.iter

instance : Inhabited SexpState where
  default := SexpState.fromString ""

inductive SexpError
  | unmatchedOpenParen (ix: String.Iterator) : SexpError
  | unmatchedCloseParen (ix: String.Iterator) : SexpError
  | notSingleSexp (s: String) (xs: List Sexp) : SexpError
  deriving BEq, Repr

instance : ToString SexpError where 
  toString 
    | .unmatchedOpenParen ix => s!"Unmatched open parenthesis at {ix}"
    | .unmatchedCloseParen ix => s!"Unmatched close parenthesis at {ix}"
    | .notSingleSexp s xs => s!"not a single sexp '{s}', parsed as: '{xs}'"

abbrev SexpM := EStateM SexpError SexpState

def SexpM.peek : SexpM (Option (Char × String.Pos)) := do
  let state ← get
  return if state.it.atEnd then none else some (state.it.curr, state.it.i)

def SexpM.curPos : SexpM String.Pos := do
  let state ← get
  return state.it.i

def SexpM.mkSubstring (l : String.Pos) (r : String.Pos) : SexpM Substring := do
  let state ← get
  return { str := state.it.s, startPos := l, stopPos := r}

def SexpM.advance: SexpM Unit := do
  modify (fun state => { state with it := state.it.next })

def SexpM.pushTok (tok: SexpTok): SexpM Unit := do
  modify (fun state => { state with stack := tok :: state.stack })

def SexpM.pushSexp (sexp: Sexp): SexpM Unit := do
  let state ← get
  if state.stack.length == 0 then 
    set { state with stack := [], sexps := sexp :: state.sexps }
  else 
    set { state with stack := (SexpTok.sexp sexp) :: state.stack }

def SexpM.incrementDepth: SexpM Unit :=
  modify (fun state => { state with depth := state.depth + 1 })

def SexpM.decrementDepth: SexpM Unit :=
  modify (fun state => { state with depth := state.depth - 1 })

instance [Inhabited α] : Inhabited (SexpM α) := by infer_instance

def SexpM.pop: SexpM SexpTok := do
  let state ← get
  match state.stack with
  | [] => panic! "empty stack"
  | x :: xs =>
      set { state with stack := xs }
      return x

-- Remove elements from the stack of tokens `List SexpToken` till we find a `SexpToken.opening`.
-- When we do, return (1) the position of the open paren, (2) the list of SexpTokens left on the stack, and (3) the list of Sexps
-- Until then, accumulate the `SexpToken.sexp`s into `sexps`.
def stackPopTillOpen (stk : List SexpTok) (sexps : List Sexp := []) : 
  Option (String.Pos × (List SexpTok) × (List Sexp)) :=
  match stk with
  | [] => .none
  | SexpTok.opening openPos :: rest => (.some (openPos, rest, sexps))
  | SexpTok.sexp s :: rest => stackPopTillOpen rest (s :: sexps)

/-- Collapse the current stack till the last ( into a single `Sexp.list`. -/
def SexpM.matchClosingParen: SexpM Unit := do
  let state ← get
  match stackPopTillOpen state.stack with
  | some (_, stk, sexps) =>
      let sexp := Sexp.list sexps
      modify (fun state => { state with stack := stk })
      SexpM.pushSexp sexp
  | none => throw (SexpError.unmatchedCloseParen state.it)

partial def SexpM.takeString (startPos : String.Pos) : SexpM Substring := do
  match (← SexpM.peek) with
  | none => SexpM.mkSubstring startPos (← SexpM.curPos)
  | some (' ', _) => SexpM.mkSubstring startPos (← SexpM.curPos)
  | some ('(', _) => SexpM.mkSubstring startPos (← SexpM.curPos)
  | some (')', _) => SexpM.mkSubstring startPos (← SexpM.curPos)
  | some _ => do
      SexpM.advance
      SexpM.takeString startPos

partial def SexpM.parse : SexpM Unit := do
  match (← SexpM.peek) with
  | some ('(', i) => do
      SexpM.advance
      SexpM.pushTok (SexpTok.opening i)
      SexpM.incrementDepth
      SexpM.parse
  | some (')', _) => do
      SexpM.advance
      SexpM.matchClosingParen
      SexpM.parse
  | some (' ', _) => do
      SexpM.advance
      SexpM.parse
  | some (_, i) => do
      let s ← SexpM.takeString i
      SexpM.pushSexp ((Sexp.atom s.toString))
      SexpM.parse
  | .none => do
      let state ← get
      match stackPopTillOpen state.stack with
      | some (openPos, _, _) => throw <| 
          SexpError.unmatchedOpenParen ({ s := state.it.s, i := openPos })
      | none => return ()

/-- Parse a list of (possibly empty) sexps. -/
def parseSexpList (s: String):  Except SexpError (List Sexp) :=
  let initState := SexpState.fromString s
  match EStateM.run SexpM.parse initState with
  | .ok () state => .ok state.sexps.reverse
  | .error e _ => .error e

/-- Parse a single s-expression, and error if found no sexp or multiple sexps. 
-/
def parseSingleSexp (s: String): Except SexpError Sexp := do
  match (← parseSexpList s) with
  | [x] => .ok x
  | xs => .error (.notSingleSexp s xs)

-- To simplify Sexps, we want to replace some subterms in an Sexp:
-- Have to mark this as partial since the termination checker doesn't like
-- these higher-order functions like map. See: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.E2.9C.94.20using.20higher-order.20functions.20on.20inductive.20types.3A.20termin.2E.2E.2E
partial def replaceTerm 
  (toReplace : Sexp) (replaceWith : Sexp) (atSexp : Sexp) : Sexp :=
  if toReplace == atSexp then 
    replaceWith
  else 
    match atSexp with
    | .atom _ => atSexp
    | .list sexps => sexps.map <| replaceTerm toReplace replaceWith

-- The idea of this simplification is to do substitutions that replace a term,
-- such that the replaced term never appears as a proper subterm elsewhere in
-- the request, i.e. neither as the goal/starting point nor in any of the
-- rewrites. Ideally maximal subterms with this property

-- For this, we start by finding wether a subexpression is contained in an Sexp
-- Yes, this is not optimal because of the checks, feel free to rewrite.

/-- Need this order of arguments (awkward for recursive call) for `.` notation.
-/
partial def Sexp.containsSubexpr (mainExpr : Sexp) (subExpr : Sexp) : Bool :=
  if subExpr == mainExpr then 
    true
  else 
    match mainExpr with
    | .atom _ => false
    | .list sexps => sexps.any (containsSubexpr · subExpr)

partial def Sexp.vars : Sexp → List String
  | .atom s => [s]
  | .list sexps => List.join <| sexps.map vars

partial def Sexp.fvarsConstsVars : Sexp → List Sexp × List Sexp × List String
  | .atom s => ([], [], [s])
  | c@(.list ("const" :: _)) => ([], [c], [])
  | fvar@(.list ("fvar" :: _)) => ([fvar], [], [])
  | .list sexps => sexps.foldl (init := ([], [], []))
      fun (consts, fvars, vars) sexp =>
      let res := sexp.fvarsConstsVars
      (consts.append res.1, fvars.append res.2.1, vars.append res.2.2)

-- We could maybe replace this with `Std.HashMap`, but this should do it for now.
abbrev VariableMapping := List (String × Sexp)

def freshVar (vars : List String) : String := Id.run do
  let mut idx := vars.length
  let mut fresh := s!"v{idx}"
  while vars.contains fresh do
    idx := idx + 1
    fresh := s!"v{idx}"
  return fresh

def Sexp.head : Sexp → String
  | .atom s => s
  | .list [] => ""
  | .list (hd::_) => head hd

def Sexp.uncurry : Sexp → Sexp
  | a@(.atom _) => a
  | .list [
      "ap", .list [
        "ap", .list [
          "ap", .list [
            "ap", .atom fname, args4
          ], args3
        ], args2
      ], args1
    ] => 
      .list [
        .atom s!"ap4-{fname}", 
        args4.uncurry, 
        args3.uncurry, 
        args2.uncurry, 
        args1.uncurry
      ]
  | .list [
      "ap", .list [
        "ap", .list [
          "ap", .atom fname, args3
        ], args2
      ], args1
    ] => 
      .list [
        .atom s!"ap3-{fname}", 
        args3.uncurry, 
        args2.uncurry, 
        args1.uncurry
      ]
  | .list [
      "ap", .list [
        "ap", .atom fname, args2
      ], args1
    ] => 
      .list [
        .atom s!"ap2-{fname}", 
        args2.uncurry, 
        args1.uncurry
      ]
  | .list ["ap", (.atom fname), args] => .list [s!"ap-{fname}", args.uncurry]
  | l@(.list _) => l

-- partial because of map..
partial def Sexp.curry : Sexp → Sexp
  | a@(.atom _) => a
  | .list [(.atom (.mk ('a'::'p'::'4'::'-'::fname))), args4, args3, args2, args1] => 
      .list ["ap", (.list ["ap", (.list ["ap", (.list ["ap", (.atom (.mk fname)), args4.curry]), args3.curry]), args2.curry]), args1.curry]
  | .list [(.atom (.mk ('a'::'p'::'3'::'-'::fname))), args3, args2, args1] => 
      .list ["ap", (.list ["ap", (.list ["ap", (.atom (.mk fname)), args3.curry]), args2.curry]), args1.curry]
  | .list [(.atom (.mk ('a'::'p'::'2'::'-'::fname))), args2, args1] => 
      .list ["ap", (.list ["ap", (.atom (.mk fname)), args2.curry]), args1.curry]
  | .list [(.atom (.mk ('a'::'p'::'-'::fname))), args] => 
      .list ["ap", (.atom (.mk fname)), args.curry]
  | l@(.list _) => l

def simplifySexps : List Sexp → List Sexp × VariableMapping
  | sexps =>
    let fvarsConstsVars := sexps.foldl (init := ([], [], []))
      fun (fvs, cs, vs) exp =>
        let res := exp.fvarsConstsVars
        ((fvs ++ res.1).unique, (cs ++ res.2.1).unique, (vs ++ res.2.2).unique)
    let fvars := fvarsConstsVars.1
    let consts := fvarsConstsVars.2.1
    Id.run do
      let mut allVars := fvarsConstsVars.2.2
      let mut mapping := []
      let mut exps := sexps
      for fvar in fvars do
        let vname := freshVar allVars
        mapping := (vname, fvar) :: mapping
        allVars := vname :: allVars
        exps := exps.map fun exp => replaceTerm fvar (.atom vname) exp
      for c in consts do
        let vname := freshVar allVars
        mapping := (vname, c) :: mapping
        allVars := vname :: allVars
        exps := exps.map fun exp => replaceTerm c (.atom vname) exp
      return (exps, mapping)

def Sexp.unsimplify : Sexp →  VariableMapping → Sexp
  | sexp, mapping => sexp.vars.foldl (init := sexp) fun e var => 
      match mapping.lookup var with
      | none => e
      | some subexp => replaceTerm (Sexp.atom var) subexp e

def unsimplifySExps : List Sexp →  VariableMapping → List Sexp
  | sexps, mapping => sexps.map fun exp => 
      exp.vars.foldl (init := exp) fun e var => 
        match mapping.lookup var with
        | none => e
        | some subexp => replaceTerm (Sexp.atom var) subexp e
