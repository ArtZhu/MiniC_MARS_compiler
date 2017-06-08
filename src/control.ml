module Q = Quads
module A = Ast
(*name: operation and function calls only on variables*)
(*lift: no nested lets*)

let getLabel maybeLabel =
  match maybeLabel with
  | None -> Label.fresh()
  | Some label -> label

type transExprOut = {iList : Q.instruction list; rhs : Q.rhs}

let mark label = [Q.Instruction {label = Some label; op = Q.Noop}]
let jump label = [Q.Instruction {label = None; op = Q.Jmp label}]

let terms2opnds x = List.map
    (fun x -> match x with
    | A.Id sym -> Q.Id sym
    | _ -> failwith "Control.terms2opnds: Should not happen")
    x

let invoke rator terms =
  let name = Label.fromString (Symbol.format rator) in
  {iList = []; rhs = Q.FunCall {label = name; opnds = terms2opnds terms}}

let initialize decls = List.map
    (fun A.{id = sym; typ} -> match typ with
       | Typ.Int -> [Q.Instruction {label = None; op = Q.Gets {dst = Q.Id sym; src = Q.Operand (Q.Word {typ; bits = 0})}}]
       | Typ.Bool -> [Q.Instruction {label = None; op = Q.Gets {dst = Q.Id sym; src = Q.Operand (Q.Word {typ; bits = 0})}}] (*Bool defaults to false*)
       | _ -> [])
    decls

let rec translate (A.Program procedures) =
  List.map translateProcedure procedures

and translateProcedure (A.Procedure {id; typ; formals; body}) =
  let name = Label.fromString (Symbol.format id) in
  let formals = List.map A.(fun bv -> bv.id) formals in
  let block' = translateStatement body in
  Q.Procedure {entry = name; formals = formals; code = block'}

and translateStatement ast = match ast with
  | A.Block {decls; statements} -> List.concat (List.concat ((initialize decls)::[List.map translateStatement statements]))
  | A.Assign {id; expr} ->
    let expr' = translateExpression expr in
    (expr'.iList @ [Q.Instruction {label = None; op = Q.Gets {dst = Q.Id id; src = expr'.rhs}}])
  | A.While {expr; statement} ->
    let expr' = translateExpression expr in
    let startL = Label.fresh() in
    let endL = Label.fresh() in
    let switch = [Q.Instruction {label = None; op = Q.JmpZero {cond = expr'.rhs; dest = endL}}] in
    List.concat ((mark startL)::expr'.iList::switch::(translateStatement statement)::(jump startL)::[mark endL])
  | A.IfS {expr; thn; els} ->
    let expr' = translateExpression expr in
    let switchL = Label.fresh() in
    let endL = Label.fresh() in
    let switch = [Q.Instruction {label = None; op = Q.JmpZero {cond = expr'.rhs; dest = switchL}}] in
    List.concat (expr'.iList::switch::(translateStatement thn)::(jump endL)::(mark switchL)::(translateStatement els)::[mark endL])
  | A.Call {rator; rands} ->
    let rands' = List.map translateExpression rands in
    let iList = List.concat (List.map (fun x -> x.iList) rands') in
    let oList = List.map (fun x -> Q.Id (Symbol.fresh())) rands in
    let passId = (List.map2 (fun x y -> Q.Instruction {label = None; op = Q.Gets {dst = x; src = y.rhs}}) oList rands') in
    let name = Label.fromString (Symbol.format rator) in
    List.concat (iList::passId::[[Q.Instruction {label = None; op = Q.Call {label = name; opnds = oList}}]])
  | A.Print expr ->
    let expr' = translateExpression expr in
    let resultId = Q.Id (Symbol.fresh()) in
    let passId = [Q.Instruction {label = None; op = Q.Gets {dst = resultId; src = expr'.rhs}}] in
    let print = [Q.Instruction {label = None; op = Q.Print (Q.Operand resultId)}] in
    List.concat (expr'.iList::passId::[print])
  | A.Return expr ->
    let expr' = translateExpression expr in
    let resultId = Q.Id (Symbol.fresh()) in
    let passId = [Q.Instruction {label = None; op = Q.Gets {dst = resultId; src = expr'.rhs}}] in
    let return = [Q.Instruction {label = None; op = Q.Ret resultId}] in
    List.concat (expr'.iList::passId::[return])

and translateExpression expr =
  match expr with
  | A.Id sym -> {iList = []; rhs = Q.Operand (Q.Id sym)}
  | A.Literal {typ; bits} -> {iList = []; rhs = Q.Operand (Q.Word {typ; bits})}
  | A.App {rator; rands = (A.Id sym1)::[A.Id sym2] as terms} ->
    (match Bases.isPrim rator with
     | true -> {iList = []; rhs = Q.BinPrimOp {op = rator; opnds = {Q.src1 = Q.Id sym1; Q.src2 = Q.Id sym2}}}
     | false -> invoke rator terms)
  | A.App {rator; rands = [A.Id sym] as terms} ->
    (match Bases.isPrim rator with
     | true -> {iList = []; rhs = Q.UnPrimOp {op = rator; opnd = Q.Id sym}}
     | false -> invoke rator terms)
  | A.App {rator; rands} -> invoke rator rands
  | A.If {expr; thn; els} ->
    let expr', thn', els' = translateExpression expr, translateExpression thn, translateExpression els in
    let resultId = Q.Id (Symbol.fresh()) in
    let switchL = Label.fresh() in
    let endL = Label.fresh() in
    let switch = [Q.Instruction {label = None; op = Q.JmpZero {cond = expr'.rhs; dest = switchL}}] in
    let passId texpr = [Q.Instruction {label = None; op = Q.Gets {dst = resultId; src = texpr.rhs}}] in
    {iList = List.concat (expr'.iList::switch::thn'.iList::(passId thn')::(jump endL)::(mark switchL)::els'.iList::(passId els')::[mark endL]);
     rhs = Q.Operand resultId}
  | A.And _ -> failwith "Control.translateExpression: Ast.And should have been eliminated by Name"
  | A.Or _ -> failwith "Control.translateExpression: Ast.Or should have been eliminated by Name"
  | A.Let {decl = A.ValBind {bv = A.{id; typ}; defn}; body} ->
    let defn' = translateExpression defn in
    let body' = translateExpression body in
    let passId = [Q.Instruction {label = None; op = Q.Gets {dst = Q.Id id; src = defn'.rhs}}] in
    {iList = List.concat(defn'.iList::passId::[body'.iList]); rhs = body'.rhs}
  | A.Let {decl = A.FunBind _ ; body} -> failwith "Control.translateExpression: Ast.FunBind is not implemented"
