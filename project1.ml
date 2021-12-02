type proposition =  
  False |  
  True |  
  Var of string |  
  And of proposition * proposition |  
  Or of proposition * proposition |  
  Not of proposition |  
  Imply of proposition * proposition |  
  Equiv of proposition * proposition |  
  If of proposition * proposition * proposition

let rec ifify p = 
  match p with 
  Not(prop1) -> If(ifify prop1, False, True)
  | And(prop1, prop2) -> If(ifify prop1, ifify prop2, False)
  | Or(prop1, prop2)  -> If(ifify prop1, True, ifify prop2)
  | Imply(prop1, prop2)  -> If(ifify prop1, ifify prop2, True)
  | Equiv (prop1, prop2) -> If(prop1, prop2, If(ifify prop2, False, True))
  | _ -> p

let rec normalize c =
  let rec normalizing pi a1 b1 =
  match pi with
    If(d, a2, b2) -> normalizing d (If(a1, a2, b2)) (If(b1, a2, b2)) 
    | _ -> If(pi, normalize(a1), normalize(b1))
in match c with
  If(pi, a1, b1) -> normalizing pi a1 b1
  | _ -> c;;

let rec substitute c v b = 
  match c with
  If(a, d, e) -> If(substitute a v b, substitute d v b, substitute e v b)
  | _ -> if(c = v)
            then b
          else c ;;

let rec simplify c =
  match c with 
  |If(True, a, _) -> simplify (a)
  |If(False, _, b) -> simplify (b)
  |If(pi, True, False) -> pi
  |If(pi, a, b) -> 
  let a = simplify(substitute (a) (pi) (True))
  in let b = simplify(substitute (b) (pi) (False))
                    in if a = b 
                      then a 
                    else 
                      If(pi, a, b)
  | _ -> c ;;

let tautology p =
  simplify(normalize(ifify(p))) = True;;


tautology(And(Var "p", Var "q"));; (*Returns False*)
tautology(If(Var "a", False, True));; (*Returns False*)
tautology (Or(Var "p", (Not(Var "p"))));; (*Return True*)