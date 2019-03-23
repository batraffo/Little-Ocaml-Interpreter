type ide = string;;
type exp =  Eint of int 
            | Ebool of bool 
            | Den of ide 
            | Prod of exp * exp 
            | Sum of exp * exp 
            | Diff of exp * exp 
            | Eq of exp * exp 
            | Minus of exp 
            | IsZero of exp 
            | Or of exp*exp 
            | And of exp*exp 
            | Not of exp 
            | Ifthenelse of exp * exp * exp 
            | Let of ide * exp * exp 
            | Fun of ide * exp 
            | FunCall of exp * exp
            | Letrec of ide * exp * exp
            | ETree of tree (* gli alberi sono anche espressioni *)
            | ApplyOver of exp * exp (* applicazione di funzione ai nodi *)
            | Update of (ide list) * exp * exp (* aggiornamento di un nodo *)   
            | Select of (ide list) * exp * exp (* selezione condizionale di un nodo *)
            and tree = Empty (* albero vuoto *)| Node of ide * exp * tree * tree (* albero binario *);;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | Unbound |Albero of ide*evT*evT*evT|Alberovuoto|Nodo of ide*evT*evT*evT |Nodovuoto| FunVal of evFun | RecFunVal of ide * evFun
and evFun = ide * exp * evT env


(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	_ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
        Letrec(f, funDef, letBody) ->
        		(match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1 |
            		_ -> failwith("non functional def"))|
        ETree alberello-> (match alberello with 
                                Empty->Alberovuoto|(*controllo se l'albero e' vuoto, se non lo e' allora valuto la radice e chiamo ricorsivamente una funzione ausiliare sui nodi*)
                                Node(nome,valore,sinis,des)->Albero((nome) ,(eval valore r), (evalnodo sinis r) , (evalnodo des r))|
                                _->failwith("valore non consentito"))|
        ApplyOver(funzione,albero)->(match (eval funzione r,eval albero r) with(*applico applyover sull'albero gia' valutato poi chiamo la funzione ausiliaria applynodo*)
                                        (_,Alberovuoto)->Alberovuoto |
                                        (FunVal(arg,body,ambiente),Albero(name,espr,ns,nd))->Albero(name,eval body(bind ambiente arg espr),applynodo funzione ns r , applynodo funzione nd r)|
                                        (_,_)->failwith("valore non consentito"))| 
        Update (cammino,funzione,albero)->(match (cammino,eval funzione r,eval albero r) with
                                                ([],_,_)->eval albero r|(*se non passo nessun cammino allora restituisco semplicemente l'albero valutato*)
                                                (_,_,Alberovuoto)->Alberovuoto|
                                                (x::[],FunVal(arg,body,ambiente),Albero(name,espr,ns,nd))->if x=name then Albero(name,eval body(bind ambiente arg espr), ns , nd ) else Albero(name,espr,ns,nd)|
                                                (x::xs,FunVal(arg,body,ambiente),Albero(name,espr,ns,nd))->if x=name then Albero(name,espr,updatenodo xs funzione ns r , updatenodo xs funzione nd r) else Albero(name,espr,ns,nd)|(*restituisco l'albero valutato senza nessuna modifica se il cammino passato e' sbagliato (non parte con la radice)*)
                                                (_,_,_)->failwith("valore non consentito"))|
    Select (cammino,funzione,albero)->(match (cammino,eval funzione r, eval albero r) with
                                                ([],_,_)->Alberovuoto|
                                                (_,_,Alberovuoto)->Alberovuoto|
                                                (x::[],FunVal(arg,body,ambiente),Albero(name,espr,ns,nd))->if x<>name then Alberovuoto else if eval body(bind ambiente arg espr)=Bool(true) then Albero(name,espr,ns,nd) else Alberovuoto|
                                                (x::xs,FunVal(arg,body,ambiente),Albero(name,espr,ns,nd))->if x<>name then Alberovuoto else (selectnodo xs funzione (trovanodo ns nd xs) r)|
                                                (_,_,_)->failwith("valore non consentito"))
                                and trovanodo (dx:evT) (sx:evT) (c:ide list):evT=(match(sx,dx,c) with
                                    (_,_,[])->Nodovuoto|
                                    (Nodovuoto,Nodo(nome,valor,s,d),x::xs)->if x=nome then dx else Nodovuoto|
                                    (Nodovuoto,Nodovuoto,_)->Nodovuoto|
                                    (Nodo(v,l,m,n),Nodovuoto,x::xs)->if x= v then sx else Nodovuoto|
                                    (Nodo(v,l,m,n),Nodo(nome,valor,s,d),x::xs)->if x=v then sx else if x=nome then dx else Nodovuoto|(*se nessun nodo e' nel cammino allora restituisco un albero vuoto*)
                                    (_,_,_)->failwith("valore non consentito"))
                                and selectnodo (c:ide list) (funzione:exp) (n:evT) (r: 't env):evT= (match(c,eval funzione r,n) with
                                    ([],_,_)->Alberovuoto|
                                    (_,_,Nodovuoto)->Alberovuoto|
                                    (x::[],FunVal(arg,body,ambiente),Nodo(nomes,espr,sinistra,destra))->if eval body(bind ambiente arg espr)=Bool(true) then Albero(nomes,espr,sinistra,destra) else Alberovuoto|
                                    (x::xs,FunVal(arg,body,ambiente),Nodo(nomes,espr,sinistra,destra))->(selectnodo xs funzione (trovanodo sinistra destra xs) r)|
                                    (_,_,_)->failwith("valore non consentito"))
                                and updatenodo (c:ide list) (funzione:exp) (n:evT) (r: 't env):evT=(match(c,eval funzione r,n) with
                                    ([],_,_)->n|
                                    (_,_,Nodovuoto)->Nodovuoto|
                                    (x::[],FunVal(arg,body,ambiente),Nodo(nomes,espr,sinistra,destra))->if x=nomes then Nodo((nomes),eval body(bind ambiente arg espr),sinistra ,  destra ) else Nodo(nomes,espr,sinistra,destra)|
                                    (x::xs,FunVal(arg,body,ambiente),Nodo(nomes,espr,sinistra,destra))->if x=nomes then Nodo((nomes),espr,updatenodo xs funzione sinistra r, updatenodo xs funzione destra r) else Nodo(nomes,espr,sinistra,destra)|
                                    (_,_,_)->failwith("valore non consentito"))
                                and applynodo (funzione : exp) (n:evT) ( r: 't env):evT=(match(eval funzione r,n) with
                                    (_,Nodovuoto)->Nodovuoto|
                                    (FunVal(arg,body,ambiente),Nodo(nomes,espr,sinistra,destra))->Nodo((nomes),eval body(bind ambiente arg espr),applynodo funzione sinistra r, applynodo funzione destra r)|(*funzione ausiliaria ricorsiva di applyover sui nodi*)
                                    (_,_)->failwith("valore non consentito"))
                                and evalnodo (n:tree) (r: 't env) :evT=
                                           ( match n with
                                                Empty->Nodovuoto|
                                                Node(nome,valore,sinist,des)->Nodo((nome) ,(eval valore  r),(evalnodo sinist r) , (evalnodo des r))|(*funzione ausiliaria per valutare i nodi*)
                                                _->failwith("valore non consentito"));;
(* =============================  TESTS  ================= *)

let env0 = emptyenv Unbound;;
let env1= bind env0 "ciao" (Int(5)) ;;
let camminodiprova=ETree(Node("a", Eint 6, Node("b", Den("ciao"), Empty, Empty),
                         Node("c", Eint 3, Empty, Empty)));;
eval camminodiprova env1;;
let funzionee = Fun("z",Sum(Den"z",Eint 1));;
let applai=ApplyOver(funzionee,camminodiprova);;
eval applai env1;;
let lista=[("a");("c")];;
let vediamoseva=Update(lista,funzionee,camminodiprova);;
eval vediamoseva env1;; 
let ve=Update([],funzionee,camminodiprova);;
eval ve env1;;
let funzione=Fun("f",Eq(Den"f",Eint 3));;
let veer=Select(lista,funzione,camminodiprova);;
eval veer env1;;
let camminodue=ETree(Node("a", Eint 6, Node("b", Den("ciao"), Empty, Empty),
                         Node("c", Eint 3, Node("ca",Eint 4,Empty,Empty) , Empty)));;
let com=Select(lista,funzione,camminodue);;
eval com env1;;
let altrafunzione=Fun("g",Prod(Den("g"),Eint 2));;
let altraprova=ApplyOver(altrafunzione,camminodue);;
eval altraprova env1;;
let listaa=[("a");("d")];;
let noncambianulla=Update(listaa,funzionee,camminodue);;
eval noncambianulla env1;;
let altralista=[("a");("c");("ca")];;
let v=Update(altralista,altrafunzione,camminodue);;
eval v env1;;
let nfunzione=Fun("f",Eq(Den"f",Eint 6));;
let test=Select(listaa,nfunzione,camminodue);;
eval test env1;;
let camminotre=ETree(Node("a", Eint 6, Node("c", Den("ciao"), Empty, Empty),
                         Node("c", Eint 3, Node("ca",Eint 4,Empty,Empty) , Empty)));;
let vaasinistra=Select(lista,funzione,camminotre);;
eval vaasinistra env1;;
let altrafunzioneuno=Fun("f",Eq(Den"f",Eint 5));;
let vaasinistraelodimostro=Select(lista,altrafunzioneuno,camminotre);;
eval vaasinistraelodimostro env1;;
let funzionefinale=Fun("f",Eq(Den"f",Eint 4));;
let ultimotest=Select(altralista,funzionefinale,camminotre);;
eval ultimotest env1;;