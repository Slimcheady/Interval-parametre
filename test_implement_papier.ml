type interval_parametre = { label : string; mutable min : parametre ;mutable max : parametre}
type parametre = { label: string; mutable min: int; mutable max : int};;
type interval = {mutable label: string ; mutable min : int; mutable max : int; };;
type op =
  | Plus of interval         (* a + b *)
  | Minus of interval;;        (* a - b *)
type ctr =
  | Lower                   (*<*)
  | Lower_equals            (*<=*)
  | Greater                 (*>*)
  | Greater_equals         (*>=*)
  | Equals         ;;         (*=*)
type exp =
  | Exp of  exp* op* exp
  | Var of interval
  | Cst of interval  ;;
type  arbre =
  | Top of exp * ctr * exp
(*  | Leaf of exp
    | Node of exp * op * exp;; *)
let op_to_string x =
  match x with 
  | Plus(y)    -> "+"
  | Minus(y)   -> "-"
let ctr_to_string = function
  | Lower -> "<"
  | Lower_equals   -> "<="
  | Greater -> ">"
  | Greater_equals   -> ">="
  | Equals ->   "="
       
let print_op chan v = output_string chan (op_to_string v)
(*
let intersect_intervalle (a : interval) (b : interval)   =
  if a.min > b.max || b.min > a.max then {label="Intervalle vide"; min= -99999; max= 99999} else
    {label= a.label^ " intersect "^b.label  ;min= (max a.min b.min);max= (min a.max b.max) };;
*)
let intersect_intervalle (a : interval) (b : interval)   =
  if a.min > b.max || b.min > a.max then (a.label<-"Intervalle vide";a.min<- -99999; a.max<- 99999;b.label<-"Intervalle vide";b.min<- -99999; b.max<- 99999) else (
    a.label<- a.label ;a.min<- (max a.min b.min); a.max<- (min a.max b.max) ;
  b.label<- a.label ;b.min<- (max a.min b.min); b.max<- (min a.max b.max)) ;;

let union_intervalle a b =
  {label=a.label^ " union "^b.label ;min= (min a.min b.min);max= (max a.max b.max)} ;;

let lower_equals_intervalle (a: interval)  (b : interval)  =
    let b_bis = {label = "b_bis"; min = -99999; max = b.max} and a_bis = {label ="a_bis"; min = a.min ; max = 99999} in ( intersect_intervalle a b_bis , intersect_intervalle b a_bis) ;;

let equals_intervalle a b =
  ( intersect_intervalle a b , intersect_intervalle b a) ;;

let plus_intervalle a b=
    {label = a.label^"+"^b.label; min = a.min + b.min; max= a.max + b.max};;

let moins_intervalle a b =
  {label = a.label^"-"^b.label; min = a.min - b.max; max= a.max-  b.min};;


let interval_op op =    (* op -> interval *)
  match op with
  |Minus(x) -> x
  |Plus(x)  -> x;;

let interval_exp exp =   (* exp -> interval *)
  match exp with
  |Exp(exp,op,exp2) -> interval_op op
  |Var n -> n
  |Cst n -> n;;

let operateur_up op a b  =      (* Met a jours les opérateurs pdt la remontée *)
  let lab = a.label^" "^(op_to_string op)^" "^b.label; in
  match op with
  |Plus(x)   -> x.label<-lab;x.min<- a.min + b.min; x.max<- a.max + b.max;x;
  |Minus(x)  -> x.label<-lab; x.min<- a.min - b.max; x.max<- a.max - b.min;x;;

let operateur_ctr ctr a b =  (* Met a jours les intervalles sur l'opérateur de contraintes *)
  match ctr with
  |Greater_equals -> lower_equals_intervalle b a;
  |Lower_equals   -> lower_equals_intervalle a b;
  |Equals         -> equals_intervalle a b;;
(*|Greater ->
  |Lower -> TODO *)

let rec up_tree (exp: exp)  =       (*  Remonte l'arbre (pour mettre a jour les op par operateur_up) *)
  match exp with
  |Var n -> n
  |Cst n -> n
  |Exp (exp1,op,exp2) -> operateur_up op (up_tree exp1) (up_tree exp2);; 

let top tree =                      (* Fonction qui lance la remonté de l'arbre a partir du haut ,#recursif *)
  match tree with
  |Top(exp1,ctr,exp2) -> operateur_ctr ctr  (up_tree exp1) (up_tree exp2)  ;;

let down_tree op fd fg  =          (* Mets a jours les noeuds pendant la descente *)
  match op with
  |Plus(x)  -> fd.min <- x.min - fg.min; fd.max <- x.max - fg.max; fg.min<-x.min-fd.min;fg.max<-x.max-fd.min;(* TODO fd Inter fd_base pareil pour fg *)
   |Minus(x) -> fd.min <- fg.min - x.min;fd.max<-fg.max-x.max;fg.min<-x.min+fd.min;fg.max<-x.max+fd.max;; (* TODO fd Inter fd_base,pareil pour fg *)


let intersect_aux (a : interval) (b : interval)   =
  if a.min > b.max || b.min > a.max then (a.label<-"Intervalle vide";a.min<- -99999;a.max<- 99999) else
   ( a.label<- a.label ; a.min<- (max a.min b.min); a.max<- (min a.max b.max)) ;;


let down_tree op fd fg  =          (* Mets a jours les noeuds pendant la descente *)
  match op with
  |Plus(x)  -> let interval_aux_fd = {label="fd_aux"; min =x.min - fg.min;max = x.max - fg.max} in intersect_aux fd interval_aux_fd ; let interval_aux_fg =  {label="fg_aux"; min =x.min - fd.min;max = x.max - fd.max} in intersect_aux fg interval_aux_fg;
  |Minus(x) -> let interval_aux_fd = {label="fd_aux"; min =fg.min - x.min;max = fg.max - x.max} in intersect_aux fd interval_aux_fd ; let interval_aux_fg =  {label="fg_aux"; min =x.min + fd.min;max = x.max + fd.max} in intersect_aux fg interval_aux_fg;;

  

let rec down_aux exp =                     (* Fonctions principales de redescente *)
  match exp with
  |Var n -> n
  |Cst n -> n
  |Exp(exp1, op, exp2) -> down_tree op (interval_exp exp1) (interval_exp exp2) ;down_aux(exp1);down_aux(exp2);;

let down tree =
  match tree with
  |Top(exp1,ctr,exp2) -> down_aux exp1;;


let bottom_Up tree =
  top tree;
  down tree;;
  

let minus = {label= "-" ;min= 0;max= 0};;
Minus ( minus );;
let plus = {label= "+" ; min = 0; max = 0};;
Plus(plus);;

let y1 = {label="y"; min=1 ; max=55} ;;
let x1 = {label="x"; min=2; max=4};;
let z1 = {label="z"; min=4; max=7};;
let x= Var(x1);;
let y= Var(y1);;
let z=Var(z1);;

let ctr1 = Equals;;
let ctr2 = Lower_equals;;
let arbre1 = Top(Exp(x,Plus(plus),y),ctr2,z);;
top arbre1;;
down arbre1;;
 bottom_Up arbre1;;
 y1;;
 x1;;
 z1;;
 Plus(plus);;
 ctr1;;
plus;;










 
(*
let op_min op a b c = (*Pas encore utilisé (prob d'arg :s *)
  match op with
  |Minus(x) -> a.min <- b.min - c.min;
  |Plus(x)  -> a.min <- b.min + c.min;;

let op_max op a b c =           (*Pas encore utilisé (prob d'arg :s *)
  match op with
  |Minus(x) -> a.max <- b.max - c.max;
  |Plus(x)  -> a.max <- b.max + c.max;;
*)
