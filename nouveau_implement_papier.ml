type interval = {mutable label : string; mutable min : int; mutable max: int; };;
type interval_singleton = interval;;
type interval_attribut = interval ;;
let interval_vide = {label="Intervalle vide"; min= max_int; max= min_int}
type op =
    Plus  
  |Minus ;;
type ctr =
    | Lower                   (*<*)
  | Lower_equals            (*<=*)
  | Greater                 (*>*)
  | Greater_equals         (*>=*)
  | Equals         ;;         (*=*)

type cst =
  |Constante of interval_singleton;; 

type exp =
  | Exp of  exp* op* interval_attribut* exp 
  | Var of interval
  | Cst of cst  ;;
type  arbre =
  | Top of exp * ctr * cst  (* Comment mettre type Cst ?#TODO *)

let op_to_string x =
  match x with 
  | Plus    -> "+"
  | Minus   -> "-"
let ctr_to_string = function
  | Lower -> "<"
  | Lower_equals   -> "<="
  | Greater -> ">"
  | Greater_equals   -> ">="
  | Equals ->   "="
       
let print_op chan v = output_string chan (op_to_string v)

let interval_cst cst =
  match cst with
  |Constante n -> n

let intersect_intervalle (a:interval)(b:interval) =
  if a.min > b.max || b.min > a.max then interval_vide else
    {label= a.label^ " intersect "^b.label  ;min= (max a.min b.min);max= (min a.max b.max) };;

let union_intervalle a b =
  {label=a.label^ " union "^b.label ;min= (min a.min b.min);max= (max a.max b.max)} ;;

let lower_equals_intervalle_1 a b  =
  let b_bis = {label = "b_bis"; min = -99999; max = b.max}  in  intersect_intervalle a b_bis  ;;

let lower_equals_intervalle_2 a b  =
    let a_bis = {label ="a_bis"; min = a.min ; max = 99999} in  intersect_intervalle b a_bis ;;

let equals_intervalle a b =
  intersect_intervalle a b ;;

let maj_intervalle_attribut_lab (x:interval_attribut) a lab =
  x.label<-lab;x.min<- a.min; x.max<- a.max ;;
let maj_intervalle_attribut (x:interval_attribut) a  =
  x.label<-a.label; x.min<- a.min; x.max<- a.max ;;

let maj_intervalle_lab a b =
  a.label<-b.label; a.min <- b.min; a.max<- b.max;;

let maj_intervalle a b =
  a.min <- b.min; a.max<- b.max;;

let maj_intervalle_intervalle a b a_ancien b_ancien = (* met a jour _ancien avec les donné de a *)
  a_ancien.label <- a.label; a_ancien.min <- a.min; a_ancien.max <-a.max;
  b_ancien.label <- b.label; b_ancien.min <- b.min; b_ancien.max <-b.max;;

let plus_intervalle a b=
    {label = a.label^"+"^b.label; min = a.min + b.min; max= a.max + b.max};;

let moins_intervalle a b =
  {label = a.label^"-"^b.label; min = a.min - b.max; max= a.max-  b.min};;

let operateur_up a op (i:interval_attribut) b  =      (* Met a jours les opérateurs pdt la remontée *)
  let lab = a.label^" "^(op_to_string op)^" "^b.label; in
  match op with
  |Plus   -> maj_intervalle_attribut_lab i (plus_intervalle a b) lab;i;
  |Minus  -> maj_intervalle_attribut_lab i (moins_intervalle a b) lab;i;;(* RENVOIE UN INTERVALLE JUSTE POUR UP_TREE   #TODO!!!! *)

let operateur_ctr ctr a b =  (* Met a jours les intervalles sur l'opérateur de contraintes *)
  match ctr with
  |Greater_equals -> maj_intervalle_intervalle (lower_equals_intervalle_1 b a) (lower_equals_intervalle_2 b a) b a ;
  |Lower_equals -> maj_intervalle_intervalle (lower_equals_intervalle_1 a b) (lower_equals_intervalle_2 a b) a b ;
  |Equals -> let interval_equals =  equals_intervalle a b in maj_intervalle_intervalle interval_equals interval_equals a b ;;
(*|Greater ->
  |Lower -> TODO *)

let exp_intervall_return exp =
  match exp with
  |Var n -> n
  |Cst n -> interval_cst n
  |Exp(exp1,op,interval,exp2) -> interval;;

let rec up_tree (exp: exp)  =       (*  Remonte l'arbre (pour mettre a jour les op par operateur_up) *)
  match exp with
  |Var n -> n
  |Cst n -> interval_cst n
  |Exp (exp1,op,interval_attribut,exp2) -> operateur_up (up_tree exp1) op interval_attribut (up_tree exp2);;  (*Bug avec operateur_up , comment vas et cst peuvent retourner unit?? TODO *)

let top_aux exp1 ctr cst =
  up_tree exp1;operateur_ctr ctr (exp_intervall_return exp1) (interval_cst cst);;

let top tree =         (* Fonction qui lance la remonté de l'arbre a partir du haut *)
  match tree with
  |Top(exp1,ctr,cst) -> top_aux exp1 ctr cst  ;;

let check_intervalle a =
  if a.max < a.min then a.max<-a.min ;a;;

let down_calcul_op_fd op interval_attr fd fg =   (*calculs interval du fd sur noeud op. FD = EXP1*)
  match op with
  |Plus -> {label="fd_aux_+"; min = interval_attr.min - fg.min;max =  interval_attr.max - fg.max} ;
  |Minus ->  {label="fd_aux_-"; min =interval_attr.min + fg.min;max =  interval_attr.max+ fg.max} ;;

let down_calcul_op_fg op interval_attr fd fg = (*calculs interval du fg sur noeud op. FG = EXP2 *)
  match op with
  |Plus -> {label="fg_aux_+"; min = interval_attr.min-fd.min; max = interval_attr.max - fd.max};
  |Minus -> {label="fg_aux_-"; min = fd.min-interval_attr.min; max = fd.max - interval_attr.max } ;;

let down_tree op interval_attr fd fg =
 maj_intervalle fd (intersect_intervalle (check_intervalle (down_calcul_op_fd op interval_attr fd fg)) fd) ; maj_intervalle fg (intersect_intervalle (check_intervalle (down_calcul_op_fg op interval_attr fd fg)) fg);;

let interval_exp exp =   (* exp -> interval *)
  match exp with
  |Exp(exp,op,interval,exp2) -> interval
  |Var n -> n
  |Cst n -> interval_cst n;;

let rec down_aux exp =        (* Fonctions principales de redescente *) 
  match exp with
  |Var n -> ()
  |Cst n -> ()
  |Exp(exp1, op, interval_attr, exp2) -> down_tree op interval_attr (interval_exp exp1) (interval_exp exp2) ;down_aux(exp1);down_aux(exp2);;

let down tree =
  match tree with
  |Top(exp1,ctr,exp2) -> down_aux exp1;;

let bottom_Up tree =
  top tree;
  down tree;
  tree;;

let y4 = {label="y"; min=2 ; max=6} ;;
let y3 = {label="y1"; min=2 ; max=3} ;;
let d=Var(y4);;
let c=Var(y3);;
let zr = {label="z"; min=0; max=3};;
let z=Constante(zr);;
let minus = {label= "-" ;min= 0;max= 0};;
let arbre1 = Top(Exp(d,Minus,minus,c),ctr1,z);;
arbre1;;
top arbre1;;
down arbre1;;
bottom_Up arbre1;;

intersect_intervalle y4 y3;;


let yr = {label="y"; min=1 ; max=5} ;;
let xr = {label="x"; min=2; max=4};;
let zr = {label="z"; min=400; max=7000};;
let x= Var(xr);;
let y= Var(yr);;
let z=Constante(zr);;
let plus = {label= "+" ; min = 0; max = 0};;
let minus = {label= "-" ;min= 0;max= 0};;
let plus2 = {label= "+" ; min = 0; max = 0};;
let minus2 = {label= "-" ;min= 0;max= 0};;

let ctr1 = Equals;;
let ctr2 = Lower_equals;;

let y2 = {label="y1"; min=10 ; max=50} ;;
let x2 = {label="x1"; min=30; max=40};;
let z2 = {label="z1"; min=20; max=70};;
let x_= Var(x2);;
let y_= Var(y2);;
let z_=Var(z2);;

let ctr1 = Equals;;
let ctr2 = Lower_equals;;

let arbre1 = Top(Exp(x,Plus,plus,y),ctr1,z);;
let arbre2 = Top(Exp(x_,Plus,plus,Exp(y_,Minus,minus,z_)),ctr2,z);;
let arbre3 = Top(Exp(y,Plus,plus,Exp(x,Plus,plus2,Exp(x_,Minus,minus,Exp(y_,Minus,minus2,z_)))),ctr2,z );;

arbre1;;
top arbre1;;
down arbre1;;
bottom_Up arbre1;;

arbre2;;
top arbre2;;
down arbre2;;
bottom_Up arbre2;;

arbre3;;
top arbre3;;
down arbre3;;
bottom_Up arbre3;;

let plus3 = {label= "+" ; min = 0; max = 0};;
let minus3 = {label= "-" ;min= 0;max= 0};;
let plus4 = {label= "+" ; min = 0; max = 0};;
let minus4 = {label= "-" ;min= 0;max= 0};;
