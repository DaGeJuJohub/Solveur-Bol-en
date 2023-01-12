(*NOM : JOSEPH           Prenom:Darryll Geneve Junior     No Etudiant: 12015696
  NOM :FRARMA            Prenom: Yanis                    No Etudiant: 12002376*)

type eb = V of int | VRAI | FAUX | AND of eb * eb | OR of eb * eb |XOR of eb * eb | NAND of eb * eb |NOT of eb ;;

let monsysdeq = [( OR(V(1),V(2)), VRAI) ; ( XOR(V(1),V(3)) ,V(2)); ( NAND(V(1),AND(V(2),V(3))) ,VRAI)  ];; 

(*Partie 1*)
let rec appartient x l =
  match l with 
    []-> 1
  |x1:: ll1 ->
      if x1=x
      then 0
      else appartient x ll1 ;;

let rec concat l1 l2 = 
  match l1 with 
    [] -> l2 
  |x1::ll1 -> 
      if (appartient x1 l2) = 0
      then 
        (concat ll1 l2)
      else
        x1::(concat ll1 l2) ;; 

let rec first l =
  match l with 
    [] -> []
  |c1::ll1 ->
      match c1 with 
        (a,b) -> let c = first ll1
          in a :: c ;; 

let equations_gauche = first monsysdeq;;

let rec second l =
  match l with 
    [] -> []
  |c1::ll1 ->
      match c1 with 
        (a,b) -> let c = second ll1
          in b :: c ;; 

let equations_droite = second monsysdeq;;

let rec sys listeq =
  match listeq with
    [] -> [] 
  |[VRAI]->[]
  |[FAUX] ->[]
  |[OR(a,b)] -> concat (sys[a]) (sys [b])
  |[AND(a,b)] -> concat (sys[a]) (sys [b])
  |[NAND(a,b)] -> concat (sys[a]) (sys [b])
  |[XOR(a,b)] -> concat (sys[a]) (sys [b])
  |[NOT(a)] -> (sys[a])
  |[V(a)] -> [V(a)]
  |eqi::listeeqi -> concat (sys [eqi]) (sys listeeqi);;

let variables_gauche = sys equations_gauche ;;
let variables_droite = sys equations_droite ;;
  
let mes_variables = concat (variables_droite) (variables_gauche);;

(*PARTIE 2*)
let rec concat2 l1 l2 = 
  match l1 with 
    [] -> l2 
  |x1::ll1 ->
      x1::(concat2 ll1 l2) ;;

let rec tailleliste l =
  match l with
    [] -> 0
  |a1 :: ll1 -> 1 + tailleliste ll1 ;;

let rec exposant2 n =
  if n =0 
  then
    1 
  else
    2 * exposant2 (n-1);;

let rec ajoutervrai l x =
  if x = 0
  then l
  else 
    VRAI :: ajoutervrai l (x-1);;

let rec ajouterfaux l x =
  if x = 0
  then l
  else 
    FAUX:: ajouterfaux l (x-1);;
  
let rec remplir l x n =
  if n = 0
  then [] 
  else
    let l1 = remplir (l) (x) (n-(2*x))
    in concat2 l1 (concat2 (ajoutervrai l x) (ajouterfaux l x)) ;; 

let rec tableaudeverite l taille = 
  match l with 
    [] -> []
  |x1:: ll1 -> 
      if ((tailleliste l) > 0)
      then 
        let ll = tableaudeverite ll1 taille
            (*in
        let l2 = ll :: []*)
        in concat2  ((remplir [] (exposant2 ((tailleliste l)-1)) (taille))) ll
      else
        [];; 
let rec couper l taille =
  match l with 
    [] -> []
  |x1::l1 ->
      if (taille > 0)
      then
        let a = couper l1 (taille-1)
        in x1 ::a 
      else 
        [];;


couper [2;5;4;6;0;9] 4 ;;
  
  
let rec couperreste l taille =
  match l with 
    [] -> []
  |x1::l1 ->
      if (taille > 0)
      then
        couperreste l1 (taille-1)
      else 
        let a = couperreste l1 (taille-1)
        in x1 :: a ;;
couperreste [2;5;4;6;0;9] 4;;


let  rec couperall l taille = 
  match l with 
    []->[]
  |x1::ll1 -> 
      let a = couperall (couperreste l taille ) (taille) 
      in (couper l taille )::a ;;

couperall [2;5;1;6;0;9] 2;; 
  


let rec premier l =
  match l with 
    [] ->[]
  |l1:: ll1->
      match l1 with 
        [] ->[]
      |x1::ll -> 
          let a = premier ll1
          in   x1 :: a ;; 

let rec supppremier l =
  match l with 
    [] ->[]
  |l1:: ll1->
      match l1 with 
        [] ->[]
      |x1::ll -> 
          let a = supppremier ll1
          in   ll :: a ;; 

let  rec premierall l = 
  match l with 
    []->[]
  |l1::ll1 -> 
      match l1 with
        []->[] 
      |x1::ll1 ->
          let a = premierall (supppremier l) 
          in premier l ::a ;; 


let gen_env l = 
  let l1= tableaudeverite l (exposant2(tailleliste l))
  in premierall ( couperall l1 (exposant2 (tailleliste l)))
    
;;

let mes_environnements = gen_env (mes_variables) ;;

let mes_environnements_associes = List.map (fun mes_environnements->List.combine mes_variables mes_environnements)mes_environnements ;;

(*PARTIE 3*)
let rec valeurassocie v listecouple =
  match listecouple with 
    [] -> FAUX
  |e::ll1 -> 
      if v = fst(e) 
      then snd(e)
      else 
        valeurassocie v ll1 ;;

let rec remplacervaleur lenv eq=
  match eq with 
    V(a) -> valeurassocie (V(a)) (lenv)
  |VRAI ->VRAI
  |FAUX ->FAUX
  |OR (a ,b) -> OR((remplacervaleur lenv a) , (remplacervaleur lenv b)) 
  |AND (a ,b) -> AND((remplacervaleur lenv a) , (remplacervaleur lenv b))
  |XOR (a ,b) -> XOR((remplacervaleur lenv a) , (remplacervaleur lenv b))
  |NAND (a ,b) -> NAND((remplacervaleur lenv a) , (remplacervaleur lenv b))
  |NOT (a) -> NOT((remplacervaleur lenv a));; 

let rec testegalite couple =
  match couple with 
    (a,b)->
      if a = b 
      then 1 
      else 0;;

let rec evaluer p =
  match p with 
    V(i) ->  V(i)
  |VRAI -> VRAI 
  |FAUX ->FAUX
  |NOT(VRAI)-> FAUX
  |NOT(FAUX)-> VRAI 
  |NOT(a)-> evaluer (NOT(evaluer a))
  |AND(VRAI, VRAI)->VRAI
  |AND(VRAI,FAUX) ->FAUX
  |AND(FAUX,VRAI) -> FAUX
  |AND(FAUX,FAUX)-> FAUX
  |AND(a,b) ->evaluer (AND(evaluer a , evaluer b))
  |NAND(a,b)-> evaluer (NOT(AND(evaluer a, evaluer b)))
  |OR(VRAI,VRAI)->VRAI
  |OR(VRAI,FAUX)->VRAI
  |OR(FAUX, VRAI) -> VRAI
  |OR(FAUX , FAUX) -> FAUX 
  |OR (a,b)-> evaluer(OR(evaluer a, evaluer b))
  |XOR(VRAI,VRAI) -> FAUX
  |XOR(VRAI,FAUX)->VRAI
  |XOR(FAUX, VRAI) -> VRAI
  |XOR(FAUX , FAUX) -> FAUX 
  |XOR (a,b)-> evaluer(XOR(evaluer a, evaluer b)) ;;

let rec remplacervaleurliste l env= 
  match l with 
    []->[]
  |c1 :: ll2 ->
      match c1 with 
        (a,b) ->let q = remplacervaleurliste ll2 env
          in ((remplacervaleur env a),(remplacervaleur env b))::q ;;
            

let rec evaluervaleurliste l = 
  match l with 
    []->[]
  |c1 :: ll2 ->
      match c1 with 
        (a,b) ->let q = evaluervaleurliste ll2 
          in ((evaluer a),(evaluer b))::q ;; 

let rec derniereq l taille =
  match l with 
    []->[]
  |c1::ll1 ->
      match c1 with
        (a,b)->
          if taille = 1
          then 
            [(a,b)]
          else 
            derniereq (ll1) (taille-1) ;;

let memecouple c1 c2 =
  match c1,c2 with 
    (a,b), (c,d) -> 
      if a = c
      then 
        if b =d
        then 
          1
        else 
          0 
      else 0 ;;


let rec verifieegalite l taille =
  match l with 
    []-> 0
  |c1 :: ll1 -> 
      match c1 with
        (a,b) -> 
          if ((testegalite c1) = 1)
          then
            if (taille = 1)
            then 1 
            else
              verifieegalite ll1 (taille-1)
          else 0;; 
  
let inverse lst =
  let rec aux (acc,l) = match l with
    | [] -> acc
    |a::q -> aux(a::acc,q)
  in aux([],lst);;

let rec messolutions mes_envi monsyse  = 
  match mes_envi with 
    [] -> []
  |env ::ll1 ->
      match monsyse with 
        []->[]
      |c1 :: ll2 ->
          if (verifieegalite (evaluervaleurliste (remplacervaleurliste (monsyse) (env))) (tailleliste(monsyse)) = 1)
          then 
            let sol = messolutions (inverse(ll1)) monsyse 
            in (inverse([env])) :: sol
          else 
            messolutions ll1 monsyse;;

messolutions  mes_environnements_associes monsysdeq;;


