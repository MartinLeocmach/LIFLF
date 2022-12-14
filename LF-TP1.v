(* TP1 Langages formels

   ATTENTION
   Pour le bon affichage des caractères accentués, précisez que l'encodage par défaut de votre NAVIGATEUR doit être Unicode (UTF-8)

   BUT DU TP

   Manipuler Coq / Gallina

   Se familiariser avec 4 mots-clés :
      - Definition
      - Definition avec match ... with
      - Inductive
      - Fixpoint
*)


(* DÉFINIR UN OBJET (entier, fonction, etc.) *)
(* Mot-clef "Definition" 
   suivi du nom de l'objet
   suivi de ":" 
   suivi du type de l'objet
   suivi de ":="
   suivi de la valeur de l'objet. *)
Definition a : nat := 3.
Definition b : nat := 6.

(* En Coq on donne TOUJOURS les types. *)

(* EFFECTUER UN CALCUL... dans l'interpréteur *)
(* Directive "Compute" *)
(* RÉSULTAT ATTENDU : 9 *)
Compute (a+b).

(* AFFICHER LE TYPE... dans l'interpréteur *)
(* Directive "Check" *)
Check (a+b).

Print a.



(* 1) TYPES ÉNUMÉRÉS et INDUCTIFS *)


(* Mots-clefs "Inductive" et "|" par cas. 
   C'est la définition d'un ensemble inductif, on donne des règles...
   Comme on définit un *type* de données, son propre type est Type. *)
Inductive jour : Type :=
  | lundi : jour
  | mardi : jour
  | mercredi : jour
  | jeudi : jour
  | vendredi: jour
  | samedi : jour
  | dimanche : jour.
(* ici uniquement des cas de base *)


(* On peut définir une FONCTION jour_suivant sur ce type.
   (jour_suivant e) s'évalue en le nom du jour suivant le jour e.
   Elle est réalisée suivant *la forme* du paramètre, c'est du
   "filtrage" ou "PATTERN MATCHING". C'est le mécanisme le plus
   confortable pour manipuler des structures inductives. *)
(* Mots-clef "match" "with" "end" *)
Definition jour_suivant (j : jour) : jour :=
  match j with
  | lundi => mardi
  | mardi => mercredi
  | mercredi => jeudi
  | jeudi => vendredi
  | vendredi => samedi
  | samedi => dimanche
  | dimanche => lundi
  end.

(* On teste. RÉSULTAT ATTENDU : jeudi *)
Compute (jour_suivant mercredi).


(* EXERCICE *)
(* Définir la fonction qui retourne le surlendemain d'un jour donné *)
(* C'est une fonction qui APPLIQUÉE À un jour, RETOURNE un jour *)
Definition jour_suivant_le_jour_suivant (j : jour) : jour :=
jour_suivant(jour_suivant (j)).

(* On re-teste et on devrait obtenir vendredi*)
Compute (jour_suivant_le_jour_suivant mercredi).


(* On peut aussi définir les booléens... *)
(* Il n'y a que des cas de base et on va les appeler Vrai et Faux *)
Inductive booleens : Type :=
| Vrai : booleens
| Faux : booleens.

(* Ainsi que les fonctions logiques usuelles. *)
(* Le complémentaire : non. *)
Definition non (a : booleens) : booleens :=
  match a with
  | Vrai => Faux
  | Faux => Vrai
  end.


(* Directive d'affichage de type *)
Check non.

(* Directive d'affichage de valeur *)
Print non.


(* EXERCICE *)
(* Définir la fonction "et" sur les booléens. *)
Definition et (a : booleens) (b : booleens) : booleens :=
match (a, b) with
| (Vrai, Vrai) => Vrai
| _ => Faux
end.

(* un petit test, RÉPONSE ATTENDUE : Faux *)
Compute (et Vrai (et Faux Vrai)).


(* EXERCICE *)
(* Définir la fonction "ou" sur les booléens. *)
Definition ou (a : booleens) (b : booleens) : booleens :=
match (a, b) with
| (Faux, Faux) => Faux
| _ => Vrai
end.

(* RÉPONSE ATTENDUE : Vrai *)
Compute (et Vrai (ou Faux Vrai)).


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir une fonction bcompose : f -> g -> h telle que h est la composition des
deux fonctions booléennes f et g *)

(* Tester bcompose en définissant une fonction nonnon : booléens -> booléens qui
définit non o non *)

(* RÉSULTAT ATTENDU : Vrai *)
(* Compute (nonnon Vrai). *)


(* Le langage de Coq a bien sûr des booléens (dans le type prédéfini bool),
   ils sont en fait définis de la même façon que nos booleens. Pour l'instant
   nous allons continuer de travailler avec les nôtres. *)

(* On définit maintenant de façon inductive le type des entiers naturels.
   Un entier naturel est :
   - soit un élément particulier noté Z (pour zéro, c'est un cas de base ici),
   - soit le successeur d'un entier naturel.
 
   On a bien DEUX CONSTRUCTEURS pour les entiers : ils sont soit de la
   *forme* "Z" soit de la *forme* "Succ d'un entier".
*)
Inductive entiers : Type :=
| Z : entiers
| Succ : entiers -> entiers.

Definition un  := Succ Z.
Definition deux  := Succ un.
Definition trois  := Succ deux.


(* EXERCICE *)
(* Définir la fonction prédécesseur *)
(* C'est une fonction qui APPLIQUÉE À un entier, RETOURNE un entier *)
(* On considère que le prédécesseur de quelque chose de la forme Z est... Z *)
(* Le prédécesseur de quelque chose de la forme Succ toto est bien sûr toto *)
Definition pred (a : entiers) : entiers :=
match a with
| Z => Z
| Succ n => n
end.



(* RÉSULTAT ATTENDU :  Succ (Succ Z) *)
Compute (pred trois).


(* On veut écrire une FONCTION RÉCURSIVE pour ajouter deux entiers.
   Comme la fonction est récursive, on utilise le mot-clé Fixpoint (et
   non plus Definition).
   Elle se calcule selon la forme du premier paramètre *) 
Fixpoint plus (a : entiers) (b : entiers) : entiers :=
  match a with
  | Z => b
  | Succ n => Succ (plus n b)
  end.


(* EXERCICE *)
(* Multiplication
   Elle se calcule selon la forme du premier paramètre *)
Fixpoint mult (a : entiers) (b : entiers) : entiers :=
match a with
| Z => Z
| Succ Z => b
| Succ n => plus b (mult n b)
end.

(* RÉSULTAT ATTENDU : 9 *)
Compute (mult trois trois).


(* EXERCICE *)
(* Définir une fonction est_pair, telle que est_pair APPLIQUÉE À un entier a RETOURNE Vrai si a est pair, Faux sinon. *)
Fixpoint est_pair (a : entiers) : booleens:=
match a with
| Z => Vrai
| Succ Z => Faux
| Succ (Succ n) => est_pair n
end.

(* RÉSULTAT ATTENDU : Vrai *)
Compute (est_pair deux).

(* RÉSULTAT ATTENDU : Faux *)
Compute (est_pair trois).


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir la fonction factorielle sur les entiers *)
Fixpoint factorielle (a : entiers) : entiers :=
match a with
| Z => un
| Succ Z => un
| Succ n => mult a (factorielle n)
end.

(* RÉSULTAT ATTENDU : 24 sous forme de Succ( ... (Succ(Z) ...) *)
Compute (factorielle (plus trois un)).


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir la fonction moins, soustraction non négative sur les entiers *)
Fixpoint moins (a b : entiers) : entiers :=
match b with
| Z => a
| Succ n => match a with
            | Z => Z
            | Succ m => moins m n
            end
end.

(* RÉSULTAT ATTENDU : Succ Z *)
Compute (moins deux un).

(* RÉSULTAT ATTENDU : Z *)
Compute (moins deux trois).

(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir une fonction inf, tel que inf a b vaut/retourne Vrai si a est
   inférieur ou égal à b, Faux sinon. *)
Fixpoint inf (a b : entiers) : booleens :=
match a with
| Z => Vrai
| Succ n =>  match b with
             | Z => Faux
             | Succ m => inf n m
              end
end.

(* RÉSULTAT ATTENDU : Vrai *)
Compute (inf trois trois).

Compute (inf deux trois).
Compute (inf trois deux).


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir une fonction egal, tel que egal a b donne Vrai si les entiers
   a et b sont égaux, Faux sinon.*)
Fixpoint egal (a b : entiers) : booleens :=
match (a, b) with 
| (Z, Z) => Vrai
| (Succ n, Succ m) => egal n m
| _ => Faux
end.


(* RÉSULTAT ATTENDU : Vrai *)
Compute (egal trois trois).

(* RÉSULTAT ATTENDU : Faux *)
Compute (egal un trois).
Compute (egal trois un).


(* ------------------------------------------------------------ *)


(* Précédemment, on a défini nos booléens et nos entiers naturels,
mais ils sont en fait déjà définis dans la bibliothèque que Coq charge
initialement au démarrage :

NE PAS DECOMMENTER CE QUI SUIT, CE SONT DES TYPES COQ PREDEFINIS

Inductive bool : Set :=
  | true : bool
  | false : bool.

avec les fonctions 

negb (le complémentaire)
andb (le et, (le min))
orb  (le ou, (le max))

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

avec les fonctions usuelles + , - , * , etc.
et les comparaisons :
Nat.eqb pour le test d'égalité
Nat.ltb pour le test plus petit
Nat.leb pour le test plus petit ou égal.


CE SONT EUX QU'ON UTILISERA DORÉNAVANT.

 *)

(* ------------------------------------------------------------ *)


(* 2) LISTES D'OBJETS DE TYPE NAT *)


(* On considère ici des listes d'objets de type nat. *)

(* On peut définir de façon inductive un type nliste pour les listes d'objets de type nat. 
  Le cas de base est bien sûr la liste vide, l'autre règle de construction applique cons
  à un nat et une liste de l'ensemble inductif pour créer un nouvel élément de cet ensemble
*)
Inductive nliste : Type :=
  | vide : nliste
  | cons : nat -> nliste -> nliste.

Definition liste0 := vide.
Definition liste1 := cons 1 vide.
Definition liste2 := cons 2 (cons 1 vide).
Definition liste3 := cons 3 (cons 2 (cons 1 vide)).
Definition liste4 := cons 4 (cons 3 (cons 2 (cons 1 vide))).
Print liste0.
Print liste1.
Print liste2.


(* EXERCICE *)
(* Écrire une fonction ajoute: nat -> nliste -> nliste telle que ajoute n l
   retourne une liste correspondant à l'ajout de l'élément n à la liste l.
   C'est bien sûr juste la fonction qui applique cons
*)
Definition ajoute (n : nat) (l : nliste) : nliste := 
cons n (l).



(* RÉSULTAT ATTENDU : cons 3 (cons 2 (cons 1 vide)) *)
Compute (ajoute 3 liste2).


(* EXERCICE *)
(* Écrire une fonction longueur telle que longueur APPLIQUÉE À l
   RETOURNE le nombre (nat) d'éléments de la liste l.  On l'a vue en
   cours.
  C'est bien sûr une fonction qui travaille selon la FORME de l : si
  c'est vide, la longueur vaut zéro, et si l est de la forme cons n l'
  à vous de jouer.  *)
Fixpoint longueur (l : nliste) : nat :=
match l with
| vide => 0
| cons n vide => 1
| cons n l1 => 1 + longueur l1
end. 

(* RÉSULTAT ATTENDU : 2 *)
Compute (longueur liste2).

(* EXERCICE *)
(* Écrire une fonction concat: nliste -> nliste -> nliste telle que concat l l'
   retourne une liste correspondant à l'ajout des éléments de l en tête de la liste l'. *)
Fixpoint concat (l l' : nliste) : nliste :=
match l with
| vide => l'
| cons n l1 => cons n (concat l1 l')
end.

(* RÉSULTAT ATTENDU : cons 2 (cons 1 (cons 2 (cons 1 vide))) *)
Compute (concat liste2 liste2).

(* EXERCICE *)
(* Écrire une fonction recherche: nat -> nliste -> bool telle que recherche n l
   retourne Vrai si un élément n appartient à la liste l et Faux sinon. *)
(* Pour l'égalité entre éléments du type nat, soit on la redéfinit, soit on utilise Nat.eqb *)
Require Import Nat.
Check (eqb 3 4).
Compute (eqb 3 4).

Fixpoint recherche (n : nat) (l : nliste) : bool :=
match l with
| vide => false
| cons a l1 => match eqb n a with
               | true => true
               | false => recherche n l1
               end
end.

(* RÉSULTAT ATTENDU : true *)
Compute (recherche 1 liste2).

(* RÉSULTAT ATTENDU : false *)
Compute (recherche 3 liste2).


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Écrire une fonction miroir: nliste -> nliste, qui
   retourne une liste correspondant à son argument dans l'ordre
   inverse. Dans un premier temps, on pourra utiliser la fonction de
   concaténation vue précédemment. *)
Fixpoint miroir (l : nliste) : nliste :=
match l with
| vide => l
| cons n l1 => concat (miroir l1) (cons n vide)
end.

(* RÉSULTAT ATTENDU : cons 1 (cons 2 (cons 3 (cons 4 vide))) *)
Compute (miroir liste4).



(* EXERCICE A FAIRE CHEZ VOUS *)
(* Écrire une fonction supprime: nat -> nliste -> nliste telle que
   supprime n l retourne une liste d'objets de type nat correspondant
   à l sans la première occurrence de n (le cas échéant), à l
   sinon. *)
Fixpoint supprime (n : nat) (l : nliste) : nliste :=
match l with
| vide => l
| cons a l1 => match eqb n a with
               | true => l1
               | false => cons a (supprime n l1)
               end
end. 

(* RÉSULTAT ATTENDU : cons 4 (cons 2 (cons 1 vide)) *)
Compute (supprime 3 liste4).


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Écrire une fonction supprime_tout: nat -> nliste -> nliste telle
   que supprime_tout n l retourne une liste correspondant à l sans
   occurrence d'un nat n (le cas échéant), à l sinon. *)
Fixpoint supprime_tout (n : nat) (l : nliste) : nliste :=
match l with
| vide => l
| cons a l1 => match eqb n a with
               | true => supprime_tout n l1
               | false => cons a (supprime_tout n l1)
               end
end.


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Écrire une fonction il_existe_pair: nliste -> booleens, telle que
   il_existe_pair l retourne Vrai si un élément de l est pair, Faux
   sinon. *)
Fixpoint pair (n : nat) : bool :=
match n with
| 0 => true
| 1 => false
| S (S a) => pair a
end.

Fixpoint il_existe_pair (l : nliste) : bool :=
match l with
| vide => false
| cons n l1 => match pair n with
               | true => true
               | false => il_existe_pair l1
               end
end.


(* RÉSULTAT ATTENDU : true *)
Compute (il_existe_pair liste4).


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Insertion triée *)
(* Écrire dans un premier temps une fonction leq : nat -> nat -> bool qui teste si le
premier entier est inférieur ou égal au second *)
Fixpoint leq (a b : nat) : bool :=
match (a, b) with
| (0, 0) => true
| (0, S b1) => true
| (S a1, 0) => false
| (S a1, S b1) => leq a1 b1
end.

(* RÉSULTAT ATTENDU : true *)
Compute (leq 2 2).

(* RÉSULTAT ATTENDU : true *)
Compute (leq 2 3).

(* RÉSULTAT ATTENDU : false *)
Compute (leq 3 2).

(* Écrire une fonction insertion_triee : nat -> nliste -> nliste qui effectue
une insertion triée dans une liste *)
Fixpoint insertion_triee (n : nat) (l : nliste) : nliste :=
match l with
| vide => cons n vide
| cons a l1 => match leq n a with
               | true => cons n l
               | false => cons a (insertion_triee n l1)
               end
end. 

(* RÉSULTAT ATTENDU : cons 1 (cons 2 (cons 2 (cons 3 (cons 4 vide)))) *)
Compute (insertion_triee 2 (miroir liste4)).

(* RÉSULTAT ATTENDU : cons 4 (cons 3 (cons 2 (cons 1 (cons 6 vide)))) *)
Compute (insertion_triee 6 liste4).


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Tri par insertion d'une liste *)
(* Écrire une fonction tri_insertion : nliste -> nliste qui effectue
le tri par insertion d'une liste *)
Fixpoint tri_insertion (l : nliste) : nliste :=
match l with
| vide => l
| cons a l1 => insertion_triee a (tri_insertion l1)
end.

(* RÉSULTAT ATTENDU : cons 1 (cons 1 (cons 2 (cons 2 (cons 3 (cons 3 (cons 4 (cons 4 vide)))))) *)
Compute (tri_insertion (concat liste4 liste4)).




(* 3) ARBRES BINAIRES *)


(* EXERCICE *)
(* Donner une définition par induction de l'ensemble nBin des arbres
binaires contenant des nat. On souhaite avoir une représentation de
l'arbre vide dans nBin. *)
Inductive nBin : Type :=
| nEmpty : nBin
| nNode : nBin -> nat -> nBin ->nBin.


(* Donner un exemple d'arbre, disons à 5 éléments *)

Definition a1 := nNode
                      (nNode nEmpty 2 nEmpty)
                      1
                      (nNode
                            (nNode nEmpty 4 nEmpty)
                            3
                            (nNode nEmpty 5 nEmpty)
                      ).

Check a1.
Print a1.

(* EXERCICE *)
(* Définir la fonction nelements qui renvoie la liste des éléments
   contenus dans un arbre binaire de nat. Le faire naïvement avec un
   concat pour commencer. *)

Fixpoint nelements (a : nBin) : nliste :=
match a with
| nEmpty => vide
| nNode ga n da => cons n (concat (nelements ga) (nelements da))
end.

(* RÉSULTAT ATTENDU : cons 1 (cons 2 (cons 3 (cons 4 (cons 5 vide)))) *)
Compute (nelements a1).



(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir la fonction nnelts qui renvoie le nombre de noeuds internes
   (portant une étiquette de type nat) dans un nBin. *)
Fixpoint nnelts (a : nBin) : nat :=
match a with
| nEmpty => 0
| nNode ga n da => 1 + nnelts ga + nnelts da
end.

(* RÉSULTAT ATTENDU : 5 *)
Compute (nnelts a1).



(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir la fonction nfeuilles qui renvoie le nombre de feuilles *)
Fixpoint nfeuilles (a : nBin) : nat :=
match a with
| nEmpty => 1
| nNode ga n da => nfeuilles ga + nfeuilles da
end.

(* RÉSULTAT ATTENDU : 6 *)
Compute nfeuilles a1.


(* EXERCICE A FAIRE CHEZ VOUS *)
(* Définir la fonction nsum qui renvoie la somme des valeurs portées
   par les noeuds internes d'un nBin. *)
Fixpoint nsum (a : nBin) : nat :=
match a with
| nEmpty => 0
| nNode ga n da => n + nsum ga + nsum da
end.

(* RÉSULTAT ATTENDU : 15 *)
Compute (nsum a1).



(* ------------------------------------------------------------ *)




