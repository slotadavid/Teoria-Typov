(*********************************************)
(**       Zadanie k prednáške 1             **)
(*********************************************)
(**       Programovanie v Rocq              **)

(*
  Poznámka:
  Odporúčam stiahnuť a vytlačiť nasledujúce "cheatsheets":
  -https://www.inf.ed.ac.uk/teaching/courses/tspl/cheatsheet.pdf
  -https://www.cs.cornell.edu/courses/cs3110/
   2018sp/a5/coq-tactics-cheatsheet.html

  Poznámka:
  Ďalšiu odporúčanú literatúru nájdete 
  na stránke predmetu.
*)

(*
  Úloha 1.1
  Definujte modul cvicenieBool pre prácu s vlastným typom bool.
*)

Module cvicenieBool.

(*
  Úloha 1.2
  Definujte vlastný induktívny typ bool.
*)

(* tu príde definícia TODO *)
Inductive bool: Type :=.


(*
  Úloha 1.3
  Definujte funkcie pre nasledujúce operácie nad typom bool:
  - negácia
  - konjunkcia
  - disjunkcia
  - implikácia
  Pomenujte ich negb, andb, orb, implb. 
*)

(* definície funkcií TODO *)
Definition negb (b:bool) :bool . 
Admitted.

Definition andb (b1 b2:bool) :bool . 
Admitted.

Definition orb (b1 b2:bool) :bool .
Admitted.

Definition implb (b1 b2:bool) :bool . 
Admitted.

(*
  Úloha 1.4
  Využitím Vernacular príkazov:
  - Check
  - Print
  - About
  vypíšte informácie o Vašich definíciách a 
  pouvažujte nad rozdielmi medzi nimi.
*)

(* príklady použitia: Check ..., Print ..., About ... TODO *)
Check andb.
Check orb.
Check implb.
Check negb.

Print andb.
Print orb.
Print implb.
Print negb.

About andb.
About orb.
About implb.
About negb.


(*
  Úloha 1.5
  Prostredníctvom Vernacular príkazu Compute 
  otestujte či sa Vaše funkcie negb, andb, orb, a implb 
  správajú podľa očakávania.
*)

(* 
TODO odkomentovať

Compute (negb true).
Compute (negb false).

Compute (andb true true).
Compute (andb true false).
Compute (andb false true).
Compute (andb false false).

Compute (orb true true).
Compute (orb true false).
Compute (orb false true).
Compute (orb false false).

Compute (implb true true).
Compute (implb true false).
Compute (implb false true).
Compute (implb false false).
*)

(*
  Úloha 1.6
  Aktuálne pre výpočet boolovských funkcií 
  je potrebné využívať prefixnú formu,
  čo je pre programátora neprirodzené. 
  
  Zaveďte notácie pre Vami definované
  funkcie (! negb, &&& andb, ||| orb, ---> implb), 
  uvažujte o priorite a asociativite jednotlivých
  operátorov.
*)

(* Notation ... TODO*)


(*
  Úloha 1.7
  Prostredníctvom Vernacular príkazu Compute otestujte
  implementáciu notácií.
*)

(*
  Predpokladáme, že máte definované:
  - funkciu negácie
  - konjunkciu
  - disjunkciu
  - implikáciu
  a zavedené notácie: !, &&&, |||, --->.
*)

(*
  Testovacie príklady pre zavedenú notáciu (!, &&&, |||, --->)
  Odkomentujte a otestujte:

Compute (! true).            (* očak.: false *)
Compute (! false).           (* očak.: true  *)

Compute (true &&& true).     (* očak.: true  *)
Compute (true &&& false).    (* očak.: false *)
Compute (false &&& true).    (* očak.: false *)
Compute (false &&& false).   (* očak.: false *)

Compute (true ||| true).     (* očak.: true  *)
Compute (true ||| false).    (* očak.: true  *)
Compute (false ||| true).    (* očak.: true  *)
Compute (false ||| false).   (* očak.: false *)

Compute (true ---> true).    (* očak.: true  *)
Compute (true ---> false).   (* očak.: false *)
Compute (false ---> true).   (* očak.: true  *)
Compute (false ---> false).  (* očak.: true  *)
*)


(*
  Úloha 1.8
  Otestujte implementáciu asociativity 
  a priority na vhodných príkladoch.
*)

(*
  Testy priorít a asociativity
  Odkomentujte a otestujte
*)

(* Negácia má najvyššiu prioritu 
Compute (! true &&& true).    *)
(* vyhodnotí sa ako ((! true) &&& true) → očak.: false *)

(* Konjunkcia  má najvyššiu než disjunkcia) 
Compute (true ||| true &&& false).  *)
(* vyhodnotí sa ako (true ||| (true &&& false)) → očak.: true *)
 
 
(* Implikácia má najnižšiu prioritu 
Compute (true &&& false ---> true). *)
(* vyhodnotí sa ako ((true &&& false) ---> true) → očak.: true *)


(* Asociativita disjunkcie 
Compute ((true ||| false) ||| false).   (* očak.: true *)
Compute (true ||| (false ||| false)).   (* očak.: true *)
*)

(* Asociativita konjunkcie 
Compute ((true &&& false) &&& true).    (* očak.: false *)
Compute (true &&& (false &&& true)).    (* očak.: false *)
*)



(*
  Úloha 1.9
  Ukončite prácu v rámci modulu cvicenieBool.
*)

End cvicenieBool.

(*
  Úloha 1.10
  V rámci materiálov pre cvičenie a prednášku
  je prezentovaný kód pre definíciu typu
  nat a operácií sčítania a násobenia.

  Tento typ obsahuje štandardná knižnica systému Rocq.

  Zistite, ako je daný typ implementovaný v štandardnej knižnici 
  a aké operácie nad ním sú definované.
  
  TODO
*)


(*
  Úloha 1.11
  Definujte funkcie:
  - následovníka succesor
  - predchodcu pred
  - overenia nuly iszero
  s využitím typu nat zo štandardnej knižnice.
*)

(* TODO definície funkcií succesor, pred, iszero *)

Definition succesor (n:nat) : nat .
Admitted.

Definition pred (n:nat) : nat .
Admitted.

Definition iszero (n:nat) : bool .
Admitted.

(*
  Úloha 1.12
  Implementujte funkcie pre sčítanie 
  a násobenie podľa rekurzívnej definície
  z cvičenia 3 na stránke predmetu.
  Pomenujte ich plus_rec a times_rec
*)

(* TODO definície funkcií pre sčítanie a násobenie *)
Fixpoint plus_rec (m:nat) (n:nat) : nat .
Admitted.

Fixpoint times_rec (m:nat) (n:nat) : nat .
Admitted.



(*********************************************)
(**             Zadanie                     **)
(*********************************************)
(**            Prvé dôkazy                  **)


(*
===============================================
     Príklady na precvičenie základných taktík
===============================================
*)

(*
 Úloha 2.1. 
 Dokážte, že každý boolean je rovný sám sebe.
*)
Theorem bool_self : forall b : bool, b = b.
Proof.
Admitted.

(*
 Úloha 2.2. 
 Dokážte, že 4 + 0 = 4.
*)

Theorem four_plus_zero : 4 + 0 = 4.
Proof.
Admitted.

(*
 Úloha 2.3.
*)
Theorem use_assumption :
  forall (n m : nat), n = m -> n = m.
Proof.
Admitted.

(*
 Úloha 2.4. 
 Dokážte, že ak n = m, tak n + 2 = m + 2.
*)
Theorem plus_two :
  forall (n m : nat), n = m -> n + 2 = m + 2.
Proof.
Admitted.

(*
 Úloha 2.5. Rewrite s lemmou
 Najprv dokážte jednoduchú lemmu a potom ju použite 
 v plus_zero_example.
*)
Theorem add_zero_left : forall n, 0 + n = n.
Proof.
Admitted.

Theorem plus_zero_example : forall n, 0 + n + 3 = n + 3.
Proof.
Admitted.

(*
 Úloha 2.6. 
 Dokážte, že b || true = true.
*)
(* Načítanie typu zo štandardnej knižnice *)
Require Import Coq.Bool.Bool.
Compute (true && true).  (*konjunjcia*)
Compute (true || true).  (*disjunkcia*)
Compute (negb true).     (*negácia*)

Theorem orb_true : forall b : bool, b || true = true.
Proof.
Admitted.

(*
 Úloha 2.7.
 Dokážte, že pre každé n : nat platí:
   1 + n = S n
*)

Theorem one_plus_n : forall n : nat, 1 + n = S n.
Proof.
Admitted.


(*
 Úloha 2.8. 
 Dokážte: (n = m) -> (m = k) -> (n = k).
*)
Theorem trans_eq : forall n m k : nat, n = m -> m = k -> n = k.
Proof.
Admitted.
