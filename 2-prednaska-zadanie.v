(*********************************************)
(**       Zadanie k prednáške 2             **)
(*Import potrebných knižníc*)
Require Import Coq.Bool.Bool.
Require Import Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

(*
==================================================
Doplnok k prednáške:
==================================================
Základná tabuľka operátorov v Coq
==================================================

1 Porovnávacie operátory pre nat (vracajú bool)
--------------------------------------------------
  n =? m    : test rovnosti (true ak n = m, inak false)
  n <=? m   : menšie alebo rovné
  n <? m    : menšie

Príklady:
  Compute (3 <=? 5).  (* true *)
  Compute (5 =? 3).   (* false *)
  Compute (4 <? 4).   (* false *)

--------------------------------------------------
2 Logické operátory pre bool
--------------------------------------------------
  negb b        : -
  andb b1 b2    : b1 && b2
  orb b1 b2     : b1 || b2
  xorb b1 b2    : -

Príklady:
  Compute (andb true false).   (* false *)
  Compute (orb true false).    (* true *)
  Compute (negb true).         (* false *)
  Compute (xorb true false).   (* true *)

--------------------------------------------------
3 Logické operátory pre Prop (dôkazy)
--------------------------------------------------
  P /\ Q        : P AND Q
  P \/ Q        : P OR Q
  ~ P           : NOT P
  P -> Q        : implikácia
  P <-> Q       : ekvivalencia

Poznámka: Prop je typ pre formálne tvrdenia a dôkazy,
          bool je typ programovo vyhodnocovateľný.

==================================================
*)


(*
==================================================
Rozdiel medzi bool a Prop pri porovnaniach
==================================================

V Rocq existujú dve “verzie” porovnania pre nat:

bool – programovo vyhodnocovateľná hodnota
  - Napr. n =? m alebo n <=? m vracia true/false (typu bool)
  - Používa sa pri výpočtoch, Compute, if vetveniach
  - Príklad: Compute (3 <=? 5).  (* true *)

Prop – logické tvrdenie
  - Napr. n = m alebo n <= m typu Prop
  - Používa sa pri dôkazoch, rewrite, indukcii
  - Príklad: forall n m : nat, n <= m -> ...

Otáznik (?):
  - n =? m, n <=? m, n <? m vracajú bool
  - Bez otázniku n = m... vracajú Prop, 
    ktoré nie je hodnotou
  - Bool verziu môžeme kombinovať 
    s andb, orb alebo if (vo výpočtoch)
  - Prop verziu používame v dôkazoch
==================================================
*)

(*********************************************)
(**           Dôkazy                        **)

(* 
  Úloha 3.1: Dokážte, že n - n = 0
*)
Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.2: Dokážte: n * 0 = 0 *)
Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.3: Dokážte: n * 1 = n *)
Theorem mult_n_1 : forall n, n * 1 = n.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.4: Dokážte, že 1 + (n + m) = n + (1 + m) *)
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.5: Dokážte komutatívnosť sčítania *)
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.6: Dokážte asociativnosť sčítania *)
Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Definícia: Funkcia double zdvojnásobí argument *)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(* Úloha 3.7: Dokážte, že double n = n + n *)
Lemma double_plus : forall n, double n = n + n .
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.8
Jedným nepraktickým aspektom definície even 
zo štandardnej knižnice je 
rekurzívne volanie na n - 2. 
To sťažuje dôkazy indukciou, 
pretože môžeme potrebovať 
indukčný predpoklad pre n - 2. 
Nasledujúca lema poskytuje 
alternatívnu charakterizáciu even (S n).
*)
Print even.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.9: Zamiešanie sčítania *)
Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.10: Komutativnosť násobenia *)
Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.11: 
Ak má hypotéza tvar H: P → a = b, 
potom taktika rewrite H prepíše a na b 
v cieli a pridá P ako nový podcieľ. 

Použite to v indukčnom kroku tejto úlohy. *)
Check leb.
Print leb.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.12: Reflektivita leb *)
Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.13: 0 sa nerovná 1 + n *)
Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.14: b && false = b *)
Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.15: 1+n sa nerovná 0 *)
Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.16: 1 * n = n *)
Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.17: Logická kombinácia orb/andb/negb *)
Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.18: Distribútivita násobenia 
cez sčítanie sprava *)
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.19: Asociativnosť násobenia *)
Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* Doplnte dôkaz *) Admitted.

(* Úloha 3.20: add_shuffle3' s replace *)
Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* Doplnte dôkaz *) Admitted.



