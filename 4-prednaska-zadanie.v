(*********************************************)
(**       Zadanie k prednáške 4             **)
(*********************************************)

(*        Import potrebných knižníc         *) 

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.PeanoNat.
Require Import Init.Nat.
Require Import Stdlib.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(*-------------------------------------------*)
(** Úlohy:                                   *)
(*-------------------------------------------*)


         ; (bodkočiarka)
  - aplikuje druhú taktiku na všetky vetvy po destruct

*)


(**
===========================================
      MAPA TAKTÍK – VIZUÁLNY PREHĽAD
===========================================

Cieľom je vedieť rýchlo určiť, KTORÚ taktiku
použiť v danej situácii.

────────────────────────────────────────────
1  PRÁCA S ROVNOSŤAMI
────────────────────────────────────────────
        +----------------------+
        |  Potrebujem dokázať  |
        |     x = y            |
        +----------------------+
                 │
                 ▼
     ┌────────────────────────────┐
     │ obe strany rovnaké →       │ reflexivity
     │ známa rovnosť H : x = y →  │ apply H
     │ opačný smer →              │ symmetry
     │ cez medzičlánok →          │ transitivity
     │ konštruktor rovnaký →      │ injection
     │ konštruktor rôzny →        │ discriminate
     │ chcem nahradiť v kontexte →│ subst
     └────────────────────────────┘

────────────────────────────────────────────
2  SPORY A KONTRADIKCIE
────────────────────────────────────────────
        +----------------------+
        |  V kontexte mám      |
        |  spor (False, P ∧ ¬P)|
        +----------------------+
                 │
                 ▼
     ┌────────────────────────────┐
     │ logický spor →             │ contradiction
     │ nemožná rovnosť (S n = O) →│ discriminate
     │ z False dokážem čokoľvek → │ destruct H
     └────────────────────────────┘

────────────────────────────────────────────
3  PRÁCA S KONTEXTOM
────────────────────────────────────────────
        +----------------------+
        |  Chcem upraviť alebo |
        |  použiť hypotézu     |
        +----------------------+
                 │
                 ▼
     ┌────────────────────────────┐
     │ zjednodušiť výraz →        │ simpl / simpl in H
     │ aplikovať implikáciu →     │ apply ... in
     │ konkretizovať ∀ →          │ specialize H with (...)
     │ rozbaliť definíciu →       │ unfold názov
     │ rozdeliť tvar →            │ destruct ... eqn:
     │ vrátiť premennú do cieľa → │ revert
     │ zmeniť poradie pre indukciu│ generalize dependent
     └────────────────────────────┘
────────────────────────────────────────────
4  LOGICKÉ SPOJKY (Prop)
────────────────────────────────────────────
        +----------------------+
        |  Cieľ alebo hypotéza  |
        |  má tvar P /\ Q , P \/ Q , ∃ x, P x, ~P |
        +----------------------+
                 │
                 ▼
     ┌────────────────────────────┐
     │ P /\ Q →                   │ split / destruct
     │   • cieľ: split.           │ rozdelí P /\ Q na P a Q
     │   • hypotéza H: destruct H │ H : P /\ Q → H1 : P, H2 : Q
     │     as [HP HQ].            │
     ├────────────────────────────┤
     │ P \/ Q →                   │ left / right / destruct
     │   • cieľ: vyber stranu:    │
     │           left. apply HP.  │
     │   • hypotéza H:            │
     │    destruct H as [HP | HQ].│
     ├────────────────────────────┤
     │ ∃ x, P x →                 │ exists / destruct
     │   • cieľ:                  │
     │       exists t; apply ...  │
     │   • hypotéza H:            │ 
     │     destruct H as [x Hx].  │
     ├────────────────────────────┤
     │ P -> Q →                   │ intros / apply
     │   • cieľ:                  │
     │        intros HP; apply H. │
     │   • hypotéza H:            │
     │        apply H in HP.      │
     ├────────────────────────────┤
     │ ~P (P -> False) →          │ intros; destruct
     │   • cieľ: intros HP;       │
     │           destruct HP      │
     │   • hypotéza H :           │ 
     │       ~P → apply H in HP   │
     ├────────────────────────────┤
     │ False →                    │ contradiction / destruct
     │   • hypotéza H :           │
     │      False → contradiction │
     │   • z False možno          │
     │     dokázať čokoľvek       │
     └────────────────────────────┘

────────────────────────────────────────────
PRÍKLADY:
────────────────────────────────────────────
1) Existencia v kontexte:
   H : ∃ x, P x
   → destruct H as [x Hx]. (* Hx : P x *)

2) Existencia v cieli:
   Goal: ∃ x, P x
   → exists t. (* t je konkrétny kandidát *)
   → apply H.  (* ak máme dôkaz P t *)

3) Negácia / absurdum:
   H : P /\ ~P
   → destruct H as [HP HnP].
   → contradiction. (* logický spor *)

4) Hypotéza False:
   H : False
   → contradiction. 
   (* z False možno dokázať čokoľvek *)


────────────────────────────────────────────
5  STRATÉGIA DÔKAZU
────────────────────────────────────────────
   • **Backward reasoning** – začni od cieľa
       (apply, transitivity, symmetry, intros)

   • **Forward reasoning** – začni z hypotéz
       (apply ... in, specialize, simpl in)

   • **Reorganizácia dôkazu**
       (assert, revert, generalize dependent)

   • **Riadenie vetiev**
       (destruct ... eqn:, ;, repeat)

   • **Automatické riešenie sporu**
       (discriminate, contradiction)

   • **Rozbalenie a analýza**
       (unfold, induction)
*)
