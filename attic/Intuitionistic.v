Require Import List.
Require Import PeanoNat.
Require Import Coq.Arith.Wf_nat.
Require Import Cantor.
Require Import Sorting.Permutation.
Import ListNotations.
Import EqNotations.

Inductive Formula : Set :=
| Var : nat -> Formula
| Arrow : Formula -> Formula -> Formula.

Inductive IL: list Formula -> Formula -> Prop :=
| Ax : forall Gamma phi, List.In phi Gamma -> IL Gamma phi
| ArrI : forall Gamma phi psi, IL (phi :: Gamma) psi -> IL Gamma (Arrow phi psi)
| ArrE : forall Gamma phi psi, IL Gamma (Arrow phi psi) -> IL Gamma phi -> IL Gamma psi.

Inductive SC: list Formula -> Formula -> Prop :=
| SC_Perm: forall Gamma Gamma' phi, Permutation Gamma Gamma' -> SC Gamma phi -> SC Gamma' phi
| SC_Ax : forall Gamma phi, SC (phi :: Gamma) phi
| SC_L : forall Gamma phi psi sigma, SC Gamma phi -> SC (psi :: Gamma) sigma ->
                                SC (Arrow phi psi :: Gamma) sigma
| SC_R : forall Gamma phi psi, SC (phi :: Gamma) psi -> SC Gamma (Arrow phi psi).

Lemma weakening: forall Gamma Gamma' phi,
    (forall psi, List.In psi Gamma -> List.In psi Gamma') ->
    IL Gamma phi -> IL Gamma' phi.
Proof.
  intros Gamma Gamma' phi inprf prf.
  revert Gamma' inprf.
  induction prf as [ | Gamma phi psi prf IH | Gamma phi psi prf1 IH1 prf2 IH2 ]; intros Gamma' inprf.
  - apply Ax; apply inprf; assumption.
  - apply ArrI.
    apply IH.
    intros psi' [ here | there ].
    + left; assumption.
    + right; apply inprf; assumption.
  - eapply ArrE; eauto.
Qed.  

Corollary weakening_step: forall Gamma phi psi, IL Gamma phi -> IL (psi :: Gamma) phi.
Proof.
  intros Gamma phi psi prf.
  apply (weakening Gamma).
  - intros; right; assumption.
  - assumption.
Qed.

Definition abstractCtxt (Gamma: list Formula) (phi: Formula): Formula :=
  fold_left (fun x y => Arrow y x) Gamma phi.

Lemma MultiArrI: forall Gamma phi, IL Gamma phi -> IL [] (abstractCtxt  Gamma phi).
Proof.
  intro Gamma.
  induction Gamma as [ | psi Gamma IH ].
  - intros; assumption.
  - intros phi prf.
    exact (IH _ (ArrI _ _ _ prf)).
Qed.

Lemma MultiArrE: forall Gamma Gamma' psi,
    IL Gamma (abstractCtxt Gamma' psi) ->
    (forall phi, List.In phi Gamma' -> IL Gamma phi) ->
    IL Gamma psi.
Proof.
  intros Gamma Gamma'.
  induction Gamma' as [ | phi Gamma' IH ].
  - intros; assumption.
  - intros psi prf argprfs.
    eapply ArrE.
    + apply IH.
      * exact prf.
      * intros; apply argprfs; right; assumption.
    + apply argprfs; left; reflexivity.
Qed.

Fixpoint Formula_eq_dec (phi psi : Formula) : { phi = psi } + { phi <> psi }.
Proof.
  destruct phi as [ n | phi1 phi2 ];
    destruct psi as [ m | psi1 psi2 ];
    try solve [ right; intro devil; inversion devil ].
  - destruct (Nat.eq_dec n m) as [ eq | ineq ].
    + rewrite eq; left; reflexivity.
    + right; intro devil; inversion devil; contradiction.
  - destruct (Formula_eq_dec phi1 psi1) as [ eqsrc | ineqsrc ];
      [ | right; intro devil; inversion devil; contradiction ];
      destruct (Formula_eq_dec phi2 psi2) as [ eqtgt | ineqtgt ];
      [ | right; intro devil; inversion devil; contradiction ].
    left; rewrite eqsrc; rewrite eqtgt; reflexivity.
Qed.    

Theorem Hauptsatz2: forall Gamma phi, SC Gamma phi -> IL Gamma phi.
Proof.
  intros Gamma phi prf.
  induction prf as [ Gamma Gamma' phi perm prf IH | | Gamma phi psi sigma prf1 IH1 prf2 IH2 | ].
  - apply (weakening Gamma).
    + intro psi.
      apply Permutation_in.
      assumption.
    + assumption.
  - apply Ax; left; reflexivity.
  - apply (ArrE _ _ _ (weakening_step _ _ _ (ArrI _ _ _ IH2))).
    apply (ArrE _ _ _ (Ax (Arrow phi psi :: Gamma) _ (or_introl eq_refl))).
    apply weakening_step.
    assumption.
  - apply ArrI.
    assumption.
Qed.


Lemma sc_weakening: forall Gamma Delta phi,
    SC Gamma phi -> SC (Delta ++ Gamma) phi.
Proof.
  intros Gamma Delta phi prf.
  revert Delta.
  induction prf
    as [ Gamma Gamma' phi perm prf IH | | Gamma phi psi sigma prf1 IH1 prf2 IH2 | Gamma phi psi prf IH ];
    intros Delta.
  - apply (SC_Perm _ _ _ (Permutation_app (Permutation_refl _) perm)).
    apply (IH Delta). 
  - apply (SC_Perm _ _ _ (Permutation_middle _ _ _)).
    apply SC_Ax.
  - apply (SC_Perm _ _ _ (Permutation_middle _ _ _)).
    apply SC_L.
    + apply IH1.
    + apply (SC_Perm _ _ _ (Permutation_sym (Permutation_middle _ _ _))).
      apply IH2.
  - apply SC_R.
    apply (SC_Perm _ _ _ (Permutation_sym (Permutation_middle _ _ _))).
    apply IH.
Qed.

Fixpoint Formula_size (phi: Formula): nat :=
  match phi with
  | Var _ => 1
  | Arrow phi1 phi2 => Formula_size phi1 + Formula_size phi2
  end.

Lemma Formula_size_S: forall phi, Formula_size phi <> 0.
Proof.
  intro phi.
  induction phi.
  - intro devil; inversion devil.
  - intro devil.
    simpl in devil.
    destruct (proj1 (Nat.eq_add_0 _ _) devil).
    auto.
Qed.

Definition Formula_size_ind
           (P : Formula -> Prop)
           (step: forall phi, (forall psi, Formula_size psi < Formula_size phi -> P psi) -> P phi)
           (phi: Formula): P phi.
Proof.
  apply (fun rec => Fix (well_founded_ltof _ Formula_size) rec).
  clear phi; intros phi IH.
  apply step.
  exact IH.
Qed.

Lemma Hauptsatz_Atom: forall phi Gamma,
    SC Gamma phi ->
    (Formula_size phi = 1) ->
    forall Delta psi, SC (phi :: Delta) psi -> SC (Gamma ++ Delta) psi.
Proof.
  intros phi Gamma prf.
  induction prf as [ Gamma Gamma' phi perm prf IH | | Gamma phi psi sigma prf1 IH1 prf2 IH2 | Gamma phi psi prf IH ].
  - intros sizeprf Delta psi prf'.
    apply (SC_Perm _ _ _ (Permutation_app perm (Permutation_refl _))).
    apply (IH sizeprf _ _ prf').
  - intros sizeprf Delta psi prf.
    simpl.
    apply (SC_Perm _ _ _ (Permutation_sym (Permutation_middle Gamma Delta phi))).
    apply sc_weakening.
    assumption.
  - intros sizeprf Delta psi' prf.
    simpl.
    apply SC_L.
    + apply (SC_Perm _ _ _ (Permutation_app_comm _ _)).
      apply sc_weakening.
      assumption.
    + apply (IH2 sizeprf _ _ prf).
  - intros sizeprf Delta psi' prf'.
    apply False_rect.
    simpl in sizeprf.
    revert sizeprf.
    clear ...
    intro sizeprf.
    induction phi as [ | phi1 IH1 phi2 IH2 ].
    + simpl in sizeprf.
      inversion sizeprf as [ sizeprf' ].
      apply (Formula_size_S _ sizeprf').
    + simpl in sizeprf.
      generalize (Formula_size_S phi1).
      destruct (Formula_size phi1).
      * intro devil; apply devil; reflexivity.
      * intros _.
        simpl in sizeprf.
        inversion sizeprf as [ sizeprf' ].
        generalize (proj1 (Nat.eq_add_0 _ _) sizeprf').
        intros [ _ devil ].
        apply (Formula_size_S _ devil).
Qed.

Lemma sc_dedup:
  forall Gamma phi,
    SC Gamma phi ->
    forall Gamma' psi,
      List.In psi Gamma ->
      (forall phi', List.In phi' Gamma' -> List.In phi' Gamma) ->
      SC Gamma' psi ->
      SC Gamma' phi.
Proof.
  intros Gamma phi prf.
  induction prf.
  - admit.
  - 
  
  revert Gamma.
  induction phi as [ | psi1 IH1 psi2 IH2 ].
  - admit.
  - intros Gamma prf psi prf'.
    apply SC_R.
    apply (IH2 _ phi).
    + apply (sc_weakening _ [psi1]).
      assumption.
    + 
  
  generalize (or_introl eq_refl : List.In phi (phi :: Gamma)).
  generalize (phi :: Gamma).
  induction prf.
  - admit.
  - 
    

(*Lemma sc_dedup:
  forall Gamma phi psi,
    SC Gamma phi ->
    SC (phi :: Gamma) psi ->
    SC Gamma psi.
Proof.
  intro Gamma.
  induction Gamma.
  - intros phi psi prf prf'.
    destruct (Formula_eq_dec phi psi) as [ eq | ineq ].
    + rewrite <- eq.
      assumption.
    + 

      destruct psi.
      * assert (notin: List.In (Var n) [phi] -> False).
        { intros [ here | there ]; [ | contradiction ].
          apply ineq; assumption. }
        revert prf' notin.
        clear prf.
        generalize [phi].
        clear ineq phi.
        generalize (eq_refl : Formula_size (Var n) = 1).
        generalize (Var n); clear n.
        intros phi phi_size Gamma prf.
        revert phi_size.
        induction prf as [ Gamma Gamma' phi perm prf IH | | | ].
        { intros phi_size notin.
          apply (IH phi_size).
          intro inprf.
          apply (notin).
          apply (Permutation_in _ perm inprf). }
        { intros phi_size inprf.
          apply False_rect.
          apply inprf.
          left; reflexivity. }
        { admit. }
        { intro devil.
          inversion devil as [ devil' ].
          apply False_rect.
          revert devil'.
          clear ...
          induction phi; intro devil'.
          - simpl in devil'.
            inversion devil'.
            apply (Formula_size_S psi); assumption.
          - simpl in devil'.
            destruct (Formula_size phi1).
            + simpl in devil'; auto.
            + simpl in devil'.
              inversion devil' as [ devil'' ].
              apply (Formula_size_S _ (proj2 (proj1 (Nat.eq_add_0 _ _) devil''))). }
      *  
      
*)
(*Lemma sc_arrow_gen:
  forall Gamma phi psi sigma,
    SC (Arrow phi psi :: Gamma) sigma ->
    (SC Gamma phi /\ SC (psi :: Gamma) sigma) \/ (SC Gamma sigma) \/ (Arrow phi psi = sigma).
Proof.
  intros Gamma.
  induction Gamma; intros phi psi sigma prf.
  - inversion prf.
    + 
  - 
  *)  
(*Lemma Hauptsatz_Step: forall phi Gamma,
    SC Gamma phi ->
    (Formula_size phi = S (S n)) ->
    
    forall Delta psi, SC (phi :: Delta) psi -> SC (Gamma ++ Delta) psi.
Proof.
  *)
Theorem Hauptsatz: forall Gamma Delta phi psi,
    SC Gamma phi -> SC (phi :: Delta) psi -> SC (Gamma ++ Delta) psi.
Proof.
  intros Gamma Delta phi.
  revert Gamma Delta.
  induction phi as [ phi IH ] using Formula_size_ind.
  destruct (Formula_size phi) as [ | n ] eqn:size_eq.
  - apply False_rect.
    apply (Formula_size_S _ size_eq).
  - destruct n as [ | n ].
    + intros; eapply Hauptsatz_Atom; eassumption.
    + intros Gamma Delta psi prf.
      revert Delta psi.
      induction prf
        as [ Gamma Gamma' phi perm prf IH'
           |
           | Gamma phi psi sigma prf1 IH1 prf2 IH2
           | Gamma phi psi prf IH' ].
      * intros Delta psi prf'.
        apply (SC_Perm _ _ _ (Permutation_app perm (Permutation_refl _))).
        apply (IH' size_eq _ _ prf').
      * intros Delta psi prf'.
        simpl.
        apply (SC_Perm _ _ _ (Permutation_sym (Permutation_middle _ _ _))).
        apply sc_weakening.
        exact prf'.
      * intros Delta psi' prf.
        simpl.
        apply SC_L.
        { apply (SC_Perm _ _ _ (Permutation_app_comm _ _)).
          apply sc_weakening.
          assumption. }
        { apply (IH2 size_eq _ _ prf). }
      * intros Delta psi' prf'.
        inversion prf'.
        { admit. }
        { apply SC_R.
          - rewrite (List.app_comm_cons).
            apply (IH psi).
            + simpl in size_eq.
              admit.
            + assumption.
            + apply SC_Ax. }
        { assert (prf'' : SC ((phi :: Gamma) ++ Delta) psi').
          { apply (IH psi).
            - admit.
            - assumption.
            - assumption. }
          destruct n as [ | n ].
          - 

          apply (SC_Perm _ _ _ (Permutation_app_comm _ _)).
          apply (IH psi).
          - admit.
          - assumption.
          - 
        
        generalize (SC_R _ _ _ prf).
        intro gamma_arrow.
        
        assert (prf'' : SC (Gamma ++ Delta) phi).
        { apply (IH psi).
        apply (IH psi).
        
        apply SC_R.


        
    intros; eapply Hauptsatz_Atom.
    + eassumption.
    + 

  psi prf1 prf2.
  revert m phi Delta prf2 n Gamma prf1.
  
  induction m as [ | m' IH ].
  - intros m phi Delta prf2.
    apply False_rect; eapply SC_zero; eassumption.
  - intros phi Delta prf2.
    inversion prf2 as
        [ ? ? ? perm prf2' | | |  ].
    + 

    
  - intros n Gamma' prf1.
    destruct (sc_weakening _ _ Delta _ prf1) as [ n' result ].
    exists (S n').
    apply (SC_Perm _ _ _ _ (Permutation_app_comm _ _)).
    assumption.
  - intros.
    
    eapply sc_weakening.

         
  revert Gamma Delta.
  induction phi as [ phi IH ] using Formula_size_ind.
  destruct phi as [ n | phi1 phi2 ].  
  - clear IH.
    intros Gamma Delta psi prf1 prf2.
    revert Gamma prf1.
    generalize (Permutation_refl (Var n :: Delta)).
    revert prf2.
    set (Delta' := Var n :: Delta).
    unfold Delta' at 2.
    generalize Delta'.
    clear Delta'.
    intros Delta' prf2.
    revert Delta.
    induction prf2 as [ Gamma Gamma' phi perm prf IH | Gamma phi | Gamma phi psi sigma prf1 IH1 prf2 IH2 | ].
    + intros Delta perm' Gamma'' prf'.
      apply IH.
      * rewrite perm; exact perm'.
      * assumption.
    + intros Delta perm Gamma' prf.
      assert (choice: Var n = phi \/ List.In phi Delta).
      { destruct (Formula_eq_dec (Var n) phi) as [ eq | ineq ].
        - left; assumption.
        - right.
          destruct (Permutation_in _ (Permutation_sym perm) (or_introl eq_refl)) as [ here | there ].
          + apply False_ind; apply ineq; assumption.
          + assumption. }
      destruct choice as [ phi_eq | inDelta ].
      * rewrite <- phi_eq.
        apply (SC_Perm _ _ _ (Permutation_app_comm _ _)).
        eapply sc_weakening; exact prf.
      * destruct (in_split _ _ inDelta) as [ l1 [ l2 Delta_eq ] ].
        apply (sc_weakening _ Gamma').
        apply (SC_Perm (phi :: l1 ++ l2)).
        { rewrite Delta_eq.
          apply Permutation_middle. }
        { apply SC_Ax. }
    + intros Delta perm Gamma' prf.
      admit.
    + admit.
  - intros Gamma Delta psi prf1 prf2.
    inversion prf1 as [ | | Gamma' phi1' phi2' sigma prf | ].
    + admit.
    + simpl.
      apply (SC_Perm _ _ _ (Permutation_sym (Permutation_middle _ _ _))).
      eapply sc_weakening; assumption.
    + simpl.
      apply ().
      
      apply SC_L.
      * apply (SC_Perm (Delta ++ Gamma') _ _ (Permutation_app_comm _ _)).
        apply (sc_weakening _ Delta).
        assumption.
      * rewrite (List.app_comm_cons).
        apply (IH phi1').
        { admit. }
        { apply (sc_weakening _ [phi2']).
          assumption. }
        { eapply (IH ).
        
    apply (IH phi2).
    
    
    
Theorem Hauptsatz1: forall Gamma phi, IL Gamma phi -> SC Gamma phi.
Proof.
  intros Gamma phi prf.
  induction prf as [ Gamma phi inprf | | Gamma phi psi prf1 IH1 prf2 IH2 ].
  - destruct (in_split _ _ inprf) as [ Gamma1 [ Gamma2 Gamma_eq ] ].
    apply (SC_Perm (phi :: Gamma1 ++ Gamma2)).
    + rewrite Gamma_eq.
      apply Permutation_middle.
    + apply SC_Ax.
  - apply SC_R; assumption.
  - inversion IH1.
    + 

Record SimpleTreeGrammar (N: Set) (T: Set) : Set :=
  { start: N;
    rules: list (N * T * list N) }.

Inductive Tree (T: Set) :=
| Node : T -> list (Tree T) -> Tree T.

Fixpoint Tree_ind' (T: Set)
         (P : Tree T -> Prop)
         (IH: forall l ts, (forall t, List.In t ts -> P t) -> P (Node _ l ts))
         (t: Tree T) {struct t}: P t :=
  match t with
  | Node _ l ts =>
    IH l ts ((fix rec ts t :=
                match ts as ts' return List.In t ts' -> P t with
                | [] => False_ind (P t)
                | (t' :: ts) =>
                  fun inprf =>
                    match inprf with
                    | or_introl here => rew here in Tree_ind' T P IH t'
                    | or_intror there => rec ts t there
                    end
                end) ts)
  end.


Section Language.
  Variable N : Set.
  Variable T: Set.
  Variable G : SimpleTreeGrammar N T.

  Fixpoint WordWithRoot (root: N) (w: Tree T) {struct w}: Prop :=
    match w with
    | Node _ l ts =>
      exists ns, List.In (root, l, ns) (rules _ _ G) /\
            (fix word_succs ns ts {struct ts} :=
               match ts with
               | [] => ns = []
               | (t :: ts) =>
                 match ns with
                 | [] => False
                 | n :: ns => WordWithRoot n t /\ word_succs ns ts
                 end
               end) ns ts
    end.

  Definition WordOf (w: Tree T): Prop :=
    WordWithRoot (start _ _ G) w.

  Section ILLanguage.
    Context (countNonTerminals : Countable N).

    Definition GrammarAssumptions : list Formula :=
      fold_right (fun rule phis =>
                    match rule with
                    | (B, _, Ns) =>
                      abstractCtxt (map (fun A => Var (toNat A)) Ns) (Var (toNat B))
                    end :: phis) [] (rules _ _ G).    
    
    Definition FormulaFor (A: N) := abstractCtxt GrammarAssumptions (Var (toNat A)).

    Lemma IL_complete: forall A w, WordWithRoot A w -> IL [] (FormulaFor A).
    Proof.
      intros A w wprf.
      unfold FormulaFor.
      apply MultiArrI.
      revert A wprf.
      induction w as [ l ts IH ] using Tree_ind'; intros A wprf.
      destruct wprf as [ ns [ inrules succs ] ].
      assert (succ_words: List.Forall2 WordWithRoot ns ts).
      { revert succs.
        clear...
        revert ns.
        induction ts as [ | t ts IH ].
        - intros ns ns_eq.
          rewrite ns_eq.
          apply List.Forall2_nil.
        - intros [ | A ns ]; [ contradiction | ].
          intros [ root succs ].
          apply List.Forall2_cons.
          + assumption.
          + apply IH; assumption. }
      clear succs.
      assert (impl: IL GrammarAssumptions (abstractCtxt (map (fun A => Var (toNat A)) ns) (Var (toNat A)))).
      { revert inrules.
        clear ...
        unfold GrammarAssumptions.
        induction (rules _ _ G).
        - intro; contradiction.
        - intros [ here | there ].
          + apply Ax; left; rewrite here; reflexivity.
          + apply weakening_step.
            auto. }
      apply (MultiArrE _ (map (fun A => Var (toNat A)) ns) _ impl).
      intros phi inprf.
      destruct ((proj1 (List.in_map_iff _ _ _)) inprf) as [ A' [ A'_eq A'_in ] ].
      rewrite <- A'_eq.
      clear impl inprf inrules.
      induction succ_words as [ | ? ? ? ? prf succ_words IH' ].
      - contradiction.
      - destruct A'_in as [ here | there ].
        + apply (IH _ (or_introl eq_refl)).
          rewrite <- here.
          assumption.
        + exact (IH' (fun t tIn => IH t (or_intror tIn)) there).
    Qed.

    Fixpoint IsTgt (phi psi: Formula): Prop :=
      match (Formula_eq_dec phi psi) with
      | left _ => True
      | right _ => match phi with
                  | Var _ => False
                  | Arrow _ phi' => IsTgt phi' psi
                  end
      end.
        
    Lemma GrammarPathLemma:
      forall phi, IL GrammarAssumptions phi ->
             (exists psi, List.In psi GrammarAssumptions /\ IsTgt psi phi) ->
             exists ns, List.In (abstractCtxt (map Var ns) phi) GrammarAssumptions ->
                   List.Forall (fun n => IL GrammarAssumptions (Var n)) ns.
    Proof.
      intros phi prf.
      induction prf as [ | Gamma phi psi prf IH | Gamma phi psi prf1 IH1 prf2 IH2 ].
      - intro; exists []; intro; apply List.Forall_nil.
      - intros [ psi' [ psi'_assumption psi'_tgt ] ].
        admit.
      - intros [ psi' [ psi'_assumption psi'_tgt ] ].
        
                     

    Lemma IL_sound: forall A, IL [] (FormulaFor A) -> exists w, WordWithRoot A w.
    Proof.
      intros A prf.
      unfold FormulaFor in prf.
      assert (prf' : IL GrammarAssumptions (Var (toNat A))).
      { apply (MultiArrE GrammarAssumptions GrammarAssumptions).
        - exact (weakening [] _ _ (fun phi phiIn => False_ind _ phiIn) prf).
        - intros; apply Ax; assumption. }
      clear prf.
      assert (assumption_prop :
                forall A, List.In A GrammarAssumptions ->
                     exists n l ns,
                       List.In (n, l, ns) (rules _ _ G) /\
                       A = abstractCtxt (map (fun x => Var (toNat x)) ns) (Var (toNat n))).
      { unfold GrammarAssumptions.
        induction (rules _ _ G) as [ | rule rules IH ].
        - intros; contradiction.
        - intros A' [ here | there ].
          + destruct rule as [ [ n l ] ns ].
            exists n, l, ns; split.
            * left; reflexivity.
            * apply eq_sym; assumption.
          + destruct (IH _ there) as [ n [ l [ ns [ inprf eqprf ] ] ] ].
            exists n, l, ns; split.
            * right; exact inprf.
            * exact eqprf. }
      revert assumption_prop.
      
      
      set (fromFormula := fun phi => match phi with | Var x => fromNat x | _ => fromNat 0 end).
      assert (from_phi : A = fromFormula (Var (toNat A))).
      { unfold fromFormula.
        rewrite fromTo_id.
        reflexivity. }
      rewrite from_phi.
      set (IsVar := fun phi => match phi with | Var _ => True | _ => False end).
      generalize (I : IsVar (Var (toNat A))).
      induction prf' as [ Gamma phi inprf | | ]; intros varprf assumption_prop.
      + destruct (assumption_prop _ inprf) as [ n [ l [ ns [ inprf' eqprf ] ] ] ].
        destruct ns as [ | B ns ].
        * simpl in eqprf.
          rewrite eqprf.
          simpl.
          rewrite fromTo_id.
          exists (Node _ l []), []; split; [ assumption | reflexivity ].
        * rewrite eqprf in varprf.
          apply False_ind.
          revert varprf.
          clear ...
          assert (ineq: B :: ns <> []).
          { intro devil; inversion devil. }
          revert ineq.
          generalize (B::ns); clear B ns; intro ns.
          generalize (Var (toNat n)).
          induction ns as [ | n' ns IH ].
          { intros phi ineq _; apply ineq; reflexivity. }
          { intros phi ineq varprf.
            destruct ns as [ | n'' ns ].
            - exact varprf.
            - simpl in varprf.
              assert (ineq': n''::ns <> []); [ intro devil; inversion devil | ].
              apply (IH _ ineq' varprf). }
      + contradiction.
      + 
  
End Language.

