Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

Section TreeGrammar.
  Variable Terminal: Type.
  Variable NonTerminal: Type.
  
  Inductive Production: Type :=
  | Derives : forall (lhs: NonTerminal) (headSymbol: Terminal) (arguments: list NonTerminal), Production.

  Definition lhs (p: Production): NonTerminal :=
    match p with Derives lhs _ _ => lhs end.

  Definition headSymbol (p: Production): Terminal :=
    match p with Derives _ headSymbol _ => headSymbol end.

  Definition arguments (p: Production): list NonTerminal :=
    match p with Derives _ _ arguments => arguments end.
  
  Structure TreeGrammar: Type :=
    { startSymbol: NonTerminal;
      productions: list Production }.

  Definition find_production_with_lhs {P : NonTerminal -> Prop} (P_dec: forall nt, { P nt } + { ~ P nt}) (G: TreeGrammar):
    option Production :=
    find (fun p => if P_dec (lhs p) then true else false)
         (productions G).

  Lemma find_production_with_lhs_spec {P : NonTerminal -> Prop}:
    forall (P_dec: forall nt, { P nt } + { ~ P nt}) (G: TreeGrammar),
      (exists p, find_production_with_lhs P_dec G = Some p) <->  (exists p, In p (productions G) /\ P (lhs p)).
  Proof.
    intros P_dec G.
    unfold find_production_with_lhs.
    induction (productions G) as [ | p' ps' IH ]; split.
    - intros [ ? devil ]; inversion devil.
    - intros [ ? [ devil _ ] ]; inversion devil.
    - simpl.
      destruct (P_dec (lhs p')) as [ P_p | nP_p ].
      + intros [ p p_eq ].
        revert P_p.
        inversion p_eq.
        intro P_p.
        exists p; auto.
      + intros [ p findprf ].
        destruct (proj1 IH (ex_intro _ p findprf)) as [ p''  [ ? ? ] ].
        exists p''; auto.
    - simpl.
      destruct (P_dec (lhs p')) as [ P_p | nP_p ].
      + intro; exists p'; reflexivity.
      + intros [ p'' [ in_p'' p''_prf ] ].
        destruct in_p'' as [ here | there ].
        * rewrite <- here in p''_prf; contradiction.
        * exact (proj2 IH (ex_intro _ p'' (conj there p''_prf))).
  Qed.

  Inductive TreeRootedIn (G: TreeGrammar): NonTerminal -> Type :=
  | Node: forall root headSymbol (arguments: list NonTerminal),
      Forest G arguments ->
      In (Derives root headSymbol arguments) (productions G) ->
      TreeRootedIn G root
  with Forest (G: TreeGrammar): list NonTerminal -> Type :=
       | Forest_nil: Forest G []
       | Forest_cons: forall root roots, TreeRootedIn G root -> Forest G roots -> Forest G (root::roots).

  Definition ForallForest (G: TreeGrammar) (P: forall nt, TreeRootedIn G nt -> Type)
             (roots: list NonTerminal) (forest: Forest G roots): Type :=
    (fix ForallForest_rec roots (forest: Forest G roots): Type :=
       match forest with
       | Forest_nil _ => unit
       | Forest_cons _ root roots' tree forest' =>
         (P root tree * ForallForest_rec roots' forest')%type
       end) roots forest.
  
  Definition TreeRootedIn_rect'
    (G : TreeGrammar) (P : forall n : NonTerminal, TreeRootedIn G n -> Type)
    (Node_case:
       forall (root : NonTerminal) (headSymbol : Terminal) (arguments : list NonTerminal) 
         (children : Forest G arguments) (inprf : In (Derives root headSymbol arguments) (productions G))
         (IH: ForallForest G P arguments children),
         P root (Node G root headSymbol arguments children inprf))
    (root: NonTerminal) (tree : TreeRootedIn G root): P root tree :=
    (fix TreeRootedIn_rect_rec (root: NonTerminal) (tree: TreeRootedIn G root): P root tree :=
       match tree with
       | Node _ root headSymbol arguments children inprf =>
         Node_case root headSymbol arguments children inprf
                   ((fix children_rec arguments (children: Forest G arguments):
                       ForallForest G P arguments children :=
                       match children with
                       | Forest_nil _ => tt
                       | Forest_cons _ arg args child children' =>
                         (TreeRootedIn_rect_rec arg child, children_rec args children')
                       end) arguments children)
       end) root tree.

  Section Algorithms.
    Variable NonTerminal_eq_dec: forall (nt nt': NonTerminal), { nt = nt' } + { nt <> nt' }.

    Definition is_ground_production
               (assumptions: list NonTerminal)
               (production: Production): bool :=
      forallb (fun arg =>
                 existsb (fun assumption =>
                            if NonTerminal_eq_dec arg assumption
                            then true else false)
                         assumptions)
              (arguments production).
    
    Definition split_ground_productions_assuming
               (assumptions: list NonTerminal)
               (productions: list Production): (list Production * list Production)%type :=
      partition (is_ground_production assumptions) productions.
    
    Fixpoint ground_if_rec (steps: nat)
             (assumptions: list NonTerminal)
             (productions: list Production): list NonTerminal :=
      match steps with
      | 0 => assumptions
      | S remaining_steps =>
        match productions with
        | [] => assumptions
        | productions =>
          let (newAssumptions, remainingProductions) :=
              split_ground_productions_assuming assumptions productions
          in (ground_if_rec remaining_steps
                            (map lhs newAssumptions ++ assumptions)
                            remainingProductions)
        end
      end.
    
    Definition ground_if (G: TreeGrammar) (assumptions: list NonTerminal): list NonTerminal :=
      ground_if_rec (length (productions G)) assumptions (productions G).

    Definition ground (G: TreeGrammar): list NonTerminal := ground_if G [].

    Lemma ground_if_rec_mono:
      forall steps assumptions productions nt,
        In nt assumptions -> In nt (ground_if_rec steps assumptions productions).
    Proof.
      intros steps.
      induction steps as [ | remaining_steps IH ].
      - intros; assumption.
      - intros assumptions productions nt inprf.
        simpl.
        destruct productions.
        + assumption.
        + match goal with
          |[|- In nt (let (_, _) := split_ground_productions_assuming ?ass ?ps in _) ]=>
           destruct (split_ground_productions_assuming ass ps) as [ newAssumptions remainingAssumptions ]
          end.
          apply IH.
          apply List.in_or_app.
          right; assumption.
    Qed.

    Lemma partition_in_true {A: Type}:
      forall (x: A) xs f, In x (fst (partition f xs)) -> f x = true.
    Proof.
      intros x xs f.
      induction xs as [ | x' xs' IH]; intro inprf.
      - contradiction.
      - simpl in inprf.
        destruct (partition f xs') as [ fxs' notFxs' ].
        remember (f x') as fx' eqn:fx'_eq.
        destruct fx'.
        + destruct inprf as [ here | there ].
          * rewrite <- here; apply eq_sym; assumption.
          * apply IH; assumption.
        + apply IH; assumption.
    Qed.
    
    Lemma split_ground_productions_assuming_ground:
      forall assumptions productions nt,
        In nt (map lhs (fst (split_ground_productions_assuming assumptions productions))) ->
        (exists p, In p productions /\
              lhs p = nt /\
              (forall nt', In nt' (arguments p) ->
                      In nt' assumptions)).
    Proof.
      intros assumptions productions nt inprf.
      destruct (proj1 (List.in_map_iff _ _ _) inprf)
        as [ p [ lhs_eq p_in ] ].
      exists p; repeat split.
      - unfold split_ground_productions_assuming in p_in.
        destruct (partition (is_ground_production assumptions) productions) eqn:partition_eq.
        eapply (List.elements_in_partition).
        + eassumption.
        + left; assumption.
      - assumption.
      - intros nt' inargs.
        generalize (proj1 (List.forallb_forall _ _) (partition_in_true _ _ _ p_in) _ inargs).
        intro exarg.
        destruct (proj1 (List.existsb_exists _ _) exarg) as [ arg [ inarg eqarg ] ].
        revert inarg.
        destruct (NonTerminal_eq_dec nt' arg) as [ arg_eq | ].
        + rewrite arg_eq; trivial.
        + inversion eqarg.
    Qed.

    Lemma ground_if_rec_ground:
      forall steps assumptions productions nt,
        In nt (ground_if_rec (S steps) assumptions productions) ->
        In nt assumptions \/
        (exists p, In p productions /\
              lhs p = nt /\
              (forall nt', In nt' (arguments p) -> In nt' (ground_if_rec steps assumptions productions))).
    Proof.
      intro steps.
      induction steps as [ | remaining_steps IH ];
        intros assumptions productions nt.
      - simpl.
        destruct (productions) as [ | p ps ].
        + intro; left; assumption.
        + generalize (split_ground_productions_assuming_ground assumptions (p::ps) nt).
          destruct (split_ground_productions_assuming assumptions (p :: ps)) as [ l r ].
          * intros prf inprf.
            destruct (List.in_app_or _ _ _ inprf) as [ inprf' | ];
              [ right; auto | left; assumption ].
      - simpl.
        destruct productions as [ | p ps ].
        + intro; left; assumption.
        + generalize (split_ground_productions_assuming_ground assumptions (p::ps) nt).
          generalize (List.elements_in_partition (is_ground_production assumptions) (p::ps)).
          fold (split_ground_productions_assuming assumptions (p::ps)).
          destruct (split_ground_productions_assuming assumptions (p::ps))
            as [ newAssumptions remainingProductions ].
          intros inproductions_prf ground_prf inprf.
          destruct (IH _ _ nt inprf) as [ inprf' | exprf ].
          * destruct (List.in_app_or _ _ _ inprf') as [ innewprf | inassumptions ].
            { right.
              destruct (ground_prf innewprf) as [ p' [ p'_in [ p'_lhs args_prf ] ] ].
              exists p'; repeat split; try solve [ assumption ].
              intros nt' inargs.
              apply ground_if_rec_mono.
              apply (List.in_or_app).
              right; auto. }
            { left; assumption. }
          * destruct exprf as [ p' [ p'_in [ p'_lhs args_prf ] ] ].
            right.
            exists p'; repeat split; try solve [ assumption ].
            apply (proj2 (inproductions_prf _ _ eq_refl p')).
            right; assumption.
    Qed.

    Lemma ground_if_rec_fix:
      forall steps assumptions productions,
        (fst (split_ground_productions_assuming assumptions productions) = []) ->
        ground_if_rec steps assumptions productions = assumptions.
    Proof.
      intro steps.
      induction steps as [ | remaining_steps IH ];
        intros assumptions productions eqprf.
      - reflexivity.
      - assert (productions_eq:
                  fst (split_ground_productions_assuming assumptions productions) = [] /\
                  snd (split_ground_productions_assuming assumptions productions) = productions).
        { unfold split_ground_productions_assuming in *.
          revert eqprf.
          generalize (is_ground_production assumptions).
          clear ...
          intro f.          
          induction productions as [ | p ps IH ].
          + intro; split; [ assumption | reflexivity ].
          + revert IH.
            simpl.
            destruct (partition f ps) as [ l r ].
            destruct (f p) eqn:fp_eq.
            * intros _ devil; inversion devil.
            * simpl.
              intros.
              split; [ assumption | ].
              apply f_equal.
              exact (proj2 (IH eqprf)). }
        generalize (IH assumptions productions).
        revert productions_eq.        
        clear IH.
        destruct productions as [ | p ps ].
        + intros; reflexivity.
        + simpl.
          match goal with
          |[|- fst ?xs = _ /\ _ -> _] =>
           destruct xs as [ empty productions' ]
          end.
          intros [ newAssumptions_empty remainingProductions_eq ] IH.
          simpl in newAssumptions_empty.
          rewrite newAssumptions_empty.
          simpl.
          simpl in remainingProductions_eq.
          rewrite remainingProductions_eq.
          apply IH.
          assumption.
    Qed.

    Lemma ground_split_ground_productions_assuming:
      forall assumptions productions p,
        In p productions ->
        (forall nt', In nt' (arguments p) ->
                In nt' assumptions) ->
        In p (fst (split_ground_productions_assuming assumptions productions)).
    Proof.
      intros assumptions productions p p_in inargs.
      induction productions as [ | p' ps' IH ].
      - assumption.
      - destruct p_in as [ here | there ].
        + simpl.
          rewrite here.
          destruct (split_ground_productions_assuming assumptions ps') as [ l r ].
          assert (is_ground: is_ground_production assumptions p = true).
          { unfold is_ground_production.
            apply (List.forallb_forall).
            intros nt' nt'_in.
            apply (List.existsb_exists).
            exists nt'; split; [ auto | ].
            destruct (NonTerminal_eq_dec nt' nt') as [ | devil ].
            - reflexivity.
            - apply (False_rect _ (devil eq_refl)). }
          rewrite is_ground.
          left; reflexivity.
        + simpl.
          generalize (IH there).
          destruct (split_ground_productions_assuming assumptions ps').
          destruct (is_ground_production assumptions p').
          * intro; right; assumption.
          * intro; assumption.
    Qed.

    Lemma ground_if_rec_unfold:
      forall steps assumptions productions nt,
        In nt (ground_if_rec (S steps) assumptions productions) ->
        In nt (ground_if_rec steps
                             (map lhs (fst (split_ground_productions_assuming assumptions productions))
                                  ++ assumptions)
                             (snd (split_ground_productions_assuming assumptions productions))).
    Proof.
      intros steps assumptions productions.
      destruct productions as [ | p ps ];
        intros nt inprf.
      - simpl; destruct steps; assumption.
      - revert inprf.
        simpl.
        destruct (split_ground_productions_assuming assumptions ps).
        destruct (is_ground_production assumptions p);
          intro; assumption.
    Qed.            
    
    Lemma ground_ground_if_rec:
      forall steps assumptions productions nt,
        length productions <= steps ->
        (In nt assumptions \/
         (exists p, In p productions /\
               lhs p = nt /\
               (forall nt', In nt' (arguments p) -> In nt' (ground_if_rec steps assumptions productions)))) ->
        In nt (ground_if_rec steps assumptions productions).
    Proof.
      intro steps.
      induction steps as [ | remaining_steps IH ];
        intros assumptions productions nt steps_gt ground_prf.
      - destruct ground_prf as [ | [ p' [ devil _ ]] ].
        + apply ground_if_rec_mono.
          assumption.
        + destruct productions.
          * inversion devil.
          * simpl in steps_gt.
            inversion steps_gt.
      - destruct ground_prf as [ | [ p' [ p'_in [ p'_lhs args_prf ]]] ].
        + apply ground_if_rec_mono.
          assumption.
        + assert (lengthprf:
                    fst (split_ground_productions_assuming assumptions productions) = [] \/
                    length (snd (split_ground_productions_assuming assumptions productions)) <= remaining_steps).
          { generalize (@List.partition_length _
                                               (is_ground_production assumptions) productions
                                               (fst (split_ground_productions_assuming assumptions productions))
                                               (snd (split_ground_productions_assuming assumptions productions))).
            unfold split_ground_productions_assuming.
            destruct (partition (is_ground_production assumptions)) as [ l r ].
            intro prf.
            rewrite (prf eq_refl) in steps_gt.
            simpl in *.
            destruct l.
            - left; reflexivity.
            - right.
              simpl in steps_gt.
              rewrite <- (Nat.succ_le_mono _ _) in steps_gt.
              rewrite (Nat.add_comm _ _) in steps_gt.
              etransitivity; [ eapply (Nat.le_add_r _ _) | exact steps_gt ]. }
          destruct lengthprf as [ isfix | lengthprf ].
          * rewrite (ground_if_rec_fix (S remaining_steps)  _ _ isfix) in args_prf.
            generalize (ground_split_ground_productions_assuming assumptions productions p'
                                                                 p'_in args_prf).
            rewrite isfix.
            intro devil; inversion devil.
          * generalize (fun nt' inprf => ground_if_rec_unfold remaining_steps assumptions productions nt'
                                                           (args_prf nt' inprf)).
            intro args_prf'.
            assert (now_or_then:
                In nt (map lhs (fst (split_ground_productions_assuming assumptions productions))
                           ++ assumptions) \/
                In p' (snd (split_ground_productions_assuming assumptions productions))).
            { generalize (@List.elements_in_partition _
                            (is_ground_production assumptions)
                            productions
                            (fst (split_ground_productions_assuming assumptions productions))
                            (snd (split_ground_productions_assuming assumptions productions))).
              unfold split_ground_productions_assuming.
              destruct (partition (is_ground_production assumptions) productions) as [ l r ].
              intro result.
              destruct (proj1 (result eq_refl p') p'_in) as [ in_left | in_right ].
              - left.
                apply (List.in_or_app).
                left.
                apply (List.in_map_iff).
                exists p'; split; assumption.
              - right; assumption. }
            generalize (IH _ _ nt lengthprf
                           (match now_or_then with
                            | or_introl x => or_introl x
                            | or_intror p'_in_rest =>
                              or_intror (ex_intro _ p' (conj p'_in_rest (conj p'_lhs args_prf')))
                            end)).
            destruct productions  as [ | p ps ];
              [ inversion p'_in | ].
            simpl.
            match goal with
            | [|- _ -> In nt (let (_, _) := ?x in _)] =>
              destruct x as [ newAssumptions  remainingAssumptions ]
            end.
            intro; assumption.
    Qed.    

    Lemma ground_Tree: forall G nt, List.In nt (ground G) -> inhabited (TreeRootedIn G nt).
    Proof.
      intros G.
      unfold ground.
      unfold ground_if.
      generalize (length (productions G)).
      intro steps.
      assert (in_assumptions: forall nt, In nt [] -> inhabited (TreeRootedIn G nt)).
      { intros; contradiction. }
      revert in_assumptions.
      generalize (@nil NonTerminal).
      induction steps as [ | remainingSteps IH ].
      + intros; auto.
      + intros assumptions assumptions_closed nt inprf.
        destruct (ground_if_rec_ground _ _ _ _ inprf)
          as [ | [ [lhs hd args] [ p_in [ p_lhs p_args]]] ].
        * auto.
        * simpl in p_lhs.
          rewrite <- p_lhs.
          assert (children: inhabited (Forest G args)).
          { clear p_in.
            induction args as [ | arg args IH' ].
            - constructor; apply Forest_nil.
            - destruct (IH assumptions assumptions_closed arg (p_args arg (or_introl _ eq_refl))) as [ arg_tree ].
              destruct (IH' (fun nt inprf => p_args nt (or_intror _ inprf))) as [ args_forest ].
              constructor.
              apply (Forest_cons G _ _ arg_tree args_forest). }
          destruct children as [ children ].
          constructor.
          exact (Node G lhs hd args children p_in).
    Qed.

    Lemma Tree_ground: forall G nt, TreeRootedIn G nt -> List.In nt (ground G).
    Proof.
      intros G nt tree.
      generalize (fun nt => ground_ground_if_rec (length (productions G))
                                              [] (productions G) nt (Nat.le_refl _)).
      intro prf.
      unfold ground.
      unfold ground_if.
      induction tree as [ root hd args children inprf IH ] using TreeRootedIn_rect'.
      apply (prf root); right.
      exists (Derives root hd args); repeat split.
      - assumption.
      - intros arg arg_in.
        revert IH arg_in.
        clear ...
        induction children as [ | arg' args child children IH' ];
          intros IH arg_in.
        + contradiction.
        + destruct IH as [ result rest ].
          destruct arg_in as [ here | there ].
          * rewrite <- here; assumption.
          * apply (IH' rest there).
    Qed.

    Definition TreeGrammar_empty_dec (G: TreeGrammar) (nt: NonTerminal):
      { inhabited (TreeRootedIn G nt) } + { ~inhabited (TreeRootedIn G nt) }.
    Proof.
      destruct (find (fun nt' => if NonTerminal_eq_dec nt nt' then true else false) (ground G))
        as [ | nt' ] eqn:find_eq.
      - left.
        destruct (List.find_some _ _ find_eq) as [ inprf eqprf ].        
        apply ground_Tree.
        destruct (NonTerminal_eq_dec nt n) as [ eq | ineq ].
        + rewrite eq; assumption.
        + inversion eqprf.
      - right.
        intros [ devil ].
        generalize (find_none _ _ find_eq nt (Tree_ground _ _ devil)).
        intro devil'.
        destruct (NonTerminal_eq_dec nt nt) as [ | devil'' ].
        + inversion devil'.
        + apply devil''; reflexivity.
    Qed.

    

  End Algorithms.
End TreeGrammar.