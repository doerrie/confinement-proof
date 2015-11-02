Require Import FMapInterface2.
Require Import FMapFacts2.
Require Import OptionMap2.
Require Import OptionSumbool.
Require Import FMapExists.

Module MakeEquiv_fun (E:OrderedType) (MapS: Sfun E) (Data:OrderedType) (ST: Sord_fun E MapS Data).

  Module STOrdProps := OrdProperties_fun E MapS.
  Module STProps := STOrdProps.P.
  Module STFacts := STProps.F.
  Module STExists := MakeExists_fun E MapS Data ST.

  Module DataFacts := OrderedTypeFacts Data.



  Theorem compat_cmp_eq :
    STFacts.compat_cmp Data.eq ST.cmp.
  Proof.
    unfold STFacts.compat_cmp; unfold ST.cmp.
    intros; split; intros;
      [destruct Data.compare; first [apply diff_false_true in H; tauto | auto] |
    destruct Data.compare; 
      [ apply Data.lt_not_eq in H; tauto |
        auto |
        apply Data.eq_sym in H;
          apply Data.lt_not_eq in l; tauto]].
  Qed.

  (* this is probably simpler now that we have option_map_eq_Equiv. *)


  Theorem find_eq: forall k k' s s',
    E.eq k k' -> 
    ST.eq s s' ->
    option_map_eq Data.eq (MapS.find k s) (MapS.find k' s').
  Proof.
    intros.
    unfold option_map_eq.
    unfold option_map2.
    apply ST.eq_2 in H0.
    generalize (STFacts.Equiv_Equivb compat_cmp_eq s s'); intros H1.
    destruct H1 as [_ H2].
    apply H2 in H0.
    clear H2.
    unfold MapS.Equiv in H0.
    destruct H0.
    generalize (H0 k); intros H2.
    case (option_sumbool (MapS.find k s)); intros Hopt.
    rewrite Hopt.
    apply STFacts.not_find_in_iff in Hopt.
    assert (~ MapS.In k s'); [firstorder|].
    generalize (STFacts.In_iff s' H); intros H4.
    assert (~ MapS.In k' s'); [firstorder|].
    apply STFacts.not_find_in_iff in H5.
    rewrite H5; trivial.
    (*other case*)
    destruct Hopt as [v Hopt].
    rewrite Hopt.
    apply STFacts.find_mapsto_iff in Hopt.
    assert (exists x, MapS.MapsTo k x s); [apply ex_intro with v; auto |].
    apply H2 in H3.
    destruct H3.
    generalize (STFacts.MapsTo_iff s' x H); intros H4.
    apply H4 in H3.
    apply STFacts.find_mapsto_iff in H3.
    rewrite H3.
    apply H1 with (k:=k) (e:=v) (e':=x); firstorder.
  Qed.

  Theorem mapsTo_eq:forall k k' v v' s s',
    E.eq k k' ->
    ST.eq s s' ->
    MapS.MapsTo k v s ->
    MapS.MapsTo k' v' s' ->
    Data.eq v v'.
  Proof.
    intros.
    generalize (find_eq _ _ _ _ H H0); intros Hgoal.
    rewrite (MapS.find_1 H1) in Hgoal.
    rewrite (MapS.find_1 H2) in Hgoal.
    simpl in Hgoal.
    assumption.
  Qed.

  Theorem exists_mapsTo_eq: 
    forall s s', ST.eq s s' ->
      forall k v, MapS.MapsTo k v s ->
        forall k', E.eq k k' -> 
          exists v', Data.eq v v' /\ MapS.MapsTo k' v' s'.
  Proof.
    intros.
    generalize (find_eq _ _ _ _ H1 H);
    unfold option_map_eq; unfold option_map2; intros H2.
    rewrite (MapS.find_1 H0) in H2.
    case (option_sumbool (MapS.find k' s')); intros Hopt;
      [|destruct Hopt as [v' Hopt]]; rewrite Hopt in H2;
        [contradiction
          | apply ex_intro with v'; apply MapS.find_2 in Hopt; split; auto].
  Qed.

Theorem Equal_eq: forall s s',
   MapS.Equal s s' -> ST.eq s s'.
Proof.
  intros.
  apply ST.eq_1.
  unfold MapS.Equivb.
  unfold Cmp.
  unfold ST.cmp.
  unfold MapS.Equiv.
  split; intros.
  (* In case *)
  unfold MapS.In.
  split; intros [e H2];
  eapply STFacts.find_mapsto_iff in H2;
  [rewrite H in H2 | rewrite <- H in H2];
  eapply STFacts.find_mapsto_iff in H2;
  eapply ex_intro; eauto.
  (* compare case *)
  eapply STFacts.find_mapsto_iff in H1.  
  eapply STFacts.find_mapsto_iff in H0.  
  rewrite <- H in H1.
  rewrite H0 in H1.
  injection H1; intros.
  rewrite H2 in *; auto.
  case (Data.compare e' e'); auto; intros Hlt;  apply Data.lt_not_eq in Hlt; intuition.
Qed.

Theorem In_eq: 
    forall s s', ST.eq s s' ->
      forall k, MapS.In k s ->
        forall k', E.eq k k' -> 
          MapS.In k' s'.
Proof.
  intros s s' Hs k [e He] k' Hk.
  generalize (exists_mapsTo_eq _ _ Hs _ _ He _ Hk); intros [e' [HeqE He']].
  eapply ex_intro; apply He'.
Qed.

(* The following were added very late, so many theorems about equivalence probably want to be updated
   to use these *)
Theorem In_m : Proper (E.eq ==> ST.eq ==> iff) (@MapS.In Data.t).
Proof.
  unfold Proper; unfold respectful; intros;
  split; intros; eapply In_eq; eauto; try (apply ST.eq_sym; auto).
Qed.

Theorem remove_m: Proper (E.eq ==> ST.eq ==> ST.eq) (@MapS.remove Data.t).
Proof.
  unfold Proper; unfold respectful; intros.
  apply ST.eq_1.
  apply ST.eq_2 in H0.
  unfold MapS.Equivb in *.
  unfold Cmp in *.
  unfold ST.cmp in *.
  unfold MapS.Equiv in *.
  destruct H0 as [Hin Hmap].
  split; intros.

  (* reduce to in over remove *)
  eapply iff_trans.
  eapply STFacts.remove_in_iff.
  eapply iff_sym; eapply iff_trans;[ eapply STFacts.remove_in_iff|].
  (* cases on equality, reduce through rewrite *)
  case (E.eq_dec x k); intros Heq;
    intuition; rewrite H in Heq;
      try solve [contradiction | auto | apply Hin; auto].

  (* MapsTo k e (remove x m) can be rewriten to MapsTo k e m using remove_mapsto_iff *)
  eapply STFacts.remove_mapsto_iff in H0; destruct H0 as [_ H0];
    eapply STFacts.remove_mapsto_iff in H1; destruct H1 as [_ H1];
      eapply Hmap; eauto.
Qed.


Theorem add_m: Proper (E.eq ==> Data.eq ==> ST.eq ==> ST.eq) (@MapS.add Data.t).
Proof.
  unfold Proper; unfold respectful; intros.
  apply ST.eq_1.
  apply ST.eq_2 in H1.
  unfold MapS.Equivb in *.
  unfold Cmp in *.
  unfold ST.cmp in *.
  unfold MapS.Equiv in *.
  destruct H1 as [Hin Hmap].
  split; intros.
  
  eapply iff_trans.
  eapply STFacts.add_in_iff.
  eapply iff_sym; eapply iff_trans; [ eapply STFacts.add_in_iff|].
  case (E.eq_dec x k); intros Heq;
    intuition; rewrite H in Heq;
      intuition (try solve [contradiction | auto | apply Hin; auto]).

    eapply STFacts.add_mapsto_iff in H1; 
      eapply STFacts.add_mapsto_iff in H2.
    destruct H1 as [[HeqX HeqE] | [HneqX HmapE]];
      destruct H2 as [[HeqY HeqE'] | [HneqY HmapE']];
        solve [
          (* first case *)
          rewrite <- HeqE; rewrite <- HeqE';
            DataFacts.elim_comp; auto
          | (* contradictory cases *) 
            DataFacts.elim_comp; eauto
          | (* last case *)
            eapply Hmap; eauto].

Qed.

Theorem find_m : Proper (E.eq ==> ST.eq ==> (option_map_eq Data.eq)) (@MapS.find Data.t).
Proof.
  unfold Proper; unfold respectful; intros.
  apply ST.eq_2 in H0.
  unfold MapS.Equivb in *.
  unfold Cmp in *.
  unfold ST.cmp in *.
  unfold MapS.Equiv in *.
  destruct H0 as [Hin Hmap].

  case (option_sumbool (MapS.find x x0)); intros Hcase;
    [|destruct Hcase as [x1 Hcase]]; rewrite Hcase in *;
      (case (option_sumbool (MapS.find y y0)); intros Hcase';
        [|destruct Hcase' as [y1 Hcase']]; rewrite Hcase' in *);
      simpl in *; try solve [eauto].

  Ltac solve_find_contradiction Hin Hin1 Hin2 Hin' Hcase Hcase' H:=
  unfold MapS.In in *;
  edestruct Hin as [Hin1 Hin2];
  apply STFacts.not_find_in_iff in Hcase;
  apply STFacts.find_mapsto_iff in Hcase';
  eapply ex_intro with (P:=(fun e => MapS.MapsTo _ e _)) in Hcase';
  apply Hin' in Hcase';
  destruct Hcase' as [e Hcase'];
  eapply STFacts.MapsTo_m in Hcase'; 
    [| apply H | apply eq_refl | apply STFacts.Equal_refl];
  eapply ex_intro with (P:=(fun e => MapS.MapsTo _ e _)) in Hcase';
  contradiction.

  solve_find_contradiction Hin Hin1 Hin2 Hin2 Hcase Hcase' H.
  solve_find_contradiction Hin Hin1 Hin2 Hin1 Hcase' Hcase (E.eq_sym H).
 
  apply STFacts.find_mapsto_iff in Hcase.
  eapply STFacts.MapsTo_iff in Hcase;[| apply E.eq_sym; apply H].
  apply STFacts.find_mapsto_iff in Hcase'.
  generalize (Hmap _ _ _ Hcase Hcase'); clear Hmap.
  DataFacts.elim_comp; intros Hmap; discriminate Hmap.
Qed.


    Theorem Proper_Exists:
      Proper ((E.eq ==> Data.eq ==> impl) ==> ST.eq ==> impl) (fun P m => STExists.Exists P m).
    Proof.
      intros.
      unfold Proper; unfold respectful; unfold impl; unfold STExists.Exists.
      intros P P' Hproper x y Heq [i [cap [Hmap Pcap]]].
      apply ex_intro with i.
      generalize (exists_mapsTo_eq _ _ Heq _ _ Hmap _ (E.eq_refl i)); 
        intros [cap' [Hcap'eq Hcap'Map]].
      eapply ex_intro.
      split; [apply Hcap'Map|].
      eapply Hproper; eauto.
    Qed.

End MakeEquiv_fun.

Module MakeEquiv (ST:Sord).

  Include MakeEquiv_fun ST.MapS.E ST.MapS ST.Data ST.

End MakeEquiv.
