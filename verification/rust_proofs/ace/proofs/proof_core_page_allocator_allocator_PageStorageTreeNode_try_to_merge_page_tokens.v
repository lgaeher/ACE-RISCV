From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From sm.ace.generated Require Import generated_code_ace generated_specs_ace generated_template_core_page_allocator_allocator_PageStorageTreeNode_try_to_merge_page_tokens.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Hint Rewrite @fst_zip @snd_zip using lia : lithium_rewrite.

Lemma core_page_allocator_allocator_PageStorageTreeNode_try_to_merge_page_tokens_proof (π : thread_id) :
  core_page_allocator_allocator_PageStorageTreeNode_try_to_merge_page_tokens_lemma π.
Proof.
  core_page_allocator_allocator_PageStorageTreeNode_try_to_merge_page_tokens_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  { liInst Hevar_x2 (λ child, child.(allocation_state) = PageTokenAvailable).
    rep liRStep. }
  rep liRStep; liShow.
  2: { rep liRStep; liShow.
    liInst Hevar_rf (mk_page_node self.(max_node_size) self.(base_address) self.(allocation_state) true).
    rep liRStep; liShow. }
  (* picking invariant for map: all nodes emitted by the iterator are available *)
  liInst Hevar_Inv (λ π iter _, ⌜Forall (λ node, node.(allocation_state) = PageTokenAvailable) iter.*1⌝%I).

  rep <-! liRStep; liShow.

  iRename select (IteratorNextFusedTrans _ _ _ _ _ _) into "Hiter".
  iPoseProof (iterator_next_fused_trans_map_inv with "Hiter") as "Hiter".
  simpl.
  set (new_children := (fmap (λ child, {| max_node_size := max_node_size child; base_address := base_address child; allocation_state := PageTokenUnavailable; children_initialized := children_initialized child |}) x')).
  iAssert (ObsList x'0 new_children)%I with "[Hiter]" as "Hobs" .
  { admit. }

  rep liRStep; liShow.
  liInst Hevar_x2 l3.
  rep liRStep; liShow.
  liInst Hevar_rf (mk_page_node self.(max_node_size) self.(base_address) PageTokenAvailable true).
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: rename x' into children.
  all: try rename l3 into tokens.
  all: try rename select (Forall2 _ _ tokens) into Hf.
  all: rewrite Hchild_init in INV_INIT_CHILDREN.
  - eexists. done.
  - move: INV_CASE.
    rename select (children_initialized self = true) into Hchild_init.
    destruct self. simpl in *.
    rewrite Hchild_init. done.
  - rewrite list_fmap_compose.
    rewrite list_fmap_compose.
    apply list_fmap_ext'; first done.
    normalize_and_simpl_goal.
    rename select (Forall2 _ _ tokens) into Hf.
    apply Forall2_length in Hf.
    clear -Hf.
    rewrite snd_zip; first done.
    lia.
  - opose proof* Forall2_length as Hlen; first apply Hf.
    rewrite length_zip Nat.min_l in Hlen; last lia.
    specialize (page_size_multiplier_ge (max_node_size self)) as Hge.
    odestruct (lookup_lt_is_Some_2 tokens 0 _) as (tok0 & Hlook_tok0).
    { lia. }
    erewrite list_lookup_total_correct; last done.
    opose proof* Forall2_lookup_r as Hlook1; [apply Hf | apply Hlook_tok0 | ].
    destruct Hlook1 as ([child_node0 ?] & Hlook_child & _ & Hsz & Hloc).
    apply lookup_zip_Some in Hlook_child as [Hlook_child _].
    destruct INV_WF as [INV_WF _].
    opose proof (INV_WF _ _ 0%nat _ _) as Hchild; [done | done | ].
    destruct Hchild as (Hchild_sz & Hchild_addr & _).
    rewrite /aligned_to.
    rewrite Hloc/=.
    rewrite Hchild_addr.
    rewrite /child_base_address/=.
    rewrite Z.mul_0_r Z.add_0_r.
    eexists. done.
  -
    rename select (tokens !! i = Some pg) into Htok_i.
    opose proof* Forall2_lookup_r as Hlook1; [apply Hf | apply Htok_i | ].
    destruct Hlook1 as ([child_node ?] & Hlook_child & _ & Hsz & Hloc).
    apply lookup_zip_Some in Hlook_child as [Hlook_child _].
    destruct INV_WF as [INV_WF _].
    opose proof (INV_WF _ _ i _ _) as Hchild; [done | done | ].
    destruct Hchild as (Hchild_sz & Hchild_addr & _).
    rewrite Hsz Hchild_sz//.
  - (* use invariant *)
    opose proof* Forall2_length as Hlen; first apply Hf.
    rewrite length_zip Nat.min_l in Hlen; last lia.
    specialize (page_size_multiplier_ge (max_node_size self)) as Hge.
    odestruct (lookup_lt_is_Some_2 tokens 0 _) as (tok0 & Hlook_tok0).
    { lia. }
    erewrite list_lookup_total_correct; last done.
    opose proof* Forall2_lookup_r as Hlook1; [apply Hf | apply Hlook_tok0 | ].
    destruct Hlook1 as ([child_node0 ?] & Hlook_child & _ & Hsz & Hloc).
    apply lookup_zip_Some in Hlook_child as [Hlook_child _].

    rename select (tokens !! i = Some _) into Htok_i.
    opose proof* Forall2_lookup_r as Hlook2; [apply Hf | apply Htok_i | ].
    destruct Hlook2 as ([child_nodei ?] & Hlook_child_i & _ & Hsz' & Hloc').
    apply lookup_zip_Some in Hlook_child_i as [Hlook_child_i _].

    destruct INV_WF as [INV_WF _].
    opose proof (INV_WF _ _ i _ _) as Hchild; [done | done | ].
    destruct Hchild as (Hchild_sz & Hchild_addr & _).

    opose proof (INV_WF _ _ 0%nat _ _) as Hchild; [done | done | ].
    destruct Hchild as (Hchild_sz_0 & Hchild_addr_0 & _).

    rewrite Hloc'/= Hchild_addr Hloc/=.
    rewrite Hchild_addr_0.
    rewrite Hsz' Hchild_sz.
    rewrite /child_base_address.
    simpl. clear. nia.
  - opose proof* Forall2_length as Hlen; first apply Hf.
    rewrite -Hlen length_zip. lia.
  - apply page_storage_node_children_wf_upd_state; last done.
    simpl. solve_goal.
  - eexists. done.
  - rewrite /new_children length_fmap//.
  - rewrite /page_storage_node_invariant_case/=.
    eexists. split_and!; try done. simpl.
    opose proof* Forall2_length as Hlen; first apply Hf.
    rewrite length_zip Nat.min_l in Hlen; last lia.
    specialize (page_size_multiplier_ge (max_node_size self)) as Hge.
    odestruct (lookup_lt_is_Some_2 tokens 0 _) as (tok0 & Hlook_tok0).
    { lia. }
    erewrite list_lookup_total_correct; last done.
    opose proof* Forall2_lookup_r as Hlook1; [apply Hf | apply Hlook_tok0 | ].
    destruct Hlook1 as ([child_node0 ?] & Hlook_child & _ & Hsz & Hloc).
    apply lookup_zip_Some in Hlook_child as [Hlook_child _].
    destruct INV_WF as [INV_WF _].
    opose proof (INV_WF _ _ 0%nat _ _) as Hchild; [done | done | ].
    destruct Hchild as (Hchild_sz & Hchild_addr & _).
    rewrite Hloc/=.
    rewrite Hchild_addr.
    rewrite /child_base_address/=.
    rewrite Z.mul_0_r Z.add_0_r//.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
